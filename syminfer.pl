/*
 * Code for symbolic inference using OSDDs.
 * Usage: ?- [bounds, syminfer, 'path/to/transformed_file'] % Load files and libraries
 * To construct an OSDD for ground query q(v1,...,vn) use ?- q(v1,....,vn,leaf(1),O).
 */
:- import get_attr/3, put_attr/3, install_verify_attribute_handler/4, install_attribute_portray_hook/3 from machine.

:- install_verify_attribute_handler(type, AttrValue, Target, type_handler(AttrValue, Target)).
:- install_verify_attribute_handler(id, AttrValue, Target, id_handler(AttrValue, Target)).
:- install_verify_attribute_handler(constraint, AttrValue, Target, constraint_handler(AttrValue, Target)).
:- install_verify_attribute_handler(bounds_var, AttrValue, Target, bounds_var_handler(AttrValue, Target)).

:- install_attribute_portray_hook(type, Attr, display_type(Attr)).
:- install_attribute_portray_hook(id, Attr, display_id(Attr)).
:- install_attribute_portray_hook(constraint, Attr, display_constr(Attr)).
:- install_attribute_portray_hook(bounds_var, Attr, display_bounds_var(Attr)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OSDD construction definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Definition of msw constraint processing.
% If X is in C_in 
%     set C_in = C_out
% Otherwise 
%     First set the type of X to be the domain of S,
%     Set bounds_var of X which will have the bounds constraints applied to
%         set the range of X:bounds_var to be the range of the domain of S,
%     Then set the ID of X to be the pair (S, I),
%     Construct the OSDD rooted at X with a single edge labeled with constraints C and a leaf node 1,
%     AND this OSDD rooted at X with C_in to compute C_out
msw(S, I, X, C_in, C_out) :- !,
    writeln('\nIN MSW...'),
    (contains(C_in, X)
    ->  C_out = C_in
    ;   values(S, T),
        set_type(X, T),
        read_bounds_var(X, B),
        intrange(S, Low, High),
        B in Low..High,
        set_id(X, (S, I)),
        read_constraint(X, C),
        make_tree(X, [C], [leaf(1)], Osdd),   % osdd: X -- C --> 1
        and(C_in, Osdd, C_out),
        write('C_in: '), writeln(C_in), write('C_out: '), writeln(C_out)
    ).

% Definition of atomic constraint processing for equality constraints.
% First check if at least one of the arguments of the constraint is a variable
% Then get the types of both arguments
%     If Lhs or Rhs has empty type and is a variable, fail
%     (ie. constraints on X must occur after msw(S, I, X))
% Update the constraint lists of any variable arguments
% Finally update the edges for Lhs and Rhs.
constraint(Lhs=Rhs, C_in, C_out) :-
    write('\n= CONSTRAINT: '),writeln(Lhs=Rhs),
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    (var(Lhs) 
    ->  read_type(Lhs, T1)
    ;   lookup_type(Lhs, T1)
    ),
    (var(Rhs) 
    ->  read_type(Rhs, T2)
    ;   lookup_type(Rhs, T2)
    ),
    nonvar(T1), nonvar(T2),
    T1 = T2,
    (var(Lhs)
    ->  set_constraint(Lhs, [Lhs=Rhs])
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, [Lhs=Rhs])
    ;   true
    ),
    write('UPDATING EDGES...'), writeln(Lhs),
    update_edges(C_in, Lhs, Lhs=Rhs, C_tmp), !,
    write('UPDATING EDGES...'), writeln(Rhs),
    update_edges(C_tmp, Rhs, Lhs=Rhs, C_out), !, 
    write('C_in: '), writeln(C_in), write('C_out: '), writeln(C_out).

% Definition of atomic constraint processing for inequality constraints.
% Same logic as in equality constraints.
constraint(Lhs\=Rhs, C_in, C_out) :-
    write('\n\= CONSTRAINT: '),writeln(Lhs\=Rhs),
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    (var(Lhs) 
    ->  read_type(Lhs, T1)
    ;   lookup_type(Lhs, T1)
    ),
    (var(Rhs) 
    ->  read_type(Rhs, T2)
    ;   lookup_type(Rhs, T2)
    ),
    nonvar(T1), nonvar(T2),
    T1 = T2,
    (var(Lhs) 
    ->  set_constraint(Lhs, [Lhs\=Rhs])
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, [Lhs\=Rhs])
    ;   true
    ),
    write('UPDATING EDGES...'), writeln(Lhs),
    update_edges(C_in, Lhs, Lhs\=Rhs, C_tmp), !,
    write('UPDATING EDGES...'), writeln(Rhs),
    update_edges(C_tmp, Rhs, Lhs\=Rhs, C_out), !, 
    write('C_in: '), writeln(C_in), write('C_out: '), writeln(C_out).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tree Structure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
one(leaf(1)).
zero(leaf(0)).

% Represent trees as tree(Root,[(Edge1, Subtree1), (Edge2, Subtree2), ...])
make_tree(Root, Edges, Subtrees, tree(Root, L)) :-
    myzip(Edges, Subtrees, L).

% Fummy predicates for and/or
and(leaf(1), _T, _T) :- !.
and(_T, leaf(1), _T) :- !.
and(leaf(0), _T, leaf(0)) :- !.
and(_T, leaf(0), leaf(0)) :- !.
or(leaf(1), _T, leaf(1)) :- !.
or(_T, leaf(1), leaf(1)) :- !.
or(leaf(0), _T, _T) :- !.
or(_T, leaf(0), _T) :- !.
and(_T1, _T2, and(_T1, _T2)) :- !.
or(_T1, _T2, or(_T1, _T2)) :- !.

% OSSD contains X if X is the root
contains(tree(Y, _), X) :- X==Y, !.

% OSDD contains X if X is in the children lists
contains(tree(Y, L), X) :-
    X \== Y,
    contains(L, X).

% OSDD constaints X if X is in the current sub-OSDD
% or if X is in a later sub-OSDD
contains([(_C,T)|R], X) :-
    (contains(T, X) 
    -> true
    ;  contains(R, X)
    ).

% For and/or OSDD pairs, X is in the left or right OSDD
contains(and(T1, _T2), X) :-
    contains(T1, X), !.
contains(and(_T1, T2), X) :-
    contains(T2, X), !.
contains(or(T1, _T2), X) :-
    contains(T1, X), !.
contains(or(_T1, T2), X) :-
    contains(T2, X), !.

% If X is a constant, leave T_in unchanged
update_edges(T_in, X, _C, T_in) :- atomic(X).

% If the input tree is connected with an and/or node
%     recurse on the left and right subtrees
update_edges(and(T1,T2), X, C, and(T1out,T2out)) :-
    var(X),
    update_edges(T1, X, C, T1out),
    update_edges(T2, X, C, T2out).
update_edges(or(T1,T2), X, C, or(T1out,T2out)) :-
    var(X),
    update_edges(T1, X, C, T1out),
    update_edges(T2, X, C, T2out).

% If X is the root of the tree, append C to X's constraint list
%     then add a 0 leaf with the complement of C as the edge
update_edges(tree(X, [(C1, S)]), Y, C, T_out) :-
    X==Y,
    basics:append(C1, [C], C2),
    write('NEW CONSTRAINTS: '), writeln(C2),
    complement(C2, (Complements, Zeros)),
    write('COMPLEMENTS: '), writeln(Complements), 
    write('ZEROS: '), writeln(Zeros),
    basics:append([C], Complements, Constraints),
    basics:append([S], Zeros, Subtrees),
    write('CONSTRAINTS: '), writeln(Constraints),
    write('SUBTREES: '), writeln(Subtrees),
    make_tree(X, Constraints, Subtrees, T_out),
    write('T-OUT: '), writeln(T_out), !.

% If X is not the root, recurse on the edges of the tree
update_edges(tree(X, S1), Y, C, tree(X, S2)) :-
    X \== Y,
    update_edges(S1, Y, C, S2).

% Base case for edge recursion
update_edges([], _Y, _C, []).

% Updates the subtrees in the edge list one at a time
update_edges([(_E, T) | R], X, C, [(_E, T1)| R1]) :-
    update_edges(T, X, C, T1),
    update_edges(R, X, C, R1).

% Leaf nodes are left unchanged
update_edges(leaf(_X), Y, _C, leaf(_X)) :- var(Y).

% Ordering relation for switch/instance pairs
ord((S1, I1), (S2, I2), C, O) :-
    atomic(I1), atomic(I2),
    (I1 @< I2
    ->  O = lt
    ;   (I1 @= I2
	    ->  ord(S1, S2, C, O)
	    ;   O = gt
	    )
    ).

ord(S1, S2, C, O) :-
    functor(S1, F1, _),
    functor(S2, F2, _),
    (F1 @< F2
    ->  O = lt
    ;   (F1 @= F2
	    ->  S1 =.. [F1| Args1],
	        S2 =.. [F1| Args2],
	        ord(Args1, Args2, C, O)
	    ;   O = gt
	    )
    ).

ord([A1 | A1Rest], [A2 | A2Rest], C, O) :-
    % check whether constraint formula (which ?) entails A1 < A2 or A1
    % > A2 or there is no ordering
    true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Attribute processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Type attribute handler
type_handler(T, X) :-
    (var(X) 
    ->  (get_attr(X, type, _T)
        ->  T = _T     % X is also attributed variable
        ;   true       % X is not attributed variable
        )
    ;   atomic(X),
        basics:member(X, T)
    ).

% Attribute handlers
id_handler(_,_).
constraint_handler(_,_).
bounds_var_handler(_,_).

% Sets type attribute of a variable to the domain to the variable.
set_type(X, T) :-
    var(X),
    (get_attr(X, type, T1)
    ->  T = T1  % We can't change type of a variable
    ;   put_attr(X, type, T)
    ).

% Sets id attribute of a random variable to (S, I).
% Where S is the switch name and I is the instance.
set_id(X, (S, I)) :-
    var(X),
    (get_attr(X, id, (S1, I1))
    ->  S=S1, I=I1  % We can't change id of a variable
    ;   put_attr(X, id, (S, I))
    ).

% Sets constraint attribute of a variable.
% If X already has a constraint list and C is not already in the list, 
%     append C to the constraint list.
% Otherwise initialize the constraint list of X to C.
set_constraint(X, C) :-
    writeln('\n    IN SET_CONSTRAINT'),
    var(X),
    read_bounds_var(X, B),
    write('    C: '), writeln(C),
    (get_attr(X, constraint, CX)
    ->  (listutil:absmember(C, CX)
        ->  true
        ;   basics:append(CX, C, _C),
            put_attr(X, constraint, _C),
            rewrite_constraint(B, X, C, CB),
            apply_bounds(B, CB)
        )
    ;   put_attr(X, constraint, C),
        rewrite_constraint(B, X, C, CB),
        apply_bounds(B, CB)
    ), 
    writeln('    EXIT SET_CONSTRAINT\n').

% Reads bounds_var attribute, if it doesn't exist set to an unbound variable
% ensuring that X and B are not the same variable.
read_bounds_var(X, B) :-
    var(X),
    (get_attr(X, bounds_var, B)
    ->  true
    ;   put_attr(X, bounds_var, B)
    ), 
    X \== B, !.

% Reads constraint attribute, if it doesn't exist set to empty constraint.
read_constraint(X, C) :-
    var(X),
    (get_attr(X, constraint, C)
    ->  true
    ;   C = [],
        put_attr(X, constraint, C)
    ).

% Reads type attribute.
% If X is a variable and its type is not set, we set it to an unbound value.
read_type(X, T) :-
    var(X),
    (get_attr(X, type, T)
    ->  true
    ;   var(T),
        put_attr(X, type, T)
    ).

% Lookup type of a constant by searching for a type T which X is an element of.
lookup_type(X, T) :-
    atomic(X),
    values(_, T),
    basics:member(X, T), !.

% Reads id attribute, if it doesn't exist set it to unbound pair of variables.
read_id(X, (S, I)) :-
    var(X),
    (get_attr(X, id, (S, I))
    ->  true
    ;   var(S), var(I),  % [?] Is this needed?
        put_attr(X, id, (S, I))
    ).

% Display handlers
% Assert display_attributes(on) to display the value of the attribute
display_type(A) :- (display_attributes(on) -> write(A); true).
display_id(A) :- (display_attributes(on) -> write(A); true).
display_constr(A) :- (display_attributes(on) -> write(A); true).
display_bounds_var(A) :- (display_attributes(on) -> write(A); true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraint processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Complements a constraint list
complement([], ([], [])).
complement([C|Cs], ([C_comp|C_comps],[leaf(0)|Zeros])) :-
    complement_atom(C, C_comp),
    complement(Cs, (C_comps, Zeros)).

% Complements a atomic constraint
complement_atom(X=Y, X\=Y).
complement_atom(X\=Y, X=Y).

% Rewrites constraints from X to X:bounds_var
rewrite_constraint(B, X, [X=Const], [B=Const]) :- X\==B, var(X), atomic(Const), !.
rewrite_constraint(B, X, [Const=X], [Const=B]) :- X\==B, var(X), atomic(Const), !.
rewrite_constraint(B, X, [X\=Const], [B\=Const]) :- X\==B, var(X), atomic(Const), !.
rewrite_constraint(B, X, [Const\=X], [Const\=B]) :- X\==B, var(X), atomic(Const), !.
rewrite_constraint(B, X, [X=Y], [B=C]) :- X\==B, X\==Y, var(Y), read_bounds_var(Y, C), !.
rewrite_constraint(B, X, [Y=X], [C=B]) :- X\==B, X\==Y, var(Y), read_bounds_var(Y, C), !.
rewrite_constraint(B, X, [X\=Y], [B\=C]) :- X\==B, X\==Y, var(Y), read_bounds_var(Y, C), !.
rewrite_constraint(B, X, [Y\=X], [C\=B]) :- X\==B, X\==Y, var(Y), read_bounds_var(Y, C), !.

% Uses constraint C to set corresponding bounds constraint
% Handles =, \= constraints
apply_bounds(X, [X=Y]) :- X #= Y.
apply_bounds(X, [Y=X]) :- Y #= X.
apply_bounds(X, [X\=Y]) :- X #\= Y.
apply_bounds(X, [Y\=X]) :- Y #\= X.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Query processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Maps the domain of an exported query to the integer representation
map_domain(Q, _Q) :-
    write('Q: '), writeln(Q),
    values_list(L),
    Q =.. [F | Args],
    map_args(Args, _Args, L),
    basics:append(_Args, [leaf(1), O], OSDD_Args),
    _Q =.. [F | OSDD_Args],
    write('_Q: '), writeln(_Q).

% Maps an individual argument to it's corresponding interger representation
map_args([], [], _).
map_args([Arg|Args], [_Arg|_Args], L) :-
    (basics:ith(I, L, Arg)
    ->  _Arg = I
    ;   _Arg = Arg
    ),
    map_args(Args, _Args, L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Visualization using DOT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
writeDot(OSDD, DotFile) :-
    paths(OSDD, Paths),
    current_prolog_flag(write_attributes, F),
    set_prolog_flag(write_attributes, ignore),
    open(DotFile, write, Handle),
    write(Handle, 'strict digraph osdd {\n'),
    writeDotPaths(Paths, Handle),
    write(Handle, '}\n'),
    close(Handle),
    set_prolog_flag(write_attributes, F).

writeDotPaths([], _H).
writeDotPaths([P|R], Handle) :-
    writeDotPath(P, Handle),
    writeDotPaths(R, Handle).

writeDotPath([(Var,Label)], Handle) :-
    (Label=0;Label=1),
    write(Handle, Var),
    write(Handle, ' [label='),
    write(Handle, Label),
    write(Handle, '];\n').

writeDotPath([(V1,L1), E| R], Handle) :-
    R = [(V2,_L2)|_],
    write(Handle, V1), write(Handle, ' [label='), write(Handle, L1), write(Handle, '];\n'),
    write(Handle, V1), write(Handle, ' -> '), write(Handle, V2), write(Handle, ' [label='), write(Handle, '"'),writeDotConstraint(Handle, E), write(Handle, '"'), write(Handle, '];\n'),
    writeDotPath(R, Handle).

writeDotConstraint(Handle, null) :-
    write(Handle, '').
writeDotConstraint(Handle, []) :-
    write(Handle, '').
writeDotConstraint(Handle, [C]) :-
    write1(Handle, C).
writeDotConstraint(Handle, [C|R]) :-
    R \= [],
    write1(Handle, C), write(Handle, ','),
    writeDotConstraint(Handle, R).

write1(Handle, X=Y) :-
    write(Handle, X=Y).
write1(Handle, X\=Y) :-
    write(Handle, X), write(Handle, '\\\='), write(Handle, Y).
write1(Handle, X<Y) :-
    write(Handle, X<Y).

% collect paths in an OSDD
% paths are simply sequences (lists) of node,edge,node... values nodes
% are represented by pairs (VarName, Label). This is needed because,
% otherwise leaves "and", "or" nodes will get combined.
paths(leaf(X), [[(_Y,X)]]). % fresh variable Y helps distinguish from other nodes with same value of X

paths(and(T1, T2), P) :-
    paths(T1, P1),
    addprefix([(Y,and),null], P1, P1A),
    paths(T2, P2),
    addprefix([(Y,and),null], P2, P2A),
    basics:append(P1A, P2A, P).

paths(or(T1, T2), P) :-
    paths(T1, P1),
    addprefix([(Y,or),null], P1, P1A),
    paths(T2, P2),
    addprefix([(Y,or),null], P2, P2A),
    basics:append(P1A, P2A, P).

paths(tree(Root, Subtrees), P) :-
    paths1(Root, Subtrees, [], P).

paths1(_Root, [], _P, _P).
paths1(Root, [(E,T)|R], Pin, Pout) :-
    paths(T, P1),
    addprefix([(Root,Root),E], P1, P2),
    basics:append(Pin, P2, P3),
    paths1(Root, R, P3, Pout).

addprefix(_L, [], []).
addprefix(L, [P|R], [P1|RR]) :-
    basics:append(L, P, P1),
    addprefix(L, R, RR).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Misc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
display_attributes(on).  % control display of attributes

myzip([], [], []).
myzip([A|AR], [B|BR], [(A,B)|R]) :-
    myzip(AR, BR, R).