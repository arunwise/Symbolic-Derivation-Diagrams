/*
 * Code for symbolic inference using OSDDs.
 * Usage: ?- [bounds, syminfer, 'path/to/transformed_file'] % Load files and libraries
 * To construct an OSDD for ground query q(v1,...,vn) use ?- q(v1,....,vn,leaf(1),O).
 */
:- import get_attr/3, put_attr/3, install_verify_attribute_handler/4, install_attribute_portray_hook/3 from machine.

:- install_verify_attribute_handler(type, AttrValue, Target, type_handler(AttrValue, Target)).
:- install_verify_attribute_handler(id, AttrValue, Target, id_handler(AttrValue, Target)).
:- install_verify_attribute_handler(constraint, AttrValue, Target, constraint_handler(AttrValue, Target)).

:- install_attribute_portray_hook(type, Attr, display_type(Attr)).
:- install_attribute_portray_hook(id, Attr, display_id(Attr)).
:- install_attribute_portray_hook(constraint, Attr, display_constr(Attr)).

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
% Constraint processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Definition of msw constraint processing.
%     If X is in C_in 
%         set C_in = C_out
%     Otherwise 
%         First set the type of X to be the domain of S,
%         Set bounds range of X,
%         Then set the ID of X to be the pair (S, I),
%         construct the OSDD rooted at X with a single edge labeled with constraints C and a leaf node 1.
msw(S, I, X, C_in, C_out) :- !,
    writeln('\nIN MSW...'),
    (contains(C_in, X)
    ->  C_out = C_in
    ;   values(S, T),
        set_type(X, T),
        /*intrange(S, Low, High),
        X in Low..High,*/
        set_id(X, (S, I)),
        read_constraint(X, C),
        one(One),
        complement(C, (C_comp, Zeros)),
        make_tree(X, [C|C_comp], [One|Zeros], Osdd),   % osdd: X -- C --> 1
        and(C_in, Osdd, C_out),
        write('C_in: '), writeln(C_in), write('C_out: '), writeln(C_out)
    ).

% Definition of atomic constraint processing for equality constraints.
% First check if at least one of the arguments of the constraint is a variable
% Then get the types of both arguments
% Update the constraint lists of any variable arguments
% Finally update the edges for Lhs and Rhs.
constraint(Lhs=Rhs, C_in, C_out) :-
    write('\n'),writeln(Lhs=Rhs),
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    (var(Lhs) 
    ->  read_type(Lhs, T1)
    ;   lookup_type(Lhs, T1)
    ),
    (var(Rhs) 
    ->  read_type(Rhs, T2)
    ;   lookup_type(Rhs, T2)
    ),
    T1 = T2,
    (var(Lhs) 
    ->  set_constraint(Lhs, [Lhs=Rhs])
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, [Lhs=Rhs])
    ;   true
    ),
    (var(Lhs)
    ->  read_constraint(Lhs, C), satisfiable(Lhs, C, T1, _)
    ;   read_constraint(Rhs, C), satisfiable(Rhs, C, T2, _)
    ),
    update_edges(C_in, Lhs, Lhs=Rhs, C_tmp), !,
    update_edges(C_tmp, Rhs, Lhs=Rhs, C_out), !, write('C_in: '), writeln(C_in), write('C_out: '), writeln(C_out).

% Definition of atomic constraint processing for inequality constraints.
% Same logic as in equality constraints.
constraint(Lhs\=Rhs, C_in, C_out) :-
    write('\n'),writeln(Lhs\=Rhs),
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    (var(Lhs) 
    ->  read_type(Lhs, T1)
    ;   lookup_type(Lhs, T1)
    ),
    (var(Rhs) 
    ->  read_type(Rhs, T2)
    ;   lookup_type(Rhs, T2)
    ),
    T1 = T2,
    (var(Lhs) 
    ->  set_constraint(Lhs, [Lhs\=Rhs])
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, [Lhs\=Rhs])
    ;   true
    ),
    (var(Lhs)
    ->  read_constraint(Lhs, C), satisfiable(Lhs, C, T1, _)
    ;   read_constraint(Rhs, C), satisfiable(Rhs, C, T2, _)
    ),
    update_edges(C_in, Lhs, Lhs\=Rhs, C_tmp), !,
    update_edges(C_tmp, Rhs, Lhs\=Rhs, C_out), !, write('C_in: '), writeln(C_in), write('C_out: '), writeln(C_out).

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

% ID attribute handler
% Nothing needs to be done in id attribute handler
id_handler(I, X) :- true.

% Constraint attribute handler.
% If X is a variable which has a constraint list CX,
%     merge C and CX and see if the new list is satisfiable w.r.t. the domain of X,
%     apply the new constraints and restricted domain as attributes of X.
% Else X is a constant,
%     and X unifies when X is a member of C.
% ---
% TESTS: set_constraint(X, [a = X, X \= b]), set_constraint(Y, [Y = d]), set_type(Y, [c, e, a]), X=Y.  [no]
%        set_constraint(X, [X \= b, a = X]), set_constraint(Y, [Y \= e, Y=Z]), set_type(Y, [c, e, a]), X=Y.  [yes]
%        set_constraint(X, [X \= b, a \= X]), set_constraint(Y, [Y \= e, Y \= c]), set_type(Y, [c, e, a]), X=Y.  [no]
%        set_constraint(X, [X \= b, a = X, X \= Y]), set_constraint(Y, [Y \= e, Y=Z]), set_type(Y, [c, e, a]), X=Y.  [no]
constraint_handler(C, X) :-
    writeln('START constraint_handler'), write(C),
    (var(X), get_attr(X, constraint, CX)
    ->  listutil:merge(C, CX, _C), 
        write('Merged constraints: '), writeln(_C), writeln('END constraint_handler\n'),
        read_type(X, T),
        satisfiable(X, _C, T, T_restricted),
        put_attr(X, type, T_restricted),
        put_attr(X, constraint, _C)
    ;   basics:member(X, C)
    ).

% An empty list of constraints is satisfiable given that the domain is not empty.
satisfiable(_, [], T, T) :- T \= [].

% Handles equality constraints.
% If the constraint is of the form X = a (or a = X) and a is in the domain of X,
%     restrict the domain of X to be a
% Else if the constraint is of the form X = Y (or Y = X),
%     continue without modifying the domain of X
% Else,
%     fail.
satisfiable(X, [Lhs = Rhs|Cs], T_in, T_out) :- 
    writeln('START satisfiable'), write('LHS: '), writeln(Lhs), write('RHS: '), writeln(Rhs), write('Domain: '), writeln(T_in),
    (X = Lhs
    ->  (var(Rhs)
        ->  (read_type(Rhs, T), ground(T)
            ->  true
            ;   T = T_in
            )
        ;   basics:member(Rhs, T_in), T = Rhs  % If Rhs is not a variable, check if it is in the domain of T, if so restrict T to Rhs
        )
    ;   (X = Rhs
        ->  (var(Lhs)
            ->  (read_type(Lhs, T), ground(T)
                ->  true
                ;   T = T_in
                )
            ;   basics:member(Lhs, T_in), T = Lhs
            )
        ;   false
        )
    ),
    write('Domain Out: '), writeln(T), writeln('END satisfiable\n'),
    satisfiable(X, Cs, T, T_out).

% Handles inequality constraints.
% If the constraint is of the form X \= a (or a \= X) and a is in the domain of X,
%     remove a from the domain of X
% Else if the constraint is of the form X \= Y (or Y \= X), 
%     continue without modifying the domain of X
% Else,
%     fail.
satisfiable(X, [Lhs \= Rhs|Cs], T_in, T_out) :- 
    writeln('START satisfiable'), write('LHS: '), writeln(Lhs), write('RHS: '), writeln(Rhs), write('Domain: '), writeln(T_in),
    (X = Lhs
    ->  (var(Rhs)
        ->  (Rhs = Lhs
            ->  false
            ;   (read_type(Rhs, _T), ground(_T)
                ->  listutil:merge(T, _T, T_in)  % T is T_in \ _T (set difference)
                ;   T = T_in  % Rhs is a "free variable" in the OSDD
                )
            )
        ;   (basics:member(Rhs, T_in)
            ->  basics:select(Rhs, T_in, T)
            ;   T = T_in
            )
        )
    ;   (X = Rhs
        ->  (var(Lhs)
            ->  (Lhs = Rhs
                ->  false
                ;   (read_type(Rhs, _T), ground(_T)
                    ->  listutil:merge(T, _T, T_in)  % T is T_in \ _T (set difference)
                    ;   T = T_in  % Rhs is a "free variable" in the OSDD
                    )
                )
            ;   (basics:member(Lhs, T_in)
                ->  basics:select(Lhs, T_in, T)
                ;   T = T_in
                )
            )
        ;   false
        )
    ),
    write('Domain Out: '), writeln(T), writeln('END satisfiable\n'),
    satisfiable(X, Cs, T, T_out).

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
    var(X),
    (get_attr(X, constraint, C1)
    ->  (basics:member(C, C1)
        ->  true
        ;   basics:append(C1, C, C2),
            put_attr(X, constraint, C2)/*,
            set_bounds(X, C)*/
        )
    ;   put_attr(X, constraint, C)/*,
        set_bounds(X, C)*/
    ).

% Reads constraint attribute, if it doesn't exist set to empty constraint.
read_constraint(X, C) :-
    var(X),
    (get_attr(X, constraint, C)
    ->  true
    ;   C=[],
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
% NOTE: Should set T to the greatest superset.
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

% Complements a constraint list
complement([], ([], [])).
complement([C|Cs], ([C_comp|C_comps],[Zero|Zeros])) :-
    zero(Zero),
    complement_atom(C, C_comp),
    complement(Cs, (C_comps, Zeros)).

% Complements a atomic constraint
complement_atom(X=Y, X\=Y).
complement_atom(X\=Y, X=Y).

% Uses constraint C to set corresponding bounds constraint
% Handles =, \= constraints
/*set_bounds(X, [X=Y]) :- X #= Y.
set_bounds(X, [Y=X]) :- Y #= X.
set_bounds(X, [X\=Y]) :- X #\= Y.
set_bounds(X, [Y\=X]) :- Y #\= X.*/

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
update_edges(tree(X, [(C1,S)]), Y, C, tree(X, [(C2, S)])) :-
    X==Y,
    basics:append(C1, [C], C2), !.

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
    ->
	O = lt
    ;
        (I1 @= I2
	->
	    ord(S1, S2, C, O)
	;
	    O = gt
	)
    ).

ord(S1, S2, C, O) :-
    functor(S1, F1, _),
    functor(S2, F2, _),
    (F1 @< F2
    ->
	O = lt
    ;
        (F1 @= F2
	->
	    S1 =.. [F1| Args1],
	    S2 =.. [F1| Args2],
	    ord(Args1, Args2, C, O)
	;
	    O = gt
	)
    ).

ord([A1 | A1Rest], [A2 | A2Rest], C, O) :-
    % check whether constraint formula (which ?) entails A1 < A2 or A1
    % > A2 or there is no ordering
    true.

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