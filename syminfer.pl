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
        %read_bounds_var(X, B),
        %intrange(S, Low, High),
        %B in Low..High,
        set_id(X, (S, I)),
        make_tree(X, [[]], [leaf(1)], Osdd),   % osdd: X -- C --> 1
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
    % Get the types
    (var(Lhs) 
    ->  read_type(Lhs, T1)
    ;   lookup_type(Lhs, T1)
    ),
    (var(Rhs) 
    ->  read_type(Rhs, T2)
    ;   lookup_type(Rhs, T2)
    ),
    nonvar(T1), nonvar(T2),  % Ensure that constraint occurs after the msw/3 is called
    T1 = T2,  % Type check
    % Set the constraints
    /*(var(Lhs)
    ->  set_constraint(Lhs, [Lhs=Rhs])
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, [Lhs=Rhs])
    ;   true
    ),*/
    % Update the edges
    (var(Lhs), var(Rhs), compare_roots(Lhs, Rhs, C)  /* If both are vars then we need to order them */
    ->  (C > 0  /* Rhs is smaller */
        -> update_edges(C_in, Lhs, Lhs=Rhs, C_out)
        ;   (C < 0 /* Lhs is smaller */
            ->  update_edges(C_in, Rhs, Lhs=Rhs, C_out)
            ;   update_edges(C_in, Rhs, Lhs=Rhs, C_out) /* Lhs=Rhs */ 
            )
        )
    ;   (var(Lhs)
        ->  update_edges(C_in, Lhs, Lhs=Rhs, C_out)
        ;   update_edges(C_in, Rhs, Lhs=Rhs, C_out)  /* One of Lhs and Rhs is a variable */
        )
    ), !.

% Definition of atomic constraint processing for inequality constraints.
% Same logic as in equality constraints.
constraint(Lhs\=Rhs, C_in, C_out) :-
    write('\n\= CONSTRAINT: '),writeln(Lhs\=Rhs),
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    % Get the types
    (var(Lhs) 
    ->  read_type(Lhs, T1)
    ;   lookup_type(Lhs, T1)
    ),
    (var(Rhs) 
    ->  read_type(Rhs, T2)
    ;   lookup_type(Rhs, T2)
    ),
    nonvar(T1), nonvar(T2),  % Ensure that constraint occurs after the msw/3 is called
    T1 = T2,  % Type check
    % Set the constraints
    /*(var(Lhs) 
    ->  set_constraint(Lhs, [Lhs\=Rhs])
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, [Lhs\=Rhs])
    ;   true
    ),*/
    % Update the edges
    (var(Lhs), var(Rhs), compare_roots(Lhs, Rhs, C)  /* If both are vars then we need to order them */
    ->  (C > 0  /* Rhs is smaller */
        -> update_edges(C_in, Lhs, Lhs\=Rhs, C_out)
        ;   (C < 0 /* Lhs is smaller */
            ->  update_edges(C_in, Rhs, Lhs\=Rhs, C_out)
            ;   update_edges(C_in, Rhs, Lhs\=Rhs, C_out) /* Lhs=Rhs */ 
            )
        )
    ;   (var(Lhs)
        ->  update_edges(C_in, Lhs, Lhs\=Rhs, C_out)
        ;   update_edges(C_in, Rhs, Lhs\=Rhs, C_out)  /* One of Lhs and Rhs is a variable */
        )
    ), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tree structure definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
one(leaf(1)).
zero(leaf(0)).

% Represent trees as tree(Root,[(Edge1, Subtree1), (Edge2, Subtree2), ...])
make_tree(Root, Edges, Subtrees, tree(Root, L)) :-
    myzip(Edges, Subtrees, L).

myzip([], [], []).
myzip([E|ER], [T|TR], [edge_subtree(E,T)|R]) :-
    myzip(ER, TR, R).

% and_osdd(+OSDD_handle1, +OSDD_handle2, -OSDD_handle):
and(Oh1, Oh2, Oh) :-
    bin_op(and, Oh1, Oh2, Oh).

% or_osdd(+OSDD_handle1, +OSDD_handle2, -OSDD_handle):
or(Oh1, Oh2, Oh) :-
    writeln('========================'), writeln(Oh1), writeln('      OR'), writeln(Oh2), writeln('========================'),
    bin_op(or, Oh1, Oh2, Oh).

% bin_op(+Operation, +OSDD1, +OSDD2, -OSDD_Out):
bin_op(Op, leaf(1), Oh2, Oh) :- !, bin_op1(Op, Oh2, Oh).
bin_op(Op, leaf(0), Oh2, Oh) :- !, bin_op0(Op, Oh2, Oh).
bin_op(Op, Oh1, leaf(1), Oh) :- !, bin_op1(Op, Oh1, Oh).
bin_op(Op, Oh1, leaf(0), Oh) :- !, bin_op0(Op, Oh1, Oh).

bin_op(Op, tree(R1, E1s), tree(R2, E2s), Oh) :-
    compare_roots(R1, R2, C),
    (Op == or
    ->  (C < 0
        ->  try_to_add_zero_branch(E1s, _E1s), _E2s = E2s
        ;   (C > 0
            ->  try_to_add_zero_branch(E2s, _E2s), _E1s = E1s
            ;   try_to_add_zero_branch(E1s, _E1s), try_to_add_zero_branch(E2s, _E2s)
            )
        )
    ;   _E1s = E1s, _E2s = E2s
    ),
    (C < 0  /* R1 is smaller */
    ->  apply_binop(Op, _E1s, tree(R2, _E2s), Es), make_osdd(R1, Es, Oh)
    ;   (C > 0 /* R2 is smaller */
        ->  apply_binop(Op, _E2s, tree(R1, _E1s), Es), make_osdd(R2, Es, Oh)
        ;   apply_all_binop(Op, _E1s, _E2s, Es), R1=R2, make_osdd(R1, Es, Oh) /* R1=R2 */ 
        )
    ).

bin_op1(and, Oh, Oh).
bin_op1(or, _, leaf(1)).
bin_op0(or, Oh, Oh).
bin_op0(and, _, leaf(0)).

/* Do binop with all trees in list (arg 2) and the other given tree (arg 3) */
:- index apply_binop/4-2.
apply_binop(_Op, [], _Oh2, []).
apply_binop(Op, [edge_subtree(C,Oh1)|E1s], Oh2, [edge_subtree(C,Oh)|Es]) :-
    bin_op(Op, Oh1, Oh2, Oh),
    apply_binop(Op, E1s, Oh2, Es).

/* Do binop, pairwise, for all trees in the two lists (arg 2, and arg 3) */
apply_all_binop(Op, E1s, E2s, Es) :- apply_all_binop(Op, E1s, E2s, [], Es).

:- index apply_all_binop/5-3.
apply_all_binop(_Op, _E1s, [], Es, Es).

apply_all_binop(Op, E1s, [edge_subtree(C2,Oh2)|E2s], Eis, Eos) :-
    apply_1_binop(Op, E1s, C2, Oh2, Eis, Ets),
    apply_all_binop(Op, E1s, E2s, Ets, Eos).

apply_1_binop(Op, [], _C2, _Oh2, Es, Es).
apply_1_binop(Op, [edge_subtree(C1,Oh1)|E1s], C2, Oh2, Eis, Eos) :-
    write('\nC2 is: '), writeln(C2),
    write('Edge is: '), writeln(edge_subtree(C1,Oh1)),
    bin_op(Op, Oh1, Oh2, Oh),
    conjunction(C1, C2, C),
    write('Conjunction is: '), writeln(C),
    Ets = [edge_subtree(C, Oh)|Eis],
    apply_1_binop(Op, E1s, C2, Oh2, Ets, Eos).  

make_osdd(R, Eis, Oh) :- Oh = tree(R, Eis).
    /*prune_inconsistent_edges(Eis, Eps),
    (Eps = []
    ->  Oh = leaf(0)
    ;   order_edges(Eps, Eos),
        Oh = tree(R, Eos)
    ).*/

% prune_inconsistent_edges(E1s, E2s):  E2s contains only those edges from E1s whose constraints are satisfiable
prune_inconsistent_edges(X, X).

% order_edges(E1s, E2s): E2s contains all edges in E1s, but ordered in a canonical way
order_edges(X, X).

% Add a zero branch for or operation if there are none present
try_to_add_zero_branch(Es_in, Es_out) :-
    (basics:member(edge_subtree(_, leaf(0)), Es_in)
    ->  Es_out = Es_in
    ;   basics:append(Es_in, [edge_subtree([], leaf(0))], Es_out)
    ).

% OSSD contains X if X is the root
contains(tree(Y, _), X) :- X==Y, !.

% OSDD contains X if X is in the children lists
contains(tree(Y, L), X) :-
    X \== Y,
    contains(L, X).

% OSDD constaints X if X is in the current sub-OSDD
% or if X is in a later sub-OSDD
contains([edge_subtree(_C,T)|R], X) :-
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

% Handles logic for when X is the root of the tree
update_edges(tree(X, Edges), Y, C, tree(X, UpdatedEdges)) :-
    X == Y,
    update_subtrees(Edges, C, [], UpdatedEdges).

% Implements completeness by adding the complement of C to the previous constraints
update_subtrees([], C, Prev, [edge_subtree(Complement, leaf(0))]) :-
    complement_atom(C, _C),
    basics:append(Prev, [_C], Complement).

% Add C to the constraint list on an edge which does not have 0 child
update_subtrees([edge_subtree(C1, T)|Edges], C, Prev, [edge_subtree(C2, T)| UpdatedEdges]) :-
    (T \== leaf(0)
    ->  basics:append(C1, [C], C2),
        basics:append(Prev, C1, Next)
    ;   Next = Prev, C2 = C1
    ),
    update_subtrees(Edges, C, Next, UpdatedEdges).

% If X is not the root, recurse on the edges of the tree
update_edges(tree(X, S1), Y, C, tree(X, S2)) :-
    X \== Y,
    update_edges(S1, Y, C, S2).

% Base case for edge recursion
update_edges([], _Y, _C, []).

% Updates the subtrees in the edge list one at a time
update_edges([edge_subtree(_E, T) | R], X, C, [edge_subtree(_E, T1)| R1]) :-
    update_edges(T, X, C, T1),
    update_edges(R, X, C, R1).

% Leaf nodes are left unchanged
update_edges(leaf(_X), Y, _C, leaf(_X)) :- var(Y).

% Compares two root nodes based on switch/instance ID
compare_roots(R1, R2, 0) :-
    read_id(R1, (S, I)),
    read_id(R2, (S, I)).

compare_roots(R1, R2, -1) :-
    read_id(R1, (S1, I1)),
    read_id(R2, (S2, I2)),
    (I1 @< I2
    ->  true
    ;   (S1 @< S2
        ->  true
        ;   false
        )
    ).

compare_roots(R1, R2, 1) :-
    read_id(R1, (S1, I1)),
    read_id(R2, (S2, I2)),
    (I1 @> I2
    ->  true
    ;   (S1 @> S2
        ->  true
        ;   false
        )
    ).

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

% Combines two constraint lists by conjunction
conjunction(C1, C2, C) :-
    listutil:absmerge(C1, C2, C).

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

% check satisfiability of constraint formula
% below code didn't work as expected
%% satisfiable(C) :-
%%     \+ \+ fs(C).
%% fs([]).
%% fs([X=Y|R]) :-
%%     call(X=Y),
%%     fs(R).
%% fs([X\=Y|R]) :-
%%     call(X\=Y),
%%     fs(R).

%% check satisfiability of constraint formula
satisfiable(C) :-
    basics:copy_term_nat(C, C1), % create a copy of C in C1 without any attributes

    term_variables(C, L),
    term_variables(C1, L1),

    assert_bounds(L, L1),
    assert_constraints(C1),
    label(L1), !.

%% assert Lower..Upper bounds for each variable in second list by
%% looking at the corresponding id in first list.
assert_bounds([], []).
assert_bounds([V|R], [V1|R1]) :-
    read_id(V, (S, _)), % get switch associated with V
    intrange(S, Lower, Upper),
    V1 in Lower..Upper,
    assert_bounds(R, R1).

%% assert #= and #\= constraints
assert_constraints([]).
assert_constraints([X=Y|R]) :-
    X #= Y,
    assert_constraints(R).
assert_constraints([X\=Y|R]) :-
    X #\= Y,
    assert_constraints(R).


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

writeDotPath([node(Var,Label)], Handle) :-
    (Label=0;Label=1),
    write(Handle, Var),
    write(Handle, ' [label='),
    write(Handle, Label),
    write(Handle, '];\n').

writeDotPath([node(V1,L1), E| R], Handle) :-
    R = [node(V2,_L2)|_],
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
paths(leaf(X), [[node(_Y,X)]]). % fresh variable Y helps distinguish from other nodes with same value of X

paths(and(T1, T2), P) :-
    paths(T1, P1),
    addprefix([node(Y,and),null], P1, P1A),
    paths(T2, P2),
    addprefix([node(Y,and),null], P2, P2A),
    basics:append(P1A, P2A, P).

paths(or(T1, T2), P) :-
    paths(T1, P1),
    addprefix([node(Y,or),null], P1, P1A),
    paths(T2, P2),
    addprefix([node(Y,or),null], P2, P2A),
    basics:append(P1A, P2A, P).

paths(tree(Root, Subtrees), P) :-
    paths1(Root, Subtrees, [], P).

paths1(_Root, [], _P, _P).
paths1(Root, [edge_subtree(E,T)|R], Pin, Pout) :-
    paths(T, P1),
    addprefix([node(Root,Root),E], P1, P2),
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
