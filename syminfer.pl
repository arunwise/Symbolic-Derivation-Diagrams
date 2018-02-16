/*
 * Code for symbolic inference using OSDDs.
 * Usage: ?- [bounds, syminfer, 'path/to/transformed_file'] % Load files and libraries
 * To construct an OSDD for ground query q(v1,...,vn) use ?- q(v1,....,vn,leaf(1),O).
 */
:- import get_attr/3, put_attr/3, install_verify_attribute_handler/4, install_attribute_portray_hook/3 from machine.
:- import vertices_edges_to_ugraph/3, transitive_closure/2, edges/2,
   neighbors/3, vertices/2 from ugraphs.
:- import list_to_ord_set/2 from ordsets.

:- install_verify_attribute_handler(type, AttrValue, Target, type_handler(AttrValue, Target)).
:- install_verify_attribute_handler(id, AttrValue, Target, id_handler(AttrValue, Target)).
:- install_verify_attribute_handler(bounds_var, AttrValue, Target, bounds_var_handler(AttrValue, Target)).

:- install_attribute_portray_hook(type, Attr, display_type(Attr)).
:- install_attribute_portray_hook(id, Attr, display_id(Attr)).
:- install_attribute_portray_hook(bounds_var, Attr, display_bounds_var(Attr)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraint/msw definitions
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
% OSDD construction definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
one(leaf(1)).
zero(leaf(0)).

% Represent trees as tree(Root,[(Edge1, Subtree1), (Edge2, Subtree2), ...])
make_tree(Root, Edges, Subtrees, tree(Root, L)) :-
    myzip(Edges, Subtrees, L).

myzip([], [], []).
myzip([E|ER], [T|TR], [edge_subtree(E,T)|R]) :-
    myzip(ER, TR, R).

% Returns a consistent OSDD
make_osdd(R, Eis, Oh) :-
    (Eis = []
    ->  Oh = leaf(0)
    ;   order_edges(Eis, Eos),
        Oh = tree(R, Eos)
    ).

% and_osdd(+OSDD_handle1, +OSDD_handle2, -OSDD_handle):
and(Oh1, Oh2, Oh) :-
    bin_op(and, Oh1, Oh2, [], Oh).

% or_osdd(+OSDD_handle1, +OSDD_handle2, -OSDD_handle):
or(Oh1, Oh2, Oh) :-
    bin_op(or, Oh1, Oh2, [], Oh).

% bin_op(+Operation, +OSDD1, +OSDD2, -OSDD_Out):
bin_op(Op, leaf(1), Oh2, Ctxt, Oh) :- !, bin_op1(Op, Oh2, Ctxt, Oh).
bin_op(Op, leaf(0), Oh2, Ctxt, Oh) :- !, bin_op0(Op, Oh2, Ctxt, Oh).
bin_op(Op, Oh1, leaf(1), Ctxt, Oh) :- !, bin_op1(Op, Oh1, Ctxt, Oh).
bin_op(Op, Oh1, leaf(0), Ctxt, Oh) :- !, bin_op0(Op, Oh1, Ctxt, Oh).

bin_op(Op, Oh1, Oh2, Ctxt, Oh) :-
    Oh1 = tree(R1, E1s), Oh2 = tree(R2, E2s),
    compare_roots(R1, R2, C),
    (Op == or, writeln('------OR------')
    ->  (C < 0
        ->  try_to_add_zero_branch(E1s, _E1s), _E2s = E2s
        ;   (C > 0
            ->  try_to_add_zero_branch(E2s, _E2s), _E1s = E1s
            ;   _E1s = E1s, _E2s = E2s, R1 = R2, writeln('===EQUAL===')
            )
        )
    ;   _E1s = E1s, _E2s = E2s, writeln('------AND------')
    ),
    _Oh1 = tree(R1, _E1s), _Oh2 = tree(R2, _E2s),
    write('    OSDD1: '), writeln(_Oh1), write('    OSDD2: '), writeln(_Oh2),
    (C < 0  /* R1 is smaller */
    -> apply_binop(Op, _E1s, _Oh2, Ctxt, Es), make_osdd(R1, Es, Oh)
    ;   (C > 0 /* R2 is smaller */
        ->  apply_binop(Op, _E2s, _Oh1, Ctxt, Es), make_osdd(R2, Es, Oh)
        ;   /* R1=R2 */ apply_all_binop(Op, _E1s, _E2s, Ctxt, Es), make_osdd(R1, Es, Oh)
        )
    ),
    write('    RESULT: '), writeln(Oh).

bin_op1(and, Oh1, Ctxt, Oh) :- apply_constraint(Oh1, Ctxt, Oh).
bin_op1(or, _, _Ctxt, leaf(1)).
bin_op0(or, Oh1, Ctxt, Oh) :- apply_constraint(Oh1, Ctxt, Oh).
bin_op0(and, _, _Ctxt, leaf(0)).

/* Do binop with all trees in list (arg 2) and the other given tree (arg 3) */
:- index apply_binop/5-2.
apply_binop(_Op, [], _Oh2, _Ctxt, []).
apply_binop(Op, [edge_subtree(C,Oh1)|E1s], Oh2, Ctxt, Edges) :-
    (conjunction(C, Ctxt, Ctxt1)
    ->  bin_op(Op, Oh1, Oh2, Ctxt1, Oh),
        Edges = [edge_subtree(C,Oh)|Es],
        apply_binop(Op, E1s, Oh2, Ctxt, Es)
    ;   % inconsistent, drop this edge:
        apply_binop(Op, E1s, Oh2, Ctxt, Edges)
    ).

/* Do binop, pairwise, for all trees in the two lists (arg 2, and arg 3) */
apply_all_binop(Op, E1s, E2s, Ctxt, Es) :- apply_all_binop(Op, E1s, E2s, Ctxt, [], Es).

:- index apply_all_binop/6-3.
apply_all_binop(_Op, _E1s, [], _Ctxt, Es, Es).
apply_all_binop(Op, E1s, [edge_subtree(C2,Oh2)|E2s], Ctxt, Eis, Eos) :-
    (conjunction(C2, Ctxt, _Ctxt1)
    ->  apply_1_binop(Op, E1s, C2, Oh2, Ctxt, Eis, Ets)
    ;   Eis = Ets  % C2's constraint is inconsistent wrt Ctxt, so drop these edges
    ),
    apply_all_binop(Op, E1s, E2s, Ctxt, Ets, Eos).

apply_1_binop(_Op, [], _C2, _Oh2, _Ctxt, Es, Es).
apply_1_binop(Op, [edge_subtree(C1,Oh1)|E1s], C2, Oh2, Ctxt, Eis, Eos) :-
    (conjunction(C1, C2, C), conjunction(C, Ctxt, Ctxt1)
    ->  bin_op(Op, Oh1, Oh2, Ctxt1, Oh),
        Eos = [edge_subtree(C, Oh)|Ets]
    ;   Eos = Ets
    ),
    apply_1_binop(Op, E1s, C2, Oh2, Ctxt, Eis, Ets).

apply_constraint(Oh1, C, Oh2) :- apply_constraint(Oh1, C, C, Oh2).
apply_constraint(leaf(X), _, _, leaf(X)).
apply_constraint(tree(R, E1s), Cons, Ctxt, Oh2) :-
    apply_constraint_edges(E1s, Cons, Ctxt, E2s),
    (E2s = []
    ->  Oh2 = leaf(0)
    ;   Oh2 = tree(R, E2s)
    ).
apply_constraint_edges([], _Cons, _Ctxt, []).
apply_constraint_edges([edge_subtree(C,T)|E1s], Cons, Ctxt, E2s) :-
    (conjunction(C, Ctxt, Ctxt1)
    ->  conjunction(C, Cons, C1),
        apply_constraint(T, Ctxt1, T1),
        E2s = [edge_subtree(C1,T1)|Eos]
    ;   E2s = Eos
    ),
    apply_constraint_edges(E1s, Cons, Ctxt, Eos).


split_if_needed(Oh1, Oh2) :-
    (identify_late_constraint(Oh1, C)
    ->  split(Oh1, C, Oh3),
        split_if_needed(Oh3, Oh2)
    ;   Oh2 = Oh1
    ).

identify_late_constraint(Oh, C) :- identify_late_constraint(Oh, [], C).
identify_late_constraint(tree(R, Es), Ctxt, C) :-
    identify_late_constraint(Es, R, Ctxt, C).
identify_late_constraint([edge_subtree(C1,_T1)|_Es], R, Ctxt, C) :-
    basics:member(C, C1),  % iterate through all constraints in C1
    not listutil:absmember(C, Ctxt),
    not_at(R, C),   !.
identify_late_constraint([edge_subtree(C1,T1)|_Es], _R, Ctxt, C) :-
    conjunction(C1, Ctxt, Ctxt1),
    identify_late_constraint(T1, Ctxt1, C), !.
identify_late_constraint([_|Es], R, Ctxt, C) :-
    identify_late_constraint(Es, R, Ctxt, C).

not_at(R, C) :- not testable_at(R, C).

split(Oh1, C, Oh2) :-
    split(Oh1, C, [], Oh2).

split(leaf(X), _C, _Ctxt, leaf(X)).
split(tree(R, E1s), C, Ctxt, tree(R, E2s)) :- 
    (testable_at(R, C)
    ->   negate(C, NC),
        (conjunction([C], Ctxt, Ctxt1)
        ->  apply_constraint_edges(E1s, [C], Ctxt1, E11s)
        ;   E11s = []
        ),
        (conjunction([NC], Ctxt, Ctxt2)
        ->  apply_constraint_edges(E1s, [NC], Ctxt2, E12s)
        ;   E12s = []
        ),
        basics:append(E11s, E12s, E2m),
        order_edges(E2m, E2s)
    ;  split_all(E1s, C, Ctxt, E2s)
    ).

split_all([], _, _, []).
split_all([edge_subtree(C1,T1)|Es], C, Ctxt, E2s) :-
    (conjunction(C1, Ctxt, Ctxt1)
    ->  split(T1, C, Ctxt1, T2),
        E2s = [edge_subtree(C1, T2)|Eos]
    ;   E2s = Eos
    ),
    split_all(Es, C, Ctxt, Eos).

%---------------- NEEDS DONE -----------------
% order_edges(E1s, E2s): E2s contains all edges in E1s, but ordered in a canonical way
order_edges(X, X).
%---------------- NEEDS DONE -----------------

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
update_edges(leaf(_X), Y, _C, leaf(_X)) :- var(Y).% Compares two root nodes based on switch/instance ID
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

%% represent constraint formulas in a canonical way
canonical_form(C, F) :-
    term_variables(C, V),
    edge_list_form(C, EQ, NEQ),
    % use ugraphs to compute closure of equality edges
    complete_equality(EQ, EQC),
    % complete neq edges
    complete_disequality(EQC, NEQ, NEQ1),
    % discard edges between constants
    discard_spurious_edges(NEQ1, NEQ2),
    % sort using ordsets to get canonical representation
    list_to_ord_set(EQC, EQORD),
    list_to_ord_set(NEQ2, NEQORD),
    F = cg(EQORD, NEQORD),
    true.

%% atomic constraints are represented as edges in constraint graph,
%% we maintain two lists corresponding to equality constraints and
%% disequality constraints. Since the graph is undirected for each
%% atomic constraint we have two edges going in either direction

%% we use the same representation as that used by "ugraph" package
edge_list_form([], [], []).
edge_list_form([X=Y|R], [S-D, D-S| EQR], NE) :-
    canonical_label(X, S),
    canonical_label(Y, D),
    edge_list_form(R, EQR, NE).
edge_list_form([X\=Y|R], EQ, [S-D, D-S | NER]) :-
    canonical_label(X, S),
    canonical_label(Y, D),
    edge_list_form(R, EQ, NER).

%% Node labels in constraint graph have a canonical form
canonical_label(X, id(S, I)) :-
    var(X),
    read_id(X, (S, I)).
canonical_label(X, X) :-
    atomic(X).

%% complete equality relation in the graph
complete_equality(E, EC) :-
    vertices_edges_to_ugraph([], E, UG),
    transitive_closure(UG, UGC),
    edges(UGC, EC).

%% complete disequality relation in the graph
%% look at each vertex and the set of its neighbors, if two neighbors
%% are connected to it by opposite constraint, add disequality
%% constraint between them as an implicit constraint
complete_disequality(EQ, NEQ, NEQ1) :-
    vertices_edges_to_ugraph([], EQ, G1),
    vertices_edges_to_ugraph([], NEQ, G2),
    vertices(G1, V1),
    vertices(G2, V2),
    basics:append(V1, V2, V),
    complete_disequality_1(V, G1, G2, [], IConstr),
    basics:append(NEQ, IConstr, NEQ1).

% no extra constraints if no variables
complete_disequality_1([], _, _, L, L). 
complete_disequality_1([V|R], G1, G2, ICin, ICout) :-
    (neighbors(V, G1, N1)
    ->
	    true
    ;
        N1 = []
    ),
    (neighbors(V, G2, N2)
    ->
	    true
    ;
        N2 = []
    ),
    pairwise_edges(N1, N2, N),
    basics:append(ICin, N, ICtmp),
    complete_disequality_1(R, G1, G2, ICtmp, ICout).

pairwise_edges(L1, L2, L) :-
    findall(X-Y, (basics:member(X, L1), basics:member(Y,L2)), L).

discard_spurious_edges([], []).
discard_spurious_edges([X-Y|R], L) :-
    X == Y,
    discard_spurious_edges(R, L).
discard_spurious_edges([X-Y|R], L) :-
    X \== Y,
    ((functor(X, id, 2); functor(Y, id, 2))
    ->
	    L = [X-Y|L1],
	    discard_spurious_edges(R, L1)
    ;
        discard_spurious_edges(R, L)
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

% collect paths in an OSDD paths are simply sequences (lists) of
% node,edge,node... values.  nodes are represented by node(VarName,
% Label). This way we can either combine or separate nodes with same
% label
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
