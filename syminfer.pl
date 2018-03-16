/*
 * Code for symbolic inference using OSDDs.
 * Usage: ?- [syminfer, 'path/to/transformed_file'] % Load files and libraries
 * To construct an OSDD for ground query q(v1,...,vn) use ?- q(v1,....,vn,leaf(1),O).
 */

:- import vertices_edges_to_ugraph/3, transitive_closure/2, edges/2,
   neighbors/3, vertices/2 from ugraphs.
:- import list_to_ord_set/2 from ordsets.
:- import empty_assoc/1, put_assoc/4, get_assoc/3, list_to_assoc/2 from assoc_xsb.
:- import member/2 from basics.

:- import (in)/2, (#=)/2, (#\=)/2, label/1 from bounds.

:- import writeDotFile/2 from visualize.

:- import set_type/2, set_id/2, read_type/2, read_id/2 from attribs.

:- import satisfiable_constraint_graph/2 from constraints.

% copied from bounds.pl
:- op(700,xfx,(#=)).
:- op(700,xfx,(#\=)).
:- op(700,xfx,(in)).
:- op(550,xfx,(..)).

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
        set_id(X, id(S, I)),
	make_osdd(X, [edge_subtree([], leaf(1))], Osdd),
        % make_tree(X, [[]], [leaf(1)], Osdd),   % osdd: X -- C --> 1
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
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    order_constraint(Lhs=Rhs, Ordered_Constraint),

    write('=======\n\n= CONSTRAINT: '), writeln(Ordered_Constraint),
    write('\nCin: '), writeln(C_in),

    %% % Get the types
    %% (var(Lhs) 
    %% ->  read_type(Lhs, T1)
    %% ;   lookup_type(Lhs, T1)
    %% ),
    %% (var(Rhs) 
    %% ->  read_type(Rhs, T2)
    %% ;   lookup_type(Rhs, T2)
    %% ),
    %% nonvar(T1), nonvar(T2),  % Ensure that constraint occurs after the msw/3 is called
    %% T1 = T2,  % Type check

    (var(Lhs)
    ->
	type_check(Lhs, Rhs)
    ;
        type_check(Rhs, Lhs)
    ),

    % Update the edges
    (var(Lhs), var(Rhs), compare_roots(Lhs, Rhs, C)  /* If both are vars then we need to order them */
    ->  (C > 0  /* Rhs is smaller */
        -> update_edges(C_in, Lhs, Ordered_Constraint, [], C_out)
        ;   (C < 0 /* Lhs is smaller */
            ->  update_edges(C_in, Rhs, Ordered_Constraint, [], C_out)
            ;   fail
            )
        )
    ;   (var(Lhs)  /* One of Lhs and Rhs is a variable */
        ->  update_edges(C_in, Lhs, Ordered_Constraint, [], C_out)
        ;   update_edges(C_in, Rhs, Ordered_Constraint, [], C_out)  
        )
    ), 
    write('\nCout: '), writeln(C_out), write('\n=======\n'), !.

% Definition of atomic constraint processing for inequality constraints.
% Same logic as in equality constraints.
constraint(Lhs\=Rhs, C_in, C_out) :-
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    order_constraint(Lhs\=Rhs, Ordered_Constraint),

    write('=======\n\n\= CONSTRAINT: '), writeln(Ordered_Constraint),
    write('\nCin: '), writeln(C_in),

    % Get the types
    %% (var(Lhs) 
    %% ->  read_type(Lhs, T1)
    %% ;   lookup_type(Lhs, T1)
    %% ),
    %% (var(Rhs) 
    %% ->  read_type(Rhs, T2)
    %% ;   lookup_type(Rhs, T2)
    %% ),
    %% nonvar(T1), nonvar(T2),  % Ensure that constraint occurs after the msw/3 is called
    %% T1 = T2,  % Type check

    (var(Lhs)
    ->
	type_check(Lhs, Rhs)
    ;
        type_check(Rhs, Lhs)
    ),

    % Update the edges
    (var(Lhs), var(Rhs), compare_roots(Lhs, Rhs, C)  /* If both are vars then we need to order them */
    ->  (C > 0  /* Rhs is smaller */
        -> update_edges(C_in, Lhs, Ordered_Constraint, [], C_out)
        ;   (C < 0 /* Lhs is smaller */
            ->  update_edges(C_in, Rhs, Ordered_Constraint, [], C_out)
            ;   fail
            )
        )
    ;   (var(Lhs)  /* One of Lhs and Rhs is a variable */
        ->  update_edges(C_in, Lhs, Ordered_Constraint, [], C_out)
        ;   update_edges(C_in, Rhs, Ordered_Constraint, [], C_out)
        )
    ), 
    write('\nCout: '), writeln(C_out), write('\n=======\n'), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OSDD construction definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
one(leaf(1)).
zero(leaf(0)).

% Represent trees as tree(Root,[(Edge1, Subtree1), (Edge2, Subtree2), ...])
%% make_tree(Root, Edges, Subtrees, tree(Root, L)) :-
%%     myzip(Edges, Subtrees, L).

%% myzip([], [], []).
%% myzip([E|ER], [T|TR], [edge_subtree(E,T)|R]) :-
%%     myzip(ER, TR, R).

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
or(Oh1, Oh2, Oh) :- writeln('OR'),
    bin_op(or, Oh1, Oh2, [], Oh).

% bin_op(+Operation, +OSDD1, +OSDD2, -OSDD_Out):
bin_op(Op, leaf(1), Oh2, Ctxt, Oh) :- !, bin_op1(Op, Oh2, Ctxt, Oh).
bin_op(Op, leaf(0), Oh2, Ctxt, Oh) :- !, bin_op0(Op, Oh2, Ctxt, Oh).
bin_op(Op, Oh1, leaf(1), Ctxt, Oh) :- !, bin_op1(Op, Oh1, Ctxt, Oh).
bin_op(Op, Oh1, leaf(0), Ctxt, Oh) :- !, bin_op0(Op, Oh1, Ctxt, Oh).

bin_op(Op, Oh1, Oh2, Ctxt, Oh) :-
    Oh1 = tree(R1, E1s), Oh2 = tree(R2, E2s),
    compare_roots(R1, R2, C),
    write('    OSDD1: '), writeln(Oh1), write('    OSDD2: '), writeln(Oh2),
    (C < 0  /* R1 is smaller */
    -> apply_binop(Op, E1s, Oh2, Ctxt, Es), make_osdd(R1, Es, Oh)
    ;   (C > 0 /* R2 is smaller */
        ->  apply_binop(Op, E2s, Oh1, Ctxt, Es), make_osdd(R2, Es, Oh)
        ;   /* R1=R2 */ R1 = R2, apply_all_binop(Op, E1s, E2s, Ctxt, Es), make_osdd(R1, Es, Oh)
        )
    ),
    write('    RESULT: '), writeln(Oh).

bin_op1(and, Oh1, Ctxt, Oh) :- apply_context(Oh1, Ctxt, Oh).
bin_op1(or, _, _Ctxt, leaf(1)).
bin_op0(or, Oh1, Ctxt, Oh) :- apply_context(Oh1, Ctxt, Oh).
bin_op0(and, _, _Ctxt, leaf(0)).

% Do binop with all trees in list (arg 2) and the other given tree (arg 3)
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

% Do binop, pairwise, for all trees in the two lists (arg 2, and arg 3)
apply_all_binop(Op, E1s, E2s, Ctxt, Es) :- apply_all_binop(Op, E1s, E2s, Ctxt, [], Es).

:- index apply_all_binop/6-3.
apply_all_binop(_Op, _E1s, [], _Ctxt, Es, Es).
apply_all_binop(Op, E1s, [edge_subtree(C2,Oh2)|E2s], Ctxt, Eis, Eos) :-
    (conjunction(C2, Ctxt, Ctxt1)
    ->  apply_1_binop(Op, E1s, C2, Oh2, Ctxt1, Eis, Ets)
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

% Apply context constraints to prune inconsistent edges
apply_context(leaf(X), _, leaf(X)).
apply_context(tree(R, E1s), Ctxt, Oh2) :-
    writeln('...Applying context...'),
    apply_context_edges(E1s, Ctxt, E2s),
    (E2s = []
    ->  Oh2 = leaf(0)
    ;   Oh2 = tree(R, E2s)
    ).

apply_context_edges([], _Ctxt, []).
apply_context_edges([edge_subtree(C,T)|E1s], Ctxt, E2s) :-
    writeln('...Applying context to edges...'),
    (conjunction(C, Ctxt, Ctxt1)
    ->  apply_context(T, Ctxt1, T1),
        E2s = [edge_subtree(C,T1)|Eos]
    ;   E2s = Eos
    ),
    apply_context_edges(E1s, Ctxt, Eos). 

% Splits OSDDs which have late constraints
/*split_if_needed(Oh1, Oh2) :-
    writeln('...Split if needed...'),
    (identify_late_constraint(Oh1, C)
    ->  writeln('-----------LATE-----------\n'),
        split(Oh1, C, Oh3),
        split_if_needed(Oh3, Oh2)
    ;   Oh2 = Oh1
    ).*/

split_if_needed(X,X).

split(Oh1, C, Oh2) :-
    split(Oh1, C, [], Oh2).

split(leaf(X), _C, _Ctxt, leaf(X)).

/*split(tree(R, E1s), C, Ctxt, tree(R, E2s)) :-
    (testable_at(R, C)
    ->  
    write('---\nConstraint: '), writeln(C),
    write('\nTree: '), writeln(tree(R, E1s)), write('---\n'),
        complement_atom(C, NC),
        (conjunction([C], Ctxt, Ctxt1)
        ->  apply_context_edges(E1s, Ctxt1, E11s)
        ;   E11s = []
        ),
        (conjunction([NC], Ctxt, Ctxt2)
        ->  apply_context_edges(E1s, Ctxt2, E12s)
        ;   E12s = []
        ),
        write('\n~~~~~~~~~~\nE11s IS: '), writeln(E11s), write('\n~~~~~~~~~~~\n'),
        write('\n~~~~~~~~~~\nE12s IS: '), writeln(E12s), write('\n~~~~~~~~~~~\n'),
        basics:append(E11s, E12s, E2m),
        write('\n~~~~~~~~~~\nE2M IS: '), writeln(E2m), write('\n~~~~~~~~~~~\n'),
        order_edges(E2m, E2s)
    ;   split_all(E1s, C, Ctxt, E2s)
    ).*/

split(tree(R, E1s), C, Ctxt, tree(R, Es_out)) :-
    (testable_at(R, C)
    ->  update_edges(tree(R, E1s), R, C, [], tree(R, E2s)),
        order_edges(E2s, Es_out)
    ;   split_all(E1s, C, Ctxt, Es_out)
    ).

split_all([], _, _, []).
split_all([edge_subtree(C1,T1)|Es], C, Ctxt, E2s) :-
    (conjunction(C1, Ctxt, Ctxt1)
    ->  split(T1, C, Ctxt1, T2),
        E2s = [edge_subtree(C1, T2)|Eos]
    ;   E2s = Eos
    ),
    split_all(Es, C, Ctxt, Eos).

% Uses context and implicit constraints to determine if there is a
% "late constraint" which is an implicit constraint which violates urgency
identify_late_constraint(Oh, C) :- identify_late_constraint(Oh, [], C).
identify_late_constraint(tree(R, Es), Ctxt, C) :-
    identify_late_constraint(Es, R, Ctxt, C).
identify_late_constraint([edge_subtree(C1,_T1)|_Es], R, Ctxt, C) :-
    listutil:absmerge(C1, Ctxt, Total_Constraints),
    get_implicit_constraints(C1, C2),
    member(C, C2),  % iterate through all constraints in C1
    not listutil:absmember(C, Total_Constraints),
    not_at(R, C), !.
identify_late_constraint([edge_subtree(C1,T1)|_Es], _R, Ctxt, C) :-
    conjunction(C1, Ctxt, Ctxt1),
    identify_late_constraint(T1, Ctxt1, C), !.
identify_late_constraint([_|Es], R, Ctxt, C) :-
    identify_late_constraint(Es, R, Ctxt, C).

not_at(R, C) :- not testable_at(R, C).

testable_at(R, _X=Y) :- R == Y.
testable_at(R, _X\=Y) :- R == Y.

% order_edges(E1s, E2s): E2s contains all edges in E1s, but ordered in
% a canonical way
order_edges(ETin, ETout) :-
    empty_assoc(Ain),
    % create a list containing canonical constraints and also insert
    % them into association list
    fill_assoc(ETin, Ain, [], Aout, Lout),
    % sort the canonical constraints
    sort(Lout, Lsort),
    % return the edge_subtrees in the corresponding order
    sorted_edgesubtrees(Lsort, Aout, ETout),
    true.

% fill_assoc(EdgeTreeList, AssocIn, ListIn, AssocOut, ListOut)
% Iterate over 'EdgeTreeList', add canonical form of constraint to
% ListIn, also add key-value pair of canonical constraint and
% Edge-Subtree term in AssocIn
fill_assoc([], A, L, A, L).
fill_assoc([edge_subtree(E, T)|R], Ain, Lin, Aout, Lout) :-
    canonical_form(E, C),
    put_assoc(C, Ain, edge_subtree(E, T), Atmp),
    basics:append(Lin, [C], Ltmp),
    fill_assoc(R, Atmp, Ltmp, Aout, Lout).

sorted_edgesubtrees([], _, []).
sorted_edgesubtrees([CC|CCR], A, [ET|ETR]) :-
    get_assoc(CC, A, ET),
    sorted_edgesubtrees(CCR, A, ETR).

% If X is a constant, leave T_in unchanged
update_edges(T_in, X, _C, _Ctxt, T_in) :- nonvar(X).

% Base case for edge recursion
update_edges([], _Y, _C, _Ctxt, []).

% If X is not the root, recurse on the edges of the tree
update_edges(tree(X, S1), Y, C, Ctxt, tree(X, S2)) :-
    X \== Y,
    update_edges(S1, Y, C, Ctxt, S2).

% Updates the subtrees in the edge list one at a time
update_edges([edge_subtree(Constraints, T) | R], X, C, Ctxt, [edge_subtree(Constraints, T1)| R1]) :-
    listutil:absmerge(Constraints, Ctxt, Ctxt1),
    update_edges(T, X, C, Ctxt1, T1),
    update_edges(R, X, C, Ctxt, R1).

% Handles logic for when X is the root of the tree
update_edges(tree(X, Edges), Y, C, Ctxt, tree(X, _UpdatedSubtrees)) :-
    X == Y,
    update_subtrees(Edges, C, [], Ctxt, UpdatedSubtrees),
    remove_empty_edge_subtrees(UpdatedSubtrees, _UpdatedSubtrees).

% Leaf nodes are left unchanged
update_edges(leaf(_X), Y, _C, _Ctxt, leaf(_X)) :- var(Y).

% Implements completeness by adding the complement of C to the previous constraints
update_subtrees([], C, Prev, Ctxt, [edge_subtree(Complement, leaf(0))]) :-
    complement_atom(C, _C),
    basics:append(Prev, [_C], Complement).

% Add C to the constraint list on an edge which does not have 0 child
update_subtrees([edge_subtree(C1, T)|Edges], C, Prev, Ctxt, [UpdatedSubtree | UpdatedEdges]) :-
    (T \== leaf(0)
    ->  basics:append(C1, [C], C2),
        % Check if the tree is satisfiable
        (listutil:absmerge(C2, Ctxt, Total_Constraints), 
            write('total constraints'), writeln(Total_Constraints), satisfiable(Total_Constraints)
        ->  true
        ;   fail
        ),
	    (satisfiable(C2)
        ->  basics:append(Prev, C1, Next),
            UpdatedSubtree = edge_subtree(C2, T)
        ;   UpdatedSubtree = []
        )
    ;   Next = Prev, C2 = C1, UpdatedSubtree = edge_subtree(C2, T)
    ),
    update_subtrees(Edges, C, Next, Ctxt, UpdatedEdges).

% Removes empty lists generated when an added constraint makes the total formula unsatisfiable
remove_empty_edge_subtrees([], []).
remove_empty_edge_subtrees([[]|Rest], Cleaned) :-
    remove_empty_edge_subtrees(Rest, Cleaned).

remove_empty_edge_subtrees([X|Rest], [X|Cleaned]) :-
    X \== [],
    remove_empty_edge_subtrees(Rest, Cleaned).

% Compares two root nodes based on switch/instance ID
compare_roots(R1, R2, 0) :-
    read_id(R1, id(S, I)),
    read_id(R2, id(S, I)).

compare_roots(R1, R2, -1) :-
    read_id(R1, id(S1, I1)),
    read_id(R2, id(S2, I2)),
    (I1 @< I2
    ->  true
    ;   (S1 @< S2
        ->  true
        ;   false
        )
    ).

compare_roots(R1, R2, 1) :-
    read_id(R1, id(S1, I1)),
    read_id(R2, id(S2, I2)),
    (I1 @> I2
    ->  true
    ;   (S1 @> S2
        ->  true
        ;   false
        )
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Change constraint formula representation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Constraint formulas are represented as constraint graphs. The
%% vertices of the constraint graph are made up of variables and
%% constants appearing in the constraint formula. There exists an
%% undirected edge between each pair of nodes involved in an atomic
%% constraint. However, to have canonical representation of each
%% constraint formula, nodes are not labeled by prolog variables, but
%% rather by canonical labels based on the 'id' attribute of the
%% prolog variables. Further we use the "ugraph" package to manipulate
%% these constraint graphs and use the "S-representation" as described
%% by the package. Since we have to distinguish between equality and
%% disequality atomic constraints, we maintain two S-representations
%% for each constraint formula: one for equality atomic constraints
%% and the other for disequality atomic constraints.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
s_representation(+Constraint_Formula, -EQ_List, -NEQ_List)
Constraint_Formula: Prolog term representing constraint formula
EQ_List: S-representation of equality constraints using canonical labels
NEQ_List: S-representation of disequality constraints using canonical labels
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
s_representation([], [], []).
s_representation([X=Y|R], [S-D, D-S| EQR], NE) :-
    canonical_label(X, S),
    canonical_label(Y, D),
    s_representation(R, EQR, NE).
s_representation([X\=Y|R], EQ, [S-D, D-S | NER]) :-
    canonical_label(X, S),
    canonical_label(Y, D),
    s_representation(R, EQ, NER).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
canonical_label(+Var/Const, -Canonical_Label)
Var/Const: Attributed variable or a "type" constant
Canonical_Label: Unique label for Var/Const
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
canonical_label(V, L) :-
    (var(V)
    ->
	read_id(V, id(S, I)),
	id_label(id(S, I), L)
    ;
        L = V
    ).

:- table id_label/2.
%:- index('$id_label'/2, [2,1]).
id_label(id(S, I), L) :-
    gensym(var, L),
    assert('$id_label'(id(S, I), L)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraint processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Combines two constraint lists by conjunction
conjunction(C1, C2, C) :-
    listutil:absmerge(C1, C2, C), 
    satisfiable(C).

% Complements a atomic constraint
complement_atom(X=Y, X\=Y).
complement_atom(X\=Y, X=Y).

% Syntactically reorders constraints
order_constraint(X=Y, A=B) :-
    var(X), var(Y), compare_roots(X, Y, C),
    (C < 0
    ->  A=X, B=Y
    ;   (C > 0
        ->  A=Y, B=X 
        ;   false  % A constraint must be between distinct variables
        )
    ).

order_constraint(X\=Y, A\=B) :-
    var(X), var(Y), compare_roots(X, Y, C),
    (C < 0
    ->  A=X, B=Y
    ;   (C > 0
        ->  A=Y, B=X 
        ;   false  % A constraint must be between distinct variables
        )
    ).

% Always order constants to the Rhs
order_constraint(X=Y, X=Y) :- var(X), nonvar(Y).
order_constraint(X=Y, Y=X) :- var(Y), nonvar(X).
order_constraint(X\=Y, X\=Y) :- var(X), nonvar(Y).
order_constraint(X\=Y, Y\=X) :- var(Y), nonvar(X).

%% %% check satisfiability of constraint formula
%% satisfiable([]) :- !.
%% satisfiable(C) :-
%%     copy_term(C, C1),
%%     getvars(C, [], L),
%%     getvars(C1, [], L1),
%%     assert_bounds(L, L1),
%%     assert_constraints(C1),
%%     label(L1), !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
satisfiable(+CF)
Is true if constraint formula CF is satisfiable
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
satisfiable(CF) :-
    s_representation(CF, EQ, NEQ),
    satisfiable_constraint_graph(EQ, NEQ).

% Gets the unique variables of a constraint list
getvars([], L, L).
getvars([X=Y|R], L, Lout) :-
    (var(X), \+ lists:memberchk_eq(X, L)
    ->
	    basics:append(L, [X], Ltmp)
    ;
        Ltmp = L
    ),
    (var(Y), \+ lists:memberchk_eq(Y, L)
    ->
	    basics:append(Ltmp, [Y], Ltmp1)
    ;
        Ltmp1 = Ltmp
    ),
    getvars(R, Ltmp1, Lout).

getvars([X\=Y|R], L, Lout) :-
    (var(X), \+ lists:memberchk_eq(X, L)
    ->
        basics:append(L, [X], Ltmp)
    ;
        Ltmp = L
    ),
    (var(Y), \+ lists:memberchk_eq(Y, L)
    ->
        basics:append(Ltmp, [Y], Ltmp1)
    ;
        Ltmp1 = Ltmp
    ),
    getvars(R, Ltmp1, Lout).

%% assert Lower..Upper bounds for each variable in second list by
%% looking at the corresponding id in first list.
assert_bounds([], []).
assert_bounds([V|R], [V1|R1]) :-
    read_id(V, id(S, _)), % get switch associated with V
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
    % term_variables(C, V),
    edge_list_form(C, EQ, NEQ),
    % use ugraphs to compute closure of equality edges
    complete_equality(EQ, EQC),
    discard_spurious_edges(EQC, EQC1),    
    % complete neq edges
    complete_disequality(EQC1, NEQ, NEQ1),
    % discard edges between constants
    discard_spurious_edges(NEQ1, NEQ2),
    % sort using ordsets to get canonical representation
    list_to_ord_set(EQC1, EQORD),
    list_to_ord_set(NEQ2, NEQORD),
    F = cg(EQORD, NEQORD),
    true.

%% complete a constraint formula with implicit constraints
%% CComp is the union of C and implicit constraints
get_implicit_constraints(C, CComp) :-
    getvars(C, [], Vars),
    id_var_pairs(Vars, Pairs),
    list_to_assoc(Pairs, A),
    canonical_form(C, cg(EQ, NEQ)),
    graph_to_formula(A, eq, EQ, [], C1),
    graph_to_formula(A, neq, NEQ, C1, CComp),
    true.

id_var_pairs([], []).
id_var_pairs([V|R], [Id-V|PR]) :-
    canonical_label(V, Id),
    id_var_pairs(R, PR).

graph_to_formula(Assoc, Op, [], C, C).
graph_to_formula(Assoc, Op, [ID1-ID2|R], Cin, Cout) :-
    % use only one of the edges in the constraint graph
    (ID1 @< ID2
    ->
        (functor(ID1, id, 2)
        ->
            get_assoc(ID1, Assoc, X)
        ;
            X = ID1
        ),
        (functor(ID2, id, 2)
        ->
            get_assoc(ID2, Assoc, Y)
        ;
            Y = ID2
        ),
        (Op = eq
        ->
            basics:append(Cin, [X=Y], Ctmp)
        ;   
            (Op = neq
            ->
                basics:append(Cin, [X\=Y], Ctmp)
            ;
                fail
            )
        ),
        graph_to_formula(Assoc, Op, R, Ctmp, Cout)
    ;
        graph_to_formula(Assoc, Op, R, Cin, Cout)
    ).

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
    read_id(X, id(S, I)).
canonical_label(X, X) :-
    nonvar(X).

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
    findall(X-Y, (member(X, L1), member(Y,L2)), L).

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

%% % Lookup type of a constant by searching for a type T which X is an element of.
%% lookup_type(X, T) :-
%%     nonvar(X),
%%     values(_, T),
%%     member(X, T), !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
type_check(+Term1, +Term2)
Is true if both Term1 and Term2 have the same type.
It is required that Term1 be a variable, Term2 can be a variable or const.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
type_check(Term1, Term2) :-
    % Ensure that constraint occurs after type has been set. Currently
    % read_type returns a variable for Type if its not been set
    read_type(Term1, Type),
    nonvar(Type), 
    (var(Term2)
    ->
	 read_type(Term2, Type)
    ;
    member(Term2, Type)
    ).

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
% Probability Computation for Tree OSDDs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

mytreeprob(leaf(X), X).

mytreeprob(tree(R, ETs), P) :-
    mytreeprob_1(R, ETs, 0, P).

mytreeprob_1(R, [], Pin, Pin).
mytreeprob_1(R, [edge_subtree(E, T)|Rest], Pin, Pout) :-
    % get solutions of R for constraint E
    findall(R, solution(R, E), SS),
    list_to_ord_set(SS, S),
    % at this point R is still not bound
    % compute probability for the edge 'E' without binding R
    copy_term(var_tree(R, T), Copy),
    Copy =.. [var_tree| [R1, T1]],
    edge_prob(var(R1, T1), S, 0, Pedge),
    Ptmp is Pin + Pedge,
    mytreeprob_1(R, Rest, Ptmp, Pout),
    true.

solution(R, E) :-
    read_id(R, id(S, _)),
    intrange(S, Lower, Upper),
    R in Lower..Upper,
    assert_constraints(E),
    label([R]).

edge_prob(var(R, T), [], Pin, Pin).
edge_prob(var(R, T), [V|VR], Pin, Pout) :-
    copy_term(var_tree(R, T), Copy),
    Copy =.. [var_tree| [R1, T1]],
    edge_prob_1(R1, V, T1, P),
    Ptmp is Pin + P,
    edge_prob(var(R, T), VR, Ptmp, Pout).

% edge probability under a particular value for output variable
edge_prob_1(R, V, T, P) :-
    read_id(R, id(S, _)),
    intrange(S, Lower, Upper),
    Index is V - Lower + 1,
    set_sw(S, Dist),
    lists:nth(Index, Dist, Pv),
    R = V,
    mytreeprob(T, Pt),
    P is Pv * Pt.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Misc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeDot(OSDD, File) :- writeDotFile(OSDD, File).
