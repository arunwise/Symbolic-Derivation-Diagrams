:- import append/3, member/2 from basics.
:- import prepare/1, gensym/2 from gensym.
:- import concat_atom/2 from string.
:- import is_empty/1 from lists.

:- import writeDotFile/2 from visualize.
:- import satisfiable_constraint_graph/2, solutions/4,
   canonical_constraint/3 from constraints.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
msw(+S, +I, X, +CtxtIn, OsddIn, -CtxtOut, OsddOut)

Update the CtxtIn with Id of random variable X. Compute OsddOut as
conjunction of OsddIn and trivial OSDD for msw(S,I,X).

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
msw(S, I, X, CtxtIn, OsddIn, CtxtOut, OsddOut) :-
    ground(S),
    ground(I),
    update_context(CtxtIn, X, S, I, CtxtOut),
    trivial_osdd(S, I, Osdd),
    and(OsddIn, Osdd, OsddOut).
    
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
constraint(+C, +CtxtIn, OsddIn, -CtxtIn, OsddOut)

Perform type checking of atomic constraint C and update the OsddIn to OsddOut
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
constraint(C, CtxtIn, OsddIn, CtxtIn, OsddOut) :-
    type_check(CtxtIn, C),
    apply_constraint(CtxtIn, OsddIn, C, [], [], CtxtIn, OsddOut).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
project_context(+CtxtIn, +FreeVars, -CtxtOut)

Project 'CtxtIn' on to FreeVars to get 'CtxtOut'
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
project_context(CtxtIn, FreeVars, CtxtOut) :-
    project_context_1(CtxtIn, FreeVars, [], CtxtOut).

project_context_1(_Ctxt, [], CtxtOut, CtxtOut).
project_context_1(Ctxt, [H| T], CtxtIn, CtxtOut) :-
    (existing_context(Ctxt, H, S, I)
    ->
	append(CtxtIn, [H-(S, I)], CtxtTmp)
    ;
        CtxtTmp = CtxtIn
    ),
    project_context_1(Ctxt, T, CtxtTmp, CtxtOut).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
apply_constraint(+CtxtIn, NodeIn, +Constraint, +OutVars, +PathConstr, 
                 -CtxtIn, NodeOut)

Given a node 'NodeIn', whose path to root contains output variables
'OutVars' and the path constraints are 'PathConstr', apply the atomic
constraint 'Constraint' to the subtree rooted at 'NodeIn' and return
the new node 'NodeOut'.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
apply_constraint(CtxtIn, NodeIn, C, OutVars, PathConstr, CtxtIn, NodeOut) :-
    ('$unique_table'(NodeIn, 0)
    ->
	% NodeIn represents a 0 leaf, nothing to apply.
	NodeOut = NodeIn
    ;
        ('$unique_table'(NodeIn, 1)
	->
	    % NodeIn represents a 1 leaf, nothing to apply.
	    NodeOut = NodeIn
	;
	    '$unique_table'(NodeIn, tree(Root, EdgeSubTrees)),
	    append(OutVars, [Root], OutVars1),
	    labeled_form(CtxtIn, C, LC),
	    (urgency_satisfied(OutVars1, LC)
	    ->
		% apply constraints here
		apply_constraint_urg(EdgeSubTrees, LC, PathConstr,
				     EdgeSubTrees1),
		negate_atomic(LC, LCN),
		make_node(0, Z),
		append(EdgeSubTrees1, [edge_subtree([LCN], Z)],
		       EdgeSubTreesOut)
	    ;
                apply_constraint_no_urg(CtxtIn, EdgeSubTrees, LC, OutVars1,
				 PathConstr, EdgeSubTreesOut)
	    ),
	    canonical_form_et(EdgeSubTreesOut, CF),
	    canonical_form(tree(Root, CF), CT),
	    make_node(CT, NodeOut)
	)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
urgency_satisfied(+Vars, +Constraint)

Is true when all the variables involved in 'Constraint' are elements
of 'Vars' ('Vars' contains the labels instead of actual variable,
similarly 'Constraint' is also represented in terms of canonical
labels).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
urgency_satisfied(Vars, Lhs=Rhs) :-
    (integer(Lhs)
    ->
	% Lhs is a constant
	true
    ;
	member(Lhs, Vars)
    ),
    (integer(Rhs)
    ->
	% Rhs is a constant
	true
    ;
        member(Rhs, Vars)
    ).

urgency_satisfied(Vars, Lhs\=Rhs) :-
    (integer(Lhs)
    ->
	% Lhs is a constant
	true
    ;
	member(Lhs, Vars)
    ),
    (integer(Rhs)
    ->
	% Rhs is a constant
	true
    ;
        member(Rhs, Vars)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
apply_constraint_no_urg(+CtxtIn, +EdgeSubtrees, +Constraint, +OutVars, 
                                          +PathConstr, -EdgeSubTreesOut)

Given a list of edge/subtree pairs, whose root has 'OutVars' as the
set of output variables on the path to the root and whose path
constraints are 'PathConstr', apply the atomic constraint 'Constraint'
to each of the subtrees and return the new list of edge/subtree pairs.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
apply_constraint_no_urg(_Ctxt, [], _C, _O, _P, []).
apply_constraint_no_urg(Ctxt, [edge_subtree(E, T)| Rest], C, OutVars,
		   PathConstr, [edge_subtree(E, TOut)| RestOut]) :-
    append(PathConstr, E, PathConstr1),
    apply_constraint(Ctxt-T, C, OutVars, PathConstr1, Ctxt-TOut),
    apply_constraint_no_urg(Ctxt, Rest, C, OutVars, PathConstr, RestOut).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
apply_constraint_urg(+EdgeSubtrees, +Constraint, +PathConstr,
                                               -EdgeSubtreesOut)

Given a list of edge/subtree pairs, whose root has 'PathConstr'
labeling the path to the root, apply 'Constraint' to each of the edges
and return the new list of edge/subtree pairs.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
apply_constraint_urg([], _C, _P, []).
apply_constraint_urg([edge_subtree(E, T)| Rest], C, PathConstr,
		   [edge_subtree(EOut, TOut)| RestOut]) :-
    append(PathConstr, E, PathConstr1),
    append(PathConstr1, [C], PathConstr2),
    (satisfiable(PathConstr2)
    ->
	TOut = T
    ;
        make_node(0, TOut)
    ),
    append(E, [C], EOut),
    apply_constraint_urg(Rest, C, PathConstr, RestOut).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
update_context(+CtxtIn, +X, +S, +I, -CtxtOut)

Check if 'CtxtIn' specifies the switch/instance pair of the variable
X. If so, it should match the pair (S, I). Otherwise, add the
switch/instance pair of X as (S, I) to CtxtIn to produce CtxtOut.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
update_context(CtxtIn, X, S, I, CtxtOut) :-
    (existing_context(CtxtIn, X, S1, I1)
    ->
	S = S1,
	I = I1,
	CtxtOut = CtxtIn
    ;
        append(CtxtIn, [X-(S, I)], CtxtOut)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
existing_context(+CtxtIn, +X, -S, -I)

Check 'CtxtIn' for the switch/instance pair of X.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
existing_context([X1-(S1, I1) | Rest], X, S, I) :-
    (X == X1
    ->
	S = S1,
	I = I1
    ;
        existing_context(Rest, X, S, I)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
trivial_osdd(+S, +I, -Osdd)

Construct the trivial osdd corresponding to msw/3 predicate. The root
of this OSDD is a canonical label that corresponds to the pair (S,
I). There is a single edge labeled by empty constraint connected to a
1 leaf.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
trivial_osdd(S, I, Osdd) :-
    make_node(1, One),
    canonical_label(S, I, Label),
    make_node(tree(Label, [edge_subtree([], One)]), Osdd).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
make_node(+Subtree, -Node)

Add an entry to the unique_table for the tree 'SubTree' if it doesn't
already exist.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
:- table make_node/2.
make_node(SubTree, Node) :-
    gensym(node, Node),
    assert('$unique_table'(Node, SubTree)).

:- dynamic '$unique_table'/2.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
canonical_label(+S, +I, -L)

Construct a canonical label for switch 'S' and instance 'I' as the atom
'var_S_I'
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
:- table canonical_label/3.
canonical_label(S, I, L) :-
    ground(S), ground(I),
    concat_atom([var,'_',S,'_',I], L).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
type_check(+Ctxt, +Constraint)

Is true if Constraint is type consistent with respect to context.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
type_check(Ctxt, Lhs=Rhs) :-
    (var(Lhs); var(Rhs)), !, % atleast one of Lhs, Rhs should be a variable
    (var(Lhs)
    ->
	type_check(Ctxt, Lhs, Rhs)
    ;
        type_check(Ctxt, Rhs, Lhs)
    ).

type_check(Ctxt, Lhs\=Rhs) :-
    (var(Lhs); var(Rhs)), !, % atleast one of Lhs, Rhs should be a variable
    (var(Lhs)
    ->
	type_check(Ctxt, Lhs, Rhs)
    ;
        type_check(Ctxt, Rhs, Lhs)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
type_check(+Ctxt, +Term1, +Term2)
Is true if both Term1 and Term2 have the same type.
It is required that Term1 be a variable, Term2 can be a variable or const.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
type_check(Ctxt, Term1, Term2) :-
    (var(Term1)
    ->
	find_type(Ctxt, Term1, Type)
    ;
        writeln('First argument to type_check/3 is not a variable'),
        fail
    ),
    (var(Term2)
    ->
	find_type(Ctxt, Term2, Type)
    ;
        member(Term2, Type)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
find_type(+Ctxt, +Var, -Type)

Find the type of 'Var' by using the switch specified by 'Ctxt'
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
find_type([X-(S, _I)| _Rest], Term, Type) :-
    X == Term, !,
    values(S, Type).
find_type([X-(_S, _I)|Rest], Term, Type) :-
    X \== Term,
    find_type(Rest, Term, Type).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
labeled_form(+Ctxt, +Atomic_Constraint, -Labeled_Atomic_Constraint)

Given an atomic constraint in terms of logical variables, return its 
representation in terms of canonical labels.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
labeled_form(Ctxt, Lhs=Rhs, LLhs=LRhs) :-
    (var(Lhs)
    ->
	existing_context(Ctxt, Lhs, SL, IL),
	canonical_label(SL, IL, LLhs)
    ;
        LLhs=Lhs
    ),
    (var(Rhs)
    ->
	existing_context(Ctxt, Rhs, SR, IR),
	canonical_label(SR, IR, LRhs)
    ;
        LRhs = Rhs
    ).
labeled_form(Ctxt, Lhs\=Rhs, LLhs\=LRhs) :-
    (var(Lhs)
    ->
	existing_context(Ctxt, Lhs, SL, IL),
	canonical_label(SL, IL, LLhs)
    ;
        LLhs = Lhs
    ),
    (var(Rhs)
    ->
	existing_context(Ctxt, Rhs, SR, IR),
	canonical_label(SR, IR, LRhs)
    ;
        LRhs = Rhs
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
negate_atomic(+C, -N)

N is the negation of the atomic constraint C
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
negate_atomic(X=Y, X\=Y).
negate_atomic(X\=Y, X=Y).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
satisfiable(+CF)

Is true if constraint formula CF is satisfiable. CF is represented in
terms of canonical labels.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
satisfiable(CF) :-
    ve_representation(CF, EQ, NEQ),
    satisfiable_constraint_graph(EQ, NEQ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
ve_representation(+Constraint_Formula, -EQ_List, -NEQ_List)

Constraint_Formula: Constraint_Formula represented using canonical
labels

EQ_List: Vertices/Edges representation of equality constraints using
canonical labels

NEQ_List: Vertices/Edges representation of disequality constraints
using canonical labels
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
ve_representation([], [], []).
ve_representation([X=Y|R], [X-Y, Y-X| EQR], NE) :-
    ve_representation(R, EQR, NE).
ve_representation([X\=Y|R], EQ, [X-Y, Y-X | NER]) :-
    ve_representation(R, EQ, NER).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
canonical_form(+Tree, +CanonicalForm)

Convert OSDD tree nodes into a canonical form. We assume that
edge/subtree pairs are already in canonical form.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
canonical_form(0, 0).
canonical_form(1, 1).
canonical_form(tree(Root, ET), T) :-
    % assume that ET is already in canonical form
    (is_empty(ET)
    ->
	T = 0
    ;
        T = tree(Root, ET)
    ).

canonical_form_et(ETIn, ETOut) :-
    is_list(ETIn),
    canonical_form_et_1(ETIn, ET),
    sort(ET, ETOut).

canonical_form_et_1([], []).
canonical_form_et_1([edge_subtree(E, T) | Rest],
		    [edge_subtree(CE, T) | RestC]) :-
    ve_representation(E, EQ, NEQ),
    canonical_constraint(EQ, NEQ, cg(EQ1, NEQ1)),
    append(EQ1, NEQ1, CE1),
    sort(CE1, CE),
    canonical_form_et_1(Rest, RestC).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
and(+Osdd1, +Osdd2, -Osdd)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
and(Osdd1, Osdd2, Osdd) :-
    binop(and, Osdd1, Osdd2, [], Osdd).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
or_ctxt_osdd(+Ctxt1-Osdd1, +Ctxt2-Osdd2, -Ctxt1-Osdd)

Combine context-osdd pairs, by taking one of the contexts (since they
are supposed to be identical) and disjunction of Osdd1 and Osdd2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
or_ctxt_osdd(Ctxt1-Osdd1, Ctxt2-Osdd2, Ctxt1-Osdd) :-
    or(Osdd1, Osdd2, Osdd).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
or(+Osdd1, +Osdd2, -Osdd)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
or(Osdd1, Osdd2, Osdd) :-
    binop(or, Osdd1, Osdd2, [], Osdd).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
binop(+OP, +Osdd1, +Osdd2, +PathConstr, -Osdd)

Apply binary operation 'OP' on Osdd1 and Osdd2 under the path
constraint 'PathConstr' to produce 'Osdd'.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
binop(Op, Osdd1, Osdd2, PathConstr, Osdd) :-
    '$unique_table'(Osdd1, 0), !,
    binop_0(Op, Osdd2, PathConstr, Osdd).
binop(Op, Osdd1, Osdd2, PathConstr, Osdd) :-
    '$unique_table'(Osdd2, 0), !,
    binop_0(Op, Osdd1, PathConstr, Osdd).
binop(Op, Osdd1, Osdd2, PathConstr, Osdd) :-
    '$unique_table'(Osdd1, 1), !,
    binop_1(Op, Osdd2, PathConstr, Osdd).
binop(Op, Osdd1, Osdd2, PathConstr, Osdd) :-
    '$unique_table'(Osdd2, 1), !,
    binop_1(Op, Osdd1, PathConstr, Osdd).

binop(Op, Osdd1, Osdd2, PathConstr, Osdd) :-
    '$unique_table'(Osdd1, tree(Root1, ET1)),
    '$unique_table'(Osdd2, tree(Root2, ET2)),
    (Root1 == Root2
    ->
	binop_pairwise(Op, ET1, ET2, PathConstr, [], ET),
	canonical_form_et(ET, CF),
	canonical_form(tree(Root1, CF), CT),
	make_node(CT, Osdd)
    ;
        (Root1 @< Root2
	->
	    binop_edges(Op, ET1, Osdd2, PathConstr, ET),
	    canonical_form_et(ET, CF),
	    canonical_form(tree(Root1, CF), CT),
	    make_node(CT, Osdd)
	;
	    binop_edges(Op, ET2, Osdd1, PathConstr, ET),
	    canonical_form_et(ET, CF),
	    canonical_form(tree(Root2, CF), CT),
	    make_node(CT, Osdd)
	)
    ).

% assume that PathConstr are satisfiable
binop_0(and, _Osdd1, _PathConstr, Osdd) :-
    make_node(0, Osdd).
binop_1(and, Osdd1, PathConstr, Osdd) :-
    check_constraints(PathConstr, Osdd1, Osdd).
binop_0(or, Osdd1, PathConstr, Osdd) :-
    check_constraints(PathConstr, Osdd1, Osdd).
binop_1(or, _Osdd1, _PathConstr, Osdd) :-
    make_node(1, Osdd).

binop_pairiwse(_Op, [], _ET2, _P, ETin, ETin).
binop_pairwise(Op, [edge_subtree(E1, T1)|Rest1],
	       ET2, PathConstr, ETin, ETout) :-
    binop_pairwise_1(Op, E1, T1, ET2, PathConstr, ETin, ETtmp),
    binop_pairwise(Op, Rest1, ET2, PathConstr, ETtmp, ETout).

binop_pairwise_1(_Op, _E1, _T1, [], _PathConstr, ETin, ETin).
binop_pairwise_1(Op, E1, T1, [edge_subtree(E2, T2)|Rest],
		 PathConstr, ETin, ETout) :-
    append(PathConstr, E1, PathConstr1),
    append(PathConstr1, E2, PathConstr2),
    append(E1, E2, E),
    (satisfiable(PathConstr2)
    ->
	binop(Op, T1, T2, PathConstr2, T),
	append(ETin, [edge_subtree(E, T)], ETtmp)
    ;
        make_node(0, T),
        append(ETin, [edge_subtree(E, T)], ETtmp)
    ),
    binop_pairwise_1(Op, E1, T1, Rest, PathConstr, ETtmp, ETout).

binop_edges(_Op, [], _Osdd, _P, []).
binop_edges(Op, [edge_subtree(E, T)|Rest], Osdd, PathConstr,
	    [edge_subtree(E, T1)|Rest1]) :-
    append(PathConstr, E, PathConstr1),
    (satisfiable(PathConstr1)
    ->
	binop(Op, T, Osdd, PathConstr1, T1)
    ;
        make_node(0, T1)
    ),
    binop_edges(Op, Rest, Osdd, PathConstr, Rest1).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
check_constraints(+PathConstr, +OsddIn, -OsddOut)

Prunes any edges which are not satisfiable under 'PathConstr'.
We assume that 'PathConstr' itself is satisfiable.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
check_constraints(_PathConstr, OsddIn, OsddOut) :-
    '$unique_table'(OsddIn, 1), !,
    OsddOut = OsddIn.
check_constraints(_PathConstr, OsddIn, OsddOut) :-
    '$unique_table'(OsddIn, 0), !,
    OsddOut = OsddIn.
check_constraints(PathConstr, OsddIn, OsddOut) :-
    '$unique_table'(OsddIn, tree(Root, ET)), !,
    check_constraints_1(PathConstr, ET, [], ET1),
    canonical_form_et(ET1, CF),
    canonical_form(tree(Root, CF), CT),
    make_node(CT, OsddOut).

check_constraints_1(_P, [], ETin, ETin).
check_constraints_1(PathConstr, [edge_subtree(E, T)|Rest], ETin, ETout) :-
    append(PathConstr, E, PathConstr1),
    (satisfiable(PathConstr1)
    ->
	check_constraints(PathConstr1, T, T1),
	append(ETin, [edge_subtree(E, T1)], ETtmp)
    ;
        ETtmp = ETin
    ),
    check_constraints_1(PathConstr, Rest, ETtmp, ETout).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
split_if_needed(+OsddIn, -OsddOut)

To be implemented.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
split_if_needed(X,X).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % OSDD construction definitions
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% one(leaf(1)).
%% zero(leaf(0)).

%% % Returns a consistent OSDD
%% make_osdd(R, Eis, Oh) :-
%%     (Eis = []
%%     ->  Oh = leaf(0)
%%     ;   order_edges(Eis, Eos),
%%         Oh = tree(R, Eos)
%%     ).

%% % and_osdd(+OSDD_handle1, +OSDD_handle2, -OSDD_handle):
%% and(Oh1, Oh2, Oh) :-
%%     bin_op(and, Oh1, Oh2, [], Oh).

%% % or_osdd(+OSDD_handle1, +OSDD_handle2, -OSDD_handle):
%% or(Oh1, Oh2, Oh) :- writeln('OR'),
%%     bin_op(or, Oh1, Oh2, [], Oh).

%% % bin_op(+Operation, +OSDD1, +OSDD2, -OSDD_Out):
%% bin_op(Op, leaf(1), Oh2, Ctxt, Oh) :- !, bin_op1(Op, Oh2, Ctxt, Oh).
%% bin_op(Op, leaf(0), Oh2, Ctxt, Oh) :- !, bin_op0(Op, Oh2, Ctxt, Oh).
%% bin_op(Op, Oh1, leaf(1), Ctxt, Oh) :- !, bin_op1(Op, Oh1, Ctxt, Oh).
%% bin_op(Op, Oh1, leaf(0), Ctxt, Oh) :- !, bin_op0(Op, Oh1, Ctxt, Oh).

%% bin_op(Op, Oh1, Oh2, Ctxt, Oh) :-
%%     Oh1 = tree(R1, E1s), Oh2 = tree(R2, E2s),
%%     compare_roots(R1, R2, C),
%%     write('    OSDD1: '), writeln(Oh1), write('    OSDD2: '), writeln(Oh2),
%%     (C < 0  /* R1 is smaller */
%%     -> apply_binop(Op, E1s, Oh2, Ctxt, Es), make_osdd(R1, Es, Oh)
%%     ;   (C > 0 /* R2 is smaller */
%%         ->  apply_binop(Op, E2s, Oh1, Ctxt, Es), make_osdd(R2, Es, Oh)
%%         ;   /* R1=R2 */ R1 = R2, apply_all_binop(Op, E1s, E2s, Ctxt, Es), make_osdd(R1, Es, Oh)
%%         )
%%     ),
%%     write('    RESULT: '), writeln(Oh).

%% bin_op1(and, Oh1, Ctxt, Oh) :- apply_context(Oh1, Ctxt, Oh).
%% bin_op1(or, _, _Ctxt, leaf(1)).
%% bin_op0(or, Oh1, Ctxt, Oh) :- apply_context(Oh1, Ctxt, Oh).
%% bin_op0(and, _, _Ctxt, leaf(0)).

%% % Do binop with all trees in list (arg 2) and the other given tree (arg 3)
%% :- index apply_binop/5-2.
%% apply_binop(_Op, [], _Oh2, _Ctxt, []).
%% apply_binop(Op, [edge_subtree(C,Oh1)|E1s], Oh2, Ctxt, Edges) :-
%%     (constraints_conjunction(C, Ctxt, Ctxt1)
%%     ->  bin_op(Op, Oh1, Oh2, Ctxt1, Oh),
%%         Edges = [edge_subtree(C,Oh)|Es],
%%         apply_binop(Op, E1s, Oh2, Ctxt, Es)
%%     ;   % inconsistent, drop this edge:
%%         apply_binop(Op, E1s, Oh2, Ctxt, Edges)
%%     ).

%% % Do binop, pairwise, for all trees in the two lists (arg 2, and arg 3)
%% apply_all_binop(Op, E1s, E2s, Ctxt, Es) :- apply_all_binop(Op, E1s, E2s, Ctxt, [], Es).

%% :- index apply_all_binop/6-3.
%% apply_all_binop(_Op, _E1s, [], _Ctxt, Es, Es).
%% apply_all_binop(Op, E1s, [edge_subtree(C2,Oh2)|E2s], Ctxt, Eis, Eos) :-
%%     (constraints_conjunction(C2, Ctxt, Ctxt1)
%%     ->  apply_1_binop(Op, E1s, C2, Oh2, Ctxt1, Eis, Ets)
%%     ;   Eis = Ets  % C2's constraint is inconsistent wrt Ctxt, so drop these edges
%%     ),
%%     apply_all_binop(Op, E1s, E2s, Ctxt, Ets, Eos).

%% apply_1_binop(_Op, [], _C2, _Oh2, _Ctxt, Es, Es).
%% apply_1_binop(Op, [edge_subtree(C1,Oh1)|E1s], C2, Oh2, Ctxt, Eis, Eos) :-
%%     (constraints_conjunction(C1, C2, C), constraints_conjunction(C, Ctxt, Ctxt1)
%%     ->  bin_op(Op, Oh1, Oh2, Ctxt1, Oh),
%%         Eos = [edge_subtree(C, Oh)|Ets]
%%     ;   Eos = Ets
%%     ),
%%     apply_1_binop(Op, E1s, C2, Oh2, Ctxt, Eis, Ets).

%% % Apply context constraints to prune inconsistent edges
%% apply_context(leaf(X), _, leaf(X)).
%% apply_context(tree(R, E1s), Ctxt, Oh2) :-
%%     writeln('...Applying context...'),
%%     apply_context_edges(E1s, Ctxt, E2s),
%%     (E2s = []
%%     ->  Oh2 = leaf(0)
%%     ;   Oh2 = tree(R, E2s)
%%     ).

%% apply_context_edges([], _Ctxt, []).
%% apply_context_edges([edge_subtree(C,T)|E1s], Ctxt, E2s) :-
%%     writeln('...Applying context to edges...'),
%%     (constraints_conjunction(C, Ctxt, Ctxt1)
%%     ->  apply_context(T, Ctxt1, T1),
%%         E2s = [edge_subtree(C,T1)|Eos]
%%     ;   E2s = Eos
%%     ),
%%     apply_context_edges(E1s, Ctxt, Eos). 

%% % Splits OSDDs which have late constraints
%% /*split_if_needed(Oh1, Oh2) :-
%%     writeln('...Split if needed...'),
%%     (identify_late_constraint(Oh1, C)
%%     ->  writeln('-----------LATE-----------\n'),
%%         split(Oh1, C, Oh3),
%%         split_if_needed(Oh3, Oh2)
%%     ;   Oh2 = Oh1
%%     ).*/

%% split_if_needed(X,X).

%% split(Oh1, C, Oh2) :-
%%     split(Oh1, C, [], Oh2).

%% split(leaf(X), _C, _Ctxt, leaf(X)).

%% /*split(tree(R, E1s), C, Ctxt, tree(R, E2s)) :-
%%     (testable_at(R, C)
%%     ->  
%%     write('---\nConstraint: '), writeln(C),
%%     write('\nTree: '), writeln(tree(R, E1s)), write('---\n'),
%%         complement_atom(C, NC),
%%         (constraints_conjunction([C], Ctxt, Ctxt1)
%%         ->  apply_context_edges(E1s, Ctxt1, E11s)
%%         ;   E11s = []
%%         ),
%%         (constraints_conjunction([NC], Ctxt, Ctxt2)
%%         ->  apply_context_edges(E1s, Ctxt2, E12s)
%%         ;   E12s = []
%%         ),
%%         write('\n~~~~~~~~~~\nE11s IS: '), writeln(E11s), write('\n~~~~~~~~~~~\n'),
%%         write('\n~~~~~~~~~~\nE12s IS: '), writeln(E12s), write('\n~~~~~~~~~~~\n'),
%%         basics:append(E11s, E12s, E2m),
%%         write('\n~~~~~~~~~~\nE2M IS: '), writeln(E2m), write('\n~~~~~~~~~~~\n'),
%%         order_edges(E2m, E2s)
%%     ;   split_all(E1s, C, Ctxt, E2s)
%%     ).*/

%% split(tree(R, E1s), C, Ctxt, tree(R, Es_out)) :-
%%     (testable_at(R, C)
%%     ->  update_edges(tree(R, E1s), R, C, [], tree(R, E2s)),
%%         order_edges(E2s, Es_out)
%%     ;   split_all(E1s, C, Ctxt, Es_out)
%%     ).

%% split_all([], _, _, []).
%% split_all([edge_subtree(C1,T1)|Es], C, Ctxt, E2s) :-
%%     (constraints_conjunction(C1, Ctxt, Ctxt1)
%%     ->  split(T1, C, Ctxt1, T2),
%%         E2s = [edge_subtree(C1, T2)|Eos]
%%     ;   E2s = Eos
%%     ),
%%     split_all(Es, C, Ctxt, Eos).

%% % Uses context and implicit constraints to determine if there is a
%% % "late constraint" which is an implicit constraint which violates urgency
%% identify_late_constraint(Oh, C) :- identify_late_constraint(Oh, [], C).
%% identify_late_constraint(tree(R, Es), Ctxt, C) :-
%%     identify_late_constraint(Es, R, Ctxt, C).
%% identify_late_constraint([edge_subtree(C1,_T1)|_Es], R, Ctxt, C) :-
%%     absmerge(C1, Ctxt, Total_Constraints),
%%     get_implicit_constraints(C1, C2),
%%     member(C, C2),  % iterate through all constraints in C1
%%     not listutil:absmember(C, Total_Constraints),
%%     not_at(R, C), !.
%% identify_late_constraint([edge_subtree(C1,T1)|_Es], _R, Ctxt, C) :-
%%     constraints_conjunction(C1, Ctxt, Ctxt1),
%%     identify_late_constraint(T1, Ctxt1, C), !.
%% identify_late_constraint([_|Es], R, Ctxt, C) :-
%%     identify_late_constraint(Es, R, Ctxt, C).

%% not_at(R, C) :- not testable_at(R, C).

%% testable_at(R, _X=Y) :- R == Y.
%% testable_at(R, _X\=Y) :- R == Y.

%% % order_edges(E1s, E2s): E2s contains all edges in E1s, but ordered in
%% % a canonical way
%% order_edges(ETin, ETout) :-
%%     empty_assoc(Ain),
%%     % create a list containing canonical constraints and also insert
%%     % them into association list
%%     fill_assoc(ETin, Ain, [], Aout, Lout),
%%     % sort the canonical constraints
%%     sort(Lout, Lsort),
%%     % return the edge_subtrees in the corresponding order
%%     sorted_edgesubtrees(Lsort, Aout, ETout),
%%     true.

%% % fill_assoc(EdgeTreeList, AssocIn, ListIn, AssocOut, ListOut)
%% % Iterate over 'EdgeTreeList', add canonical form of constraint to
%% % ListIn, also add key-value pair of canonical constraint and
%% % Edge-Subtree term in AssocIn
%% fill_assoc([], A, L, A, L).
%% fill_assoc([edge_subtree(E, T)|R], Ain, Lin, Aout, Lout) :-
%%     %% canonical_form(E, C),
%%     %% edge_list_form(E, EQ, NEQ),
%%     ve_representation(E, EQ, NEQ),
%%     canonical_form(EQ, NEQ, C),
%%     put_assoc(C, Ain, edge_subtree(E, T), Atmp),
%%     basics:append(Lin, [C], Ltmp),
%%     fill_assoc(R, Atmp, Ltmp, Aout, Lout).

%% sorted_edgesubtrees([], _, []).
%% sorted_edgesubtrees([CC|CCR], A, [ET|ETR]) :-
%%     get_assoc(CC, A, ET),
%%     sorted_edgesubtrees(CCR, A, ETR).

%% % If X is a constant, leave T_in unchanged
%% update_edges(T_in, X, _C, _Ctxt, T_in) :- nonvar(X).

%% % Base case for edge recursion
%% update_edges([], _Y, _C, _Ctxt, []).

%% % If X is not the root, recurse on the edges of the tree
%% update_edges(tree(X, S1), Y, C, Ctxt, tree(X, S2)) :-
%%     X \== Y,
%%     update_edges(S1, Y, C, Ctxt, S2).

%% % Updates the subtrees in the edge list one at a time
%% update_edges([edge_subtree(Constraints, T) | R], X, C, Ctxt, [edge_subtree(Constraints, T1)| R1]) :-
%%     absmerge(Constraints, Ctxt, Ctxt1),
%%     update_edges(T, X, C, Ctxt1, T1),
%%     update_edges(R, X, C, Ctxt, R1).

%% % Handles logic for when X is the root of the tree
%% update_edges(tree(X, Edges), Y, C, Ctxt, tree(X, _UpdatedSubtrees)) :-
%%     X == Y,
%%     update_subtrees(Edges, C, [], Ctxt, UpdatedSubtrees),
%%     remove_empty_edge_subtrees(UpdatedSubtrees, _UpdatedSubtrees).

%% % Leaf nodes are left unchanged
%% update_edges(leaf(_X), Y, _C, _Ctxt, leaf(_X)) :- var(Y).

%% % Implements completeness by adding the complement of C to the previous constraints
%% update_subtrees([], C, Prev, Ctxt, [edge_subtree(Complement, leaf(0))]) :-
%%     complement_atom(C, _C),
%%     basics:append(Prev, [_C], Complement).

%% % Add C to the constraint list on an edge which does not have 0 child
%% update_subtrees([edge_subtree(C1, T)|Edges], C, Prev, Ctxt, [UpdatedSubtree | UpdatedEdges]) :-
%%     (T \== leaf(0)
%%     ->  basics:append(C1, [C], C2),
%%         % Check if the tree is satisfiable
%%         (absmerge(C2, Ctxt, Total_Constraints), 
%%             write('total constraints'), writeln(Total_Constraints), satisfiable(Total_Constraints)
%%         ->  true
%%         ;   fail
%%         ),
%% 	    (satisfiable(C2)
%%         ->  basics:append(Prev, C1, Next),
%%             UpdatedSubtree = edge_subtree(C2, T)
%%         ;   UpdatedSubtree = []
%%         )
%%     ;   Next = Prev, C2 = C1, UpdatedSubtree = edge_subtree(C2, T)
%%     ),
%%     update_subtrees(Edges, C, Next, Ctxt, UpdatedEdges).

%% % Removes empty lists generated when an added constraint makes the total formula unsatisfiable
%% remove_empty_edge_subtrees([], []).
%% remove_empty_edge_subtrees([[]|Rest], Cleaned) :-
%%     remove_empty_edge_subtrees(Rest, Cleaned).

%% remove_empty_edge_subtrees([X|Rest], [X|Cleaned]) :-
%%     X \== [],
%%     remove_empty_edge_subtrees(Rest, Cleaned).

%% % Compares two root nodes based on switch/instance ID
%% compare_roots(Ctxt, R1, R2, 0) :-
%%     find_id(Ctxt, R1, id(S, I)),
%%     find_id(Ctxt, R2, id(S, I)).

%% compare_roots(Ctxt, R1, R2, -1) :-
%%     find_id(Ctxt, R1, id(S1, I1)),
%%     find_id(Ctxt, R2, id(S2, I2)),
%%     (I1 @< I2
%%     ->  true
%%     ;   (S1 @< S2
%%         ->  true
%%         ;   false
%%         )
%%     ).

%% compare_roots(Ctxt, R1, R2, 1) :-
%%     find_id(Ctxt, R1, id(S1, I1)),
%%     find_id(Ctxt, R2, id(S2, I2)),
%%     (I1 @> I2
%%     ->  true
%%     ;   (S1 @> S2
%%         ->  true
%%         ;   false
%%         )
%%     ).

%% find_id([c(X, ID, Type)|Rest], Term, ID) :-
%%     X == Term, !.
%% find_id([c(X, IDX, Type)|Rest], Term, ID) :-
%%     X \== Term,
%%     find_id(Rest, Term, ID).

%% % OSSD contains X if X is the root
%% contains(tree(Y, _), X) :- X==Y, !.

%% % OSDD contains X if X is in the children lists
%% contains(tree(Y, L), X) :-
%%     X \== Y,
%%     contains(L, X).

%% % OSDD constaints X if X is in the current sub-OSDD
%% % or if X is in a later sub-OSDD
%% contains([edge_subtree(_C,T)|R], X) :-
%%     (contains(T, X) 
%%     -> true
%%     ;  contains(R, X)
%%     ).

%% % For and/or OSDD pairs, X is in the left or right OSDD
%% contains(and(T1, _T2), X) :-
%%     contains(T1, X), !.
%% contains(and(_T1, T2), X) :-
%%     contains(T2, X), !.
%% contains(or(T1, _T2), X) :-
%%     contains(T1, X), !.
%% contains(or(_T1, T2), X) :-
%%     contains(T2, X), !.

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
%% prolog variables. We use the vertices edges representation that can
%% be given as input to "ugraph" package. Since we have to distinguish
%% between equality and disequality atomic constraints, we maintain
%% two graphs for each constraint formula: one for equality atomic
%% constraints and the other for disequality atomic constraints.


%% /* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
%% canonical_label(+Var/Const, -Canonical_Label)
%% Var/Const: Attributed variable or a "type" constant
%% Canonical_Label: Unique label for Var/Const
%% - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
%% canonical_label(V, L) :-
%%     (var(V)
%%     ->
%% 	read_id(V, id(S, I)),
%% 	id_label(id(S, I), L)
%%     ;
%%         L = V
%%     ).


%% :- table id_label/2.
%% %:- index('$id_label'/2, [2,1]).
%% id_label(id(S, I), L) :-
%%     gensym(var, L),
%%     assert('$id_label'(id(S, I), L)).

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % Constraint processing definitions
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% % Combines two constraint lists by conjunction
%% constraints_conjunction(C1, C2, C) :-
%%     absmerge(C1, C2, C), 
%%     satisfiable(C).

%% % Complements a atomic constraint
%% complement_atom(X=Y, X\=Y).
%% complement_atom(X\=Y, X=Y).


%% % Gets the unique variables of a constraint list
%% getvars([], L, L).
%% getvars([X=Y|R], L, Lout) :-
%%     (var(X), \+ lists:memberchk_eq(X, L)
%%     ->
%% 	    basics:append(L, [X], Ltmp)
%%     ;
%%         Ltmp = L
%%     ),
%%     (var(Y), \+ lists:memberchk_eq(Y, L)
%%     ->
%% 	    basics:append(Ltmp, [Y], Ltmp1)
%%     ;
%%         Ltmp1 = Ltmp
%%     ),
%%     getvars(R, Ltmp1, Lout).

%% getvars([X\=Y|R], L, Lout) :-
%%     (var(X), \+ lists:memberchk_eq(X, L)
%%     ->
%%         basics:append(L, [X], Ltmp)
%%     ;
%%         Ltmp = L
%%     ),
%%     (var(Y), \+ lists:memberchk_eq(Y, L)
%%     ->
%%         basics:append(Ltmp, [Y], Ltmp1)
%%     ;
%%         Ltmp1 = Ltmp
%%     ),
%%     getvars(R, Ltmp1, Lout).

%% %% complete a constraint formula with implicit constraints
%% %% CComp is the union of C and implicit constraints
%% get_implicit_constraints(C, CComp) :-
%%     getvars(C, [], Vars),
%%     id_var_pairs(Vars, Pairs),
%%     list_to_assoc(Pairs, A),
%%     %% canonical_form(C, cg(EQ, NEQ)),
%%     %% edge_list_form(C, E, N),
%%     ve_representation(C, E, N),
%%     canonical_form(E, N, cg(EQ, NEQ)),
%%     graph_to_formula(A, eq, EQ, [], C1),
%%     graph_to_formula(A, neq, NEQ, C1, CComp),
%%     true.

%% id_var_pairs([], []).
%% id_var_pairs([V|R], [Id-V|PR]) :-
%%     %% canonical_label_1(V, Id),
%%     canonical_label(V, Id),
%%     id_var_pairs(R, PR).

%% graph_to_formula(Assoc, Op, [], C, C).
%% graph_to_formula(Assoc, Op, [ID1-ID2|R], Cin, Cout) :-
%%     % use only one of the edges in the constraint graph
%%     (ID1 @< ID2
%%     ->
%%         (functor(ID1, id, 2)
%%         ->
%%             get_assoc(ID1, Assoc, X)
%%         ;
%%             X = ID1
%%         ),
%%         (functor(ID2, id, 2)
%%         ->
%%             get_assoc(ID2, Assoc, Y)
%%         ;
%%             Y = ID2
%%         ),
%%         (Op = eq
%%         ->
%%             basics:append(Cin, [X=Y], Ctmp)
%%         ;   
%%             (Op = neq
%%             ->
%%                 basics:append(Cin, [X\=Y], Ctmp)
%%             ;
%%                 fail
%%             )
%%         ),
%%         graph_to_formula(Assoc, Op, R, Ctmp, Cout)
%%     ;
%%         graph_to_formula(Assoc, Op, R, Cin, Cout)
%%     ).

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

%% mytreeprob(leaf(X), X).

%% mytreeprob(tree(R, ETs), P) :-
%%     mytreeprob_1(R, ETs, 0, P).

%% mytreeprob_1(R, [], Pin, Pin).
%% mytreeprob_1(R, [edge_subtree(E, T)|Rest], Pin, Pout) :-
%%     ve_representation(E, EQ, NEQ),
%%     canonical_label(R, Label),
%%     solutions(Label, EQ, NEQ, S),
%%     copy_term(var_tree(R, T), Copy),
%%     Copy =.. [var_tree| [R1, T1]],
%%     edge_prob(var(R1, T1), S, 0, Pedge),
%%     Ptmp is Pin + Pedge,
%%     mytreeprob_1(R, Rest, Ptmp, Pout),
%%     true.

%% edge_prob(var(R, T), [], Pin, Pin).
%% edge_prob(var(R, T), [V|VR], Pin, Pout) :-
%%     copy_term(var_tree(R, T), Copy),
%%     Copy =.. [var_tree| [R1, T1]],
%%     edge_prob_1(R1, V, T1, P),
%%     Ptmp is Pin + P,
%%     edge_prob(var(R, T), VR, Ptmp, Pout).

%% % edge probability under a particular value for output variable
%% edge_prob_1(R, V, T, P) :-
%%     read_id(R, id(S, _)),
%%     intrange(S, Lower, Upper),
%%     Index is V - Lower + 1,
%%     set_sw(S, Dist),
%%     lists:nth(Index, Dist, Pv),
%%     R = V,
%%     mytreeprob(T, Pt),
%%     P is Pv * Pt.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Misc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


writeDot(OSDD, File) :- writeDotFile(OSDD, File).

%% :- dynamic '$id_label'/2.

initialize :-
    %% retractall('$id_label'/2),
    retractall('$unique_table'/2),
    prepare(0).

compute_osdd(Query, CO) :-
    Query =.. [Pred | Args],
    make_node(1, One),
    append(Args, [[]-One, CO], Args1),
    Query1 =.. [Pred | Args1],
    Query1.

?- initialize.
