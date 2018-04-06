:- import append/3, member/2, ith/3 from basics.
:- import prepare/1, gensym/2 from gensym.
:- import concat_atom/2 from string.
:- import is_empty/1 from lists.

:- import writeDotFile/2 from visualize.
:- import satisfiable_constraint_graph/2, solutions/4,
   canonical_constraint/3 from constraints.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
msw(+S, +I, X, +CtxtIn, +OsddIn, -CtxtOut, -OsddOut)

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
constraint(+C, +CtxtIn, +OsddIn, -CtxtIn, -OsddOut)

Perform type checking of atomic constraint C and update the OsddIn to OsddOut
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
constraint(C, CtxtIn, OsddIn, CtxtIn, OsddOut) :-
    type_check(CtxtIn, C),
    apply_constraint(CtxtIn, OsddIn, C, [], [], CtxtIn, OsddOut).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
project_context(+CtxHead, +CtxtCur, +FreeVars, -CtxtOut)

From 'CtxtCur' remove bound variables to get CtxtOut. A bound variable is
the one which doesn't occur in CtxtHead and is not part of 'FreeVars'
list.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
project_context(CtxtHead, CtxtCur, FreeVars, CtxtOut) :-
    term_variables(FreeVars, FV),
    project_context_1(CtxtHead, CtxtCur, FV, [], Cout),
    sort(Cout, CtxtOut).

project_context_1(_CtxtHead, [], _FV, Cin, Cin).
project_context_1(CtxtHead, [V - (S, I) | T], FV, Cin, Cout) :-
    (member(V, FV)
    ->
	append(Cin, [V - (S, I)], Ctmp)
    ;
        (existing_context(CtxtHead, V, S, I)
	->
	    append(Cin, [V - (S, I)], Ctmp)
	;
	    Ctmp = Cin
	)
    ),
    project_context_1(CtxtHead, T, FV, Ctmp, Cout).
    %% (var(H)
    %% ->
    %% 	(existing_context(CtxtIn, H, _S, _I)
    %% 	->
    %% 	    project_context_1(Ctxt, T, CtxtIn, CtxtOut)
    %% 	;
    %%         (existing_context(Ctxt, H, S, I)
    %% 	    ->
    %% 	        append(CtxtIn, [H-(S, I)], CtxtTmp)
    %% 	    ;
    %% 	        write('Error in project_context_1. Failed to find id of variable '),
    %% 		writeln(H),
    %% 		fail
    %% 	    ),
    %% 	    project_context_1(Ctxt, T, CtxtTmp, CtxtOut)
    %% 	)
    %% ;
    %%     project_context_1(Ctxt, T, CtxtIn, CtxtOut)
    %% ).

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
				     [], EdgeSubTrees1),
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
    apply_constraint(Ctxt, T, C, OutVars, PathConstr1, Ctxt, TOut),
    apply_constraint_no_urg(Ctxt, Rest, C, OutVars, PathConstr, RestOut).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
apply_constraint_urg(+EdgeSubtrees, +Constraint, +PathConstr, +ETin, -ETout)

Given a list of edge/subtree pairs, whose root has 'PathConstr'
labeling the path to the root, apply 'Constraint' to each of the edges
and return the new list of edge/subtree pairs.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
apply_constraint_urg([], _C, _P, ETin, ETin).
apply_constraint_urg([edge_subtree(E, T)| Rest], C, PathConstr, ETin,
		     ETout) :-
    append(PathConstr, E, PathConstr1),
    append(PathConstr1, [C], PathConstr2),
    (satisfiable(PathConstr2)
    ->
	append(E, [C], EOut),
	append(ETin, [edge_subtree(EOut, T)], ET)
    ;
        ET = ETin
    ),
    apply_constraint_urg(Rest, C, PathConstr, ET, ETout).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
update_context(+CtxtIn, +X, +S, +I, -CtxtOut)

Check if 'CtxtIn' specifies the switch/instance pair of the variable
X. If so, it should match the pair (S, I). Otherwise, add the
switch/instance pair of X as (S, I) to CtxtIn to produce CtxtOut.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
update_context(CtxtIn, X, S, I, CtxtOut) :-
    (existing_context(CtxtIn, X, S1, I1)
    ->
	% we avoid duplicates and check that same context doesn't give
	% two ids
	S = S1,
	I = I1,
	CtxtOut = CtxtIn
    ;
        append(CtxtIn, [X-(S, I)], Ctxt),
        sort(Ctxt, CtxtOut)
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
    concat_atom([var,'_',S,'_',I], L),
    assert('$canonical_label'(S, I, L)).

:- dynamic '$canonical_label'/3.

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
		    [edge_subtree(CF, T) | RestC]) :-
    ve_representation(E, EQ, NEQ),
    canonical_constraint(EQ, NEQ, cg(EQ1, NEQ1)),
    eq_graph_to_formula(EQ1, [], EQF),
    neq_graph_to_formula(NEQ1, EQF, F), 
    %append(EQ1, NEQ1, CE1),
    %sort(CE1, CE),
    sort(F, CF),
    canonical_form_et_1(Rest, RestC).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
eq_graph_to_formula(+EQedges, +FormulaIn, -FormulaOut)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
eq_graph_to_formula([], F, F).
eq_graph_to_formula([A-B|Rest], Fin, Fout) :-
    (member(A=B, Fin)
    ->
	Ftmp = Fin
    ;
        (member(B=A, Fin)
	->
	    Ftmp = Fin
	;
	    append(Fin, [A=B], Ftmp)
	)
    ),
    eq_graph_to_formula(Rest, Ftmp, Fout).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
neq_graph_to_formula(+NEQedges, +FormulaIn, -FormulaOut)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
neq_graph_to_formula([], F, F).
neq_graph_to_formula([A-B|Rest], Fin, Fout) :-
    (member(A\=B, Fin)
    ->
	Ftmp = Fin
    ;
        (member(B\=A, Fin)
	->
	    Ftmp = Fin
	;
	    ((integer(A), integer(B))
	    ->
		% redundant disequality constraint between constants
		Ftmp = Fin
	    ;
	        append(Fin, [A\=B], Ftmp)
	    )
	)
    ),
    neq_graph_to_formula(Rest, Ftmp, Fout).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
and(+Osdd1, +Osdd2, -Osdd)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
and(Osdd1, Osdd2, Osdd) :-
    binop(and, Osdd1, Osdd2, [], Osdd).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
or(+Osdd1, +Osdd2, -Osdd)
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
or(Osdd1, Osdd2, Osdd) :-
    write('OR :'), write(Osdd1), write(' '), writeln(Osdd2),
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
	    binop_edges(Op, ET1, Osdd2, PathConstr, [], ET),
	    canonical_form_et(ET, CF),
	    canonical_form(tree(Root1, CF), CT),
	    make_node(CT, Osdd)
	;
	    binop_edges(Op, ET2, Osdd1, PathConstr, [], ET),
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

binop_pairwise(_Op, [], _ET2, _P, ETin, ETin).

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
        ETtmp = ETin
    ),
    binop_pairwise_1(Op, E1, T1, Rest, PathConstr, ETtmp, ETout).

binop_edges(_Op, [], _Osdd, _P, ETin, ETin).
binop_edges(Op, [edge_subtree(E, T)|Rest], Osdd, PathConstr,
	    ETin, ETout) :-
    append(PathConstr, E, PathConstr1),
    (satisfiable(PathConstr1)
    ->
	binop(Op, T, Osdd, PathConstr1, T1),
        append(ETin, [edge_subtree(E, T1)], ET)
    ;
        ET = ETin
    ),
    binop_edges(Op, Rest, Osdd, PathConstr, ET, ETout).


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
% Misc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


writeDot(OSDD, File) :- writeDotFile(OSDD, File).

initialize :-
    retractall('$canonical_label'/3),
    retractall('$unique_table'/2),
    prepare(0).

compute_osdd(Query, CO) :-
    Query =.. [Pred | Args],
    map_to_constants(Args, Args1),
    make_node(1, One),
    append(Args1, [[], One, _CtxtOut, CO], Args2),
    Query1 =.. [Pred | Args2],
    Query1.

map_to_constants([], []).
map_to_constants([Arg | Args], [Arg1 | Args1]) :-
    (var(Arg)
    ->
	Arg1 = Arg
    ;
        values_list(L),
	(ith(I, L, Arg)
	->
	    Arg1 = I
	;
	    write('failed to map '), write(Arg), writeln(' to integer'),
	    fail
	)
    ),
    map_to_constants(Args, Args1).
        
?- initialize.
