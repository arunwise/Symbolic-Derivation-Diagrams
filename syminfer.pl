:- import append/3, member/2, ith/3, length/2 from basics.
:- import prepare/1, gensym/2 from gensym.
:- import concat_atom/2 from string.
:- import is_empty/1, memberchk_eq/2, sum_list/2 from lists.
:- import empty_assoc/1, put_assoc/4, get_assoc/3 from assoc_xsb.
:- import ord_subtract/3, ord_add_element/3, ord_union/3,
list_to_ord_set/2 from ordsets.

:- import writeDotFile/2 from visualize.
:- import satisfiable_constraint_graph/2, solutions/4,
   canonical_constraint/3 from constraints.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
msw(+S, +I, X, +CtxtIn, +OsddIn, -CtxtOut, -OsddOut)

Update the CtxtIn with Id of random variables X. Compute OsddOut as
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
project_context_1(CtxtHead, [V - (S, I, N) | T], FV, Cin, Cout) :-
    (memberchk_eq(V, FV)
    ->
	append(Cin, [V - (S, I, N)], Ctmp)
    ;
        (existing_context(CtxtHead, V, S, I, N)
	->
	    append(Cin, [V - (S, I, N)], Ctmp)
	;
	    Ctmp = Cin
	)
    ),
    project_context_1(CtxtHead, T, FV, Ctmp, Cout).

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
update_context(+CtxtIn, +Xs, +S, +I, -CtxtOut)

Update 'CtxtIn' by updating the switch/instance/component triple of each 
variable in Xs.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
update_context(CtxtIn, Xs, S, I, CtxtOut) :-
    update_context_1(CtxtIn, Xs, S, I, 1, CtxtOut).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
update_context_1(+CtxtIn, +Xs, +S, +I, +N, -CtxtOut)

Check if 'CtxtIn' specifies the switch/instance/component triple of
the variable X. If so, it should match the triple (S, I, N).
Otherwise, add the switch/instance/component triple of X as (S, I, N)
to CtxtIn and recurse for all the elements in Xs.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
update_context_1(CtxtIn, [], _, _, _, CtxtOut) :-
    sort(CtxtIn, CtxtOut).
update_context_1(CtxtIn, [X|Rest], S, I, N, CtxtOut) :-
    (existing_context(CtxtIn, X, S, I, N)
    ->
	% we avoid duplicates and check that same context doesn't give
	% two ids
	Ctxt = CtxtIn
    ;
        append(CtxtIn, [X-(S, I, N)], Ctxt)
    ),
    M is N + 1,
    update_context_1(Ctxt, Rest, S, I, M, CtxtOut).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
existing_context(+CtxtIn, +X, -S, -I, -N)

Check 'CtxtIn' for the switch/instance/component triple of X.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
existing_context([X1-(S1, I1, N1) | Rest], X, S, I, N) :-
    (X == X1
    ->
	S = S1,
	I = I1,
	N = N1
    ;
        existing_context(Rest, X, S, I, N)
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
canonical_label(+S, +I, +N, -L)

Construct a canonical label for switch 'S', instance 'I' and component 'N' 
as the atom 'var_S_I_N'
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
:- table canonical_label/4.
canonical_label(S, I, N, L) :-
    ground(S), ground(I), ground(N),
    concat_atom([var,'_',S,'_',I,'_',N], L),
    assert('$canonical_label'(S, I, N, L)).

:- dynamic '$canonical_label'/4.

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
        %member(Term2, Type)
        type(Type, Values),
	member(Term2, Values)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
find_type(+Ctxt, +Var, -Type)

Find the type of 'Var' by using the switch specified by 'Ctxt'
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
find_type([X-(S, _I, N)| _Rest], Term, Type) :-
    X == Term, !,
    outcomes(S, Types),
    ith(N, Types, Type).
find_type([X-(_S, _I, _N)|Rest], Term, Type) :-
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
	existing_context(Ctxt, Lhs, SL, IL, NL),
	canonical_label(SL, IL, NL, LLhs)
    ;
        LLhs=Lhs
    ),
    (var(Rhs)
    ->
	existing_context(Ctxt, Rhs, SR, IR, NR),
	canonical_label(SR, IR, NR, LRhs)
    ;
        LRhs = Rhs
    ).
labeled_form(Ctxt, Lhs\=Rhs, LLhs\=LRhs) :-
    (var(Lhs)
    ->
	existing_context(Ctxt, Lhs, SL, IL, NL),
	canonical_label(SL, IL, NL, LLhs)
    ;
        LLhs = Lhs
    ),
    (var(Rhs)
    ->
	existing_context(Ctxt, Rhs, SR, IR, NR),
	canonical_label(SR, IR, NR, LRhs)
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
    % write('OR :'), write(Osdd1), write(' '), writeln(Osdd2),
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

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% % Query processing definitions
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% % Maps the domain of an exported query to the integer representation
%% map_domain(Q, _Q) :-
%%     write('Q: '), writeln(Q),
%%     values_list(L),
%%     Q =.. [F | Args],
%%     map_args(Args, _Args, L),
%%     basics:append(_Args, [leaf(1), O], OSDD_Args),
%%     _Q =.. [F | OSDD_Args],
%%     write('_Q: '), writeln(_Q).

%% % Maps an individual argument to it's corresponding interger representation
%% map_args([], [], _).
%% map_args([Arg|Args], [_Arg|_Args], L) :-
%%     (basics:ith(I, L, Arg)
%%     ->  _Arg = I
%%     ;   _Arg = Arg
%%     ),
%%     map_args(Args, _Args, L).    


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Probability Computation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
probability(+Osdd, +Prob)

It is necessary that Osdd be the root.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
probability(Osdd, P) :-
    % osdd has to be the root node
    empty_assoc(A),
    pi(Osdd, A, P).

:- table pi/3.
pi(Node, _Sigma, 0) :- '$unique_table'(Node, 0), !.
pi(Node, _Sigma, 1) :- '$unique_table'(Node, 1), !.
pi(Node, Sigma, P) :-
    '$unique_table'(Node, tree(Root, ET)),
    pi_1(Root, ET, Sigma, ProbList),
    sum_list(ProbList, P).

pi_1(_Root, [], _Sigma, []).
pi_1(Root, [edge_subtree(Edge, Tree) | Rest], Sigma, [Prob | ProbRest]) :-
    apply_substitution(Sigma, Edge, E1),
    ve_representation(E1, EQ, NEQ),
    solutions(Root, EQ, NEQ, Sols),
    pi_2(Root, Sols, Sigma, Tree, 0, Prob),
    pi_1(Root, Rest, Sigma, ProbRest).

pi_2(_R, [], _Sigma, _Tree, Pin, Pin).
pi_2(Root, [Val | Rest], Sigma, Tree, Pin, Pout) :-
    put_assoc(Root, Sigma, Val, Sigma1),
    pi_extra(Tree, Sigma1, Psubtree),

    '$canonical_label'(Switch, _Instance, Root),
    set_sw(Switch, Dist),
    intrange(Switch, Lower, Upper),
    Ind is Val - Lower + 1,
    ith(Ind, Dist, Pval),
    
    Pedge is Pval * Psubtree,
    Ptmp is Pin + Pedge,
    pi_2(Root, Rest, Sigma, Tree, Ptmp, Pout).

pi_extra(Node, Sigma, P) :-
    free_vars(Node, FV),
    empty_assoc(A),
    project_substitution(Sigma, FV, A, Sigma1),
    pi(Node, Sigma1, P).
    
:- table free_vars/2.
free_vars(Node, F) :-
    edge_vars(Node, E),
    output_vars(Node, O),
    ord_subtract(E, O, F).

:- table output_vars/2.
output_vars(Node, O) :-
    ('$unique_table'(Node, 0)
    ->
	O = []
    ;
        ('$unique_table'(Node, 1)
	->
	    O = []
	;
	    '$unique_table'(Node, tree(Root, ET)),
	    output_vars_1(ET, [], Ovars),
	    ord_add_element(Ovars, Root, O)
	)
    ).

output_vars_1([], Oin, Oin).
output_vars_1([edge_subtree(_E, T) | Rest], Oin, Out) :-
    output_vars(T, O),
    ord_union(Oin, O, Otmp1),
    % ord_union/3 has bug
    list_to_ord_set(Otmp1, Otmp),
    output_vars_1(Rest, Otmp, Out).

:- table edge_vars/2.
edge_vars(Node, E) :-
    ('$unique_table'(Node, 0)
    ->
	E = []
    ;
        ('$unique_table'(Node, 1)
	->
	    E = []
	;
	    '$unique_table'(Node, tree(_Root, ET)),
	    edge_vars_1(ET, [], E)
	)
    ).

edge_vars_1([], Ein, Ein).
edge_vars_1([edge_subtree(E, T) | Rest], Ein, Eout) :-
    edge_vars(T, Esubtree),
    edge_vars_2(E, [], Eedge),
    ord_union(Ein, Esubtree, Ein1),
    ord_union(Ein1, Eedge, Etmp1),
    % ord_union/3 has bug
    list_to_ord_set(Etmp1, Etmp),
    edge_vars_1(Rest, Etmp, Eout).

edge_vars_2([], Ein, Ein).
edge_vars_2([X=Y|Rest], Ein, Eout) :-
    (integer(X)
    ->
	Etmp = Ein
    ;
        ord_add_element(Ein, X, Etmp)
    ),
    (integer(Y)
    ->
	Etmp1 = Etmp
    ;
        ord_add_element(Etmp, Y, Etmp1)
    ),
    edge_vars_2(Rest, Etmp1, Eout).
edge_vars_2([X\=Y|Rest], Ein, Eout) :-
    (integer(X)
    ->
	Etmp = Ein
    ;
        ord_add_element(Ein, X, Etmp)
    ),
    (integer(Y)
    ->
	Etmp1 = Etmp
    ;
        ord_add_element(Etmp, Y, Etmp1)
    ),
    edge_vars_2(Rest, Etmp1, Eout).

apply_substitution(_Sigma, [], []).
apply_substitution(Sigma, [X=Y|Rest], [X1=Y1|RestSub]) :-
    (get_assoc(X, Sigma, ValX)
    ->
	X1 = ValX
    ;
        X1 = X
    ),
    (get_assoc(Y, Sigma, ValY)
    ->
	Y1 = ValY
    ;
        Y1 = Y
    ),
    apply_substitution(Sigma, Rest, RestSub).
apply_substitution(Sigma, [X\=Y|Rest], [X1\=Y1|RestSub]) :-
    (get_assoc(X, Sigma, ValX)
    ->
	X1 = ValX
    ;
        X1 = X
    ),
    (get_assoc(Y, Sigma, ValY)
    ->
	Y1 = ValY
    ;
        Y1 = Y
    ),
    apply_substitution(Sigma, Rest, RestSub).

project_substitution(_Sigma, [], Sin, Sin).
project_substitution(Sigma, [H| T], Sin, Sout) :-
    (get_assoc(H, Sigma, Val)
    ->
	put_assoc(H, Sin, Val, Stmp)
    ;
        Stmp = Sin
    ),
    project_substitution(Sigma, T, Stmp, Sout).

%% Measurable probability computation

probability_m(Osdd, P) :-
    % osdd has to be the root node
    empty_assoc(A),
    pi_m(Osdd, A, P).

:- table pi_m/3.
pi_m(Node, Sigma, 0) :- '$unique_table'(Node, 0), !.
pi_m(Node, Sigma, 1) :- '$unique_table'(Node, 1), !.
pi_m(Node, Sigma, P) :-
    ('$measurable_prob'(Node, Prob)
    ->
	Prob = P
    ;
        '$unique_table'(Node, tree(Root, ET)),
	pi_1_m(Root, ET, Sigma, ProbList),
	sum_list(ProbList, Prob),
	assert('$measurable_prob'(Node, Prob)),
	Prob = P
     ).

:- dynamic '$measurable_prob'/2.

pi_1_m(_Root, [], _Sigma, []).
pi_1_m(Root, [edge_subtree(Edge, Tree) | Rest], Sigma, [Prob | ProbRest]) :-
    apply_substitution(Sigma, Edge, E1),
    ve_representation(E1, EQ, NEQ),
    solutions(Root, EQ, NEQ, Sols),
    length(Sols, Measure),
    (Measure = 0
    ->
	Prob = 0
    ;
        Sols = [Sol | _Rest],
	pi_2_m(Root, Sol, Sigma, Tree, Psub),
	'$canonical_label'(Switch, _Instance, Root),
	intrange(Switch, Lower, Upper),
	Prob is Measure / (Upper - Lower + 1) * Psub
    ),
    pi_1_m(Root, Rest, Sigma, ProbRest).

pi_2_m(Root, Val, Sigma, Tree, Psub) :-
    put_assoc(Root, Sigma, Val, Sigma1),
    pi_extra_m(Tree, Sigma1, Psub).
    
pi_extra_m(Node, Sigma, P) :-
    free_vars(Node, FV),
    empty_assoc(A),
    project_substitution(Sigma, FV, A, Sigma1),
    pi_m(Node, Sigma1, P).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Misc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


writeDot(OSDD, File) :- writeDotFile(OSDD, File).

initialize :-
    retractall('$canonical_label'/3),
    retractall('$canonical_label'/4),
    retractall('$unique_table'/2),
    retractall('$measurable_prob'/2),
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
	    Arg1 = Arg
	)
    ),
    map_to_constants(Args, Args1).
        
?- initialize.
