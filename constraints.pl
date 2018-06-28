:- export satisfiable_constraint_graph/2, solutions/4,
canonical_constraint/3.

:- import is_empty/1, delete/3 from lists.

:- import vertices_edges_to_ugraph/3, transitive_closure/2, edges/2,
add_edges/3, del_edges/3, vertices/2, neighbors/3 from ugraphs.

:- import empty_assoc/1, put_assoc/4, gen_assoc/3, assoc_to_list/2
from assoc_xsb.

:- import list_to_ord_set/2 from ordsets.

:- import append/3, member/2, ith/3 from basics.

:- import (in)/2, (#=)/2, (#\=)/2, label/1 from bounds.

% copied from bounds.pl
:- op(700,xfx,(#=)).
:- op(700,xfx,(#\=)).
:- op(700,xfx,(in)).
:- op(550,xfx,(..)).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
satisfiable_constraint_graph(+EQ, +NEQ)

Is true if the CSP represented by the graph made up of edges from EQ
and NEQ is satisfiable.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
satisfiable_constraint_graph(EQ, NEQ) :-
    vertices_edges_to_ugraph([], EQ, EQ1),
    vertices_edges_to_ugraph([], NEQ, NEQ1),
    empty_assoc(A),
    map_labels_to_vars(A, EQ1, A1),
    map_labels_to_vars(A1, NEQ1, A2),
    assoc_to_list(A2, List),
    enforce_domain_constraints(List),
    enforce_equality_constraints(A2, EQ1),
    enforce_disequality_constraints(A2, NEQ1).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
map_labels_to_vars(+Ain, +S_representation, -Aout) 

Updates associative list Ain, by adding key-value pairs to produce
Aout. If vertex is labeled by numeric constant k, then key-value pair
k-k is added.  Otherwise vertex is has a canonical label 'l',
key-value l-X, is added where where X is a fresh variable.
- - - - - - - - - - - - - - - - - - - -- - - - - - - - - - - - - - - - - */
map_labels_to_vars(A, [], A).
map_labels_to_vars(Ain, [Vertex-_Neighbors| Rest], Aout) :-
    (gen_assoc(Vertex, Ain, _Value)
    ->
	map_labels_to_vars(Ain, Rest, Aout)

    ;
        (number(Vertex)
	->
	    put_assoc(Vertex, Ain, Vertex, Atmp)
	;
	    var(Var),
	    put_assoc(Vertex, Ain, Var, Atmp)
	),
	map_labels_to_vars(Atmp, Rest, Aout)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
get_vars(+Labels, +Assoc, -Vars)

Returns the list of variables associated with the 'Labels' in 'Assoc'
as the list 'Vars'.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
get_vars([], _, []).
get_vars([L|R], A, [V|VR]) :-
    gen_assoc(L, A, V),
    get_vars(R, A, VR).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
enforce_domain_constraints(+List)

Loop through list of key-value pairs and do: If key represents a
variable, get its domain and assert domain constraints on the
corresponding variable which is given by value. Otherwise key
represents a numeric constant, then do nothing.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
enforce_domain_constraints([]).
enforce_domain_constraints([Key-Value|Rest]) :-
    (number(Key)
    ->
	enforce_domain_constraints(Rest)
    ;
        % get the id corresponding to the variable, then its domain
        usermod:'$canonical_label'(S, _I, N, Key),
	usermod:outcomes(S, Types),
	ith(N, Types, Type),
	usermod:intrange(Type, Lower, Upper),
	Value in Lower..Upper,
	enforce_domain_constraints(Rest)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
enforce_equality_constraints(+Assoc, +S_representation)

Loop through the S_representation and enforce equality constraints
specified by edges. The constraints are enforced using bounds package
and on the variables that are mapped to the labels.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
enforce_equality_constraints(_Assoc, []).
enforce_equality_constraints(Assoc, [Vertex-Neighbors|Rest]) :-
    gen_assoc(Vertex, Assoc, Value),
    enforce_equality_with_neighbors(Value, Assoc, Neighbors),
    enforce_equality_constraints(Assoc, Rest).

enforce_equality_with_neighbors(_Value, _Assoc, []).
enforce_equality_with_neighbors(Value, Assoc, [H|R]) :-
    gen_assoc(H, Assoc, Value1),
    Value #= Value1,
    enforce_equality_with_neighbors(Value, Assoc, R).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
enforce_disequality_constraints(+Assoc, +S_representation)

Loop through the S_representation and enforce disequality constraints
specified by edges. The constraints are enforced using bounds package
and on the variables that are mapped to the labels.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
enforce_disequality_constraints(_Assoc, []).
enforce_disequality_constraints(Assoc, [Vertex-Neighbors|Rest]) :-
    gen_assoc(Vertex, Assoc, Value),
    enforce_disequality_with_neighbors(Value, Assoc, Neighbors),
    enforce_disequality_constraints(Assoc, Rest).

enforce_disequality_with_neighbors(_Value, _Assoc, []).
enforce_disequality_with_neighbors(Value, Assoc, [H|R]) :-
    gen_assoc(H, Assoc, Value1),
    Value #\= Value1,
    enforce_disequality_with_neighbors(Value, Assoc, R).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
solutions(+Labels, +EQ, +NEQ, -Solutions)

'Labels' are the canonical labels of variables in the CSP represented
by graph with equality edges 'EQ' and disequality edges
'NEQ'. 'Solutions' is the set of all solutions to 'Labels' which
satisfies the CSP.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
solutions(Labels, EQ, NEQ, Solutions) :-
    vertices_edges_to_ugraph(Labels, EQ, EQ1),
    vertices_edges_to_ugraph(Labels, NEQ, NEQ1),
    empty_assoc(A),
    map_labels_to_vars(A, EQ1, A1),
    map_labels_to_vars(A1, NEQ1, A2),
    assoc_to_list(A2, List),
    enforce_domain_constraints(List),
    enforce_equality_constraints(A2, EQ1),
    enforce_disequality_constraints(A2, NEQ1),
    get_vars(Labels, A2, Vars),
    findall(Vars, label(Vars), Solutions1),
    list_to_ord_set(Solutions1, Solutions), !.    

solutions(_Label, _EQ, _NEQ, []).
    
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
canonical_constraint(+EQ, +NEQ, cg(-EC, -NEC))

Given vertices edges representation of constraint graph in EQ and NEQ,
complete the equality and disequality constraints, to get EC and
NEC. Return cg(EC, NEC) as the canonical representation of the
constraint graph.

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
canonical_constraint(EQ, NEQ, cg(EC, NEC)) :-
    % compute completed equality edges using transitive closure
    vertices_edges_to_ugraph([], EQ, EQS),
    transitive_closure(EQS, G1),
    discard_redundant_edges(G1, G11),
    edges(G11, EC),

    % compute completed disequality edges
    vertices_edges_to_ugraph([], NEQ, NEQS),
    inferred_disequality(EQS, NEQS, [], INEQ),
    add_edges(NEQS, INEQ, G2),
    discard_redundant_edges(G2, G22),
    edges(G22, NEC).
    
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
inferred_disequality(+EQS, +NEQS, +INEQin -INEQout)

Given equality edges in EQS and disequality edges in NEQS, infer extra
disequality edges and put them in INEQout.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
inferred_disequality([], _NEQ, INEQin, INEQin).
inferred_disequality([V-Neib | Rest], NEQ, INEQin, INEQout) :-
    vertices(NEQ, NEQV),
    (member(V, NEQV)
    ->
	neighbors(V, NEQ, Neib1),
	pairwise(Neib, Neib1, INEQ),
	append(INEQin, INEQ, INEQtmp)
    ;
        INEQtmp = INEQin
    ),
    inferred_disequality(Rest, NEQ, INEQtmp, INEQout).

pairwise(Neib1, Neib2, Pairs) :-
    pairwise_1(Neib1, Neib2, [], Pairs).

pairwise_1([], _Neib2, PairsIn, PairsIn).
pairwise_1([N1| Rest1], Neib2, PairsIn, PairsOut) :-
    pairwise_2(N1, Neib2, Pairs),
    append(PairsIn, Pairs, PairsTmp),
    pairwise_1(Rest1, Neib2, PairsTmp, PairsOut).

pairwise_2(_N, [], []).
pairwise_2(N, [N2 | Rest2], [N-N2, N2-N | Rest]) :-
    pairwise_2(N, Rest2, Rest).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
discard_redundant_edges(+S_in, -S_out)

BUG in XSB Ugraphs package causes S-rerpresentation to contain
duplicates in neighbors after call to transitive_closure. These
duplicates need to be removed. Further we remove self loops since they
are redundant in our context. 

Given a constraint graph S_in, remove self-loops and duplicates in
neighbors list to give S_out.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
discard_redundant_edges([], []).
discard_redundant_edges([V-N | Rest], [V-N2 | Rest1]) :-
    list_to_ord_set(N, N1),
    delete(N1, V, N2),
    discard_redundant_edges(Rest, Rest1).
