:- export satisfiable_constraint_graph/2, solutions/4, canonical_form/3.

:- import is_empty/1, delete/3 from lists.
:- import vertices_edges_to_ugraph/3, transitive_closure/2, edges/2, add_edges/3, del_edges/3 from ugraphs.
:- import empty_assoc/1, put_assoc/4, gen_assoc/3, assoc_to_list/2 from assoc_xsb.
:- import list_to_ord_set/2 from ordsets.
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
k-k is added.  Otherwise vertex is labeled 'varn', key-value varn-X,
is added where where X is a fresh variable.
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
        usermod:'$id_label'(id(S, _I), Key),
	usermod:intrange(S, Lower, Upper),
	Value in Lower..Upper,
	enforce_domain_constraints(Rest)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
enforce_equality_constraints(+Assoc, +S_representation)

Loop through the S_representation and enforce equality constraints
specified by edges. The constraints are enforced using bounds package
and on the variables that are mapped to the labels.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
enforce_equality_constraints(Assoc, []).
enforce_equality_constraints(Assoc, [Vertex-Neighbors|Rest]) :-
    gen_assoc(Vertex, Assoc, Value),
    enforce_equality_with_neighbors(Value, Assoc, Neighbors),
    enforce_equality_constraints(Assoc, Rest).

enforce_equality_with_neighbors(Value, Assoc, []).
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
enforce_disequality_constraints(Assoc, []).
enforce_disequality_constraints(Assoc, [Vertex-Neighbors|Rest]) :-
    gen_assoc(Vertex, Assoc, Value),
    enforce_disequality_with_neighbors(Value, Assoc, Neighbors),
    enforce_disequality_constraints(Assoc, Rest).

enforce_disequality_with_neighbors(Value, Assoc, []).
enforce_disequality_with_neighbors(Value, Assoc, [H|R]) :-
    gen_assoc(H, Assoc, Value1),
    Value #\= Value1,
    enforce_disequality_with_neighbors(Value, Assoc, R).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
solutions(+Label, +EQ, +NEQ, -Solutions)

'Label' is the label of a variable in the CSP, represented by graph
with equality edges 'EQ' and disequality edges 'NEQ'. 'Solutions' is
the set of all solutions to 'Label' which satisfies the CSP.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
solutions(Label, EQ, NEQ, Solutions) :-
    ((is_empty(EQ), is_empty(NEQ))
    ->
	% Variable corresponding to label is unconstrained
	usermod:'$id_label'(id(S, _I), Label),
	usermod:intrange(S, Lower, Upper),
	var(X),
	X in Lower..Upper,
	findall(X, label([X]), Solutions1),
	list_to_ord_set(Solutions1, Solutions)
    ;
        % Variable corresponding to label is constrained
        vertices_edges_to_ugraph([], EQ, EQ1),
        vertices_edges_to_ugraph([], NEQ, NEQ1),
        empty_assoc(A),
        map_labels_to_vars(A, EQ1, A1),
        map_labels_to_vars(A1, NEQ1, A2),
        assoc_to_list(A2, List),
        enforce_domain_constraints(List),
        enforce_equality_constraints(A2, EQ1),
        enforce_disequality_constraints(A2, NEQ1),
	gen_assoc(Label, A2, Var),
	findall(Var, label([Var]), Solutions1),
	list_to_ord_set(Solutions1, Solutions)
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
canonical_form(+EQ, +NEQ, cg(-EQ1, -NEQ1))

Given vertices edges representation of constraint graph in EQ and NEQ,
complete the equality and disequality constraints, change them to
S-representation, sort them to get EQ1 and NEQ1. Return cg(EQ1, NEQ1)
as the canonical representation of the constraint graph.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
canonical_form(EQ, NEQ, cg(G11, G33)) :-
    % G1 = transitive_closure(EQ)
    vertices_edges_to_ugraph([], EQ, EQS),
    transitive_closure(EQS, G1),
    % G2 = transitive_closure(NEQ)
    vertices_edges_to_ugraph([], NEQ, NEQS),
    transitive_closure(NEQS, G2),
    % G3 = transitive_closure(EQ + NEQ)
    edges(NEQS, NEQedges),
    add_edges(EQS, NEQedges, EQNEQ),
    transitive_closure(EQNEQ, G3),
    % completed equality edges are in G1
    % completed disequality edges are in G3 - (G1 + G2)
    % however we need to remove self loops and duplicates
    edges(G1, Edges1),
    edges(G2, Edges2),
    del_edges(G3, Edges1, G31),
    del_edges(G31, Edges2, G32),
    % discard self-loops and duplicate neighbors
    discard_redundant_edges(G1, G11),
    discard_redundant_edges(G32, G33).

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
