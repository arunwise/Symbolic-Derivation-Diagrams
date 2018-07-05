:- import length/2, append/3, member/2, ith/3 from basics.
:- import sum_list/2 from lists.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform_file(+InFile, +OutFile)

Read program in InFile, transform and write it to OutFile
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform_file(InFile, OutFile) :-
    seeing(OF), see(InFile),
    abolish_table_pred(declare/3),
    assert(values_list([])),
    open(OutFile, write, Handle),
    read_and_transform(Handle),
    values_list(L),  % Get the final values_list
    write(Handle, 'values_list('), writeq(Handle, L), writeln(Handle, ').'),
    write_dists(Handle),
    close(Handle),
    retract(values_list(L)),
    seen, see(OF).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
read_and_transform(+Handle)

Read clauses from current inputstream and write transformed clauses to
Handle.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
read_and_transform(Handle) :-
    read(Clause),
    (Clause == end_of_file
    ->  true
    ;   transform(Clause, XClause, Handle),
        (XClause = none
        ->  read_and_transform(Handle)
        ;   num_vars:numbervars(XClause),
            write_clause(XClause, Handle),
            read_and_transform(Handle)
        )
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
write_clause(+XClause, +Handle)

Write transformed clause 'XClause' to Handle.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
write_clause(XClause, Handle) :-
    ((H :- B) = XClause
    ->
	writeq(Handle, H),
	write(Handle, ' :- '),
	writeq(Handle, B),
	write(Handle, '.\n')
    ;
        writeq(Handle, XClause),
        write(Handle, '.\n')
    ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform(+Directive, -Directive, +Handle)

leave directives alone during transformation
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform((:- Directive), (:- Directive), Handle) :- !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform(+Clause, -XClause, +Handle)

Transform 'Clause' to 'XClause' and write the table directives for
rule head to Handle.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform((H_in :- B_in), (H_out :- B_out), Handle) :- !,
    H_in =.. [Pred | Args],
    length(Args, N),
    declare(Pred, N, Handle), % write table directives
    transform_pred(H_in, H_out, (CtxtIn, OsddIn, CtxtOut, OsddOut)),
    transform_body(B_in, CtxtIn, Args, B_out,
		   (CtxtIn, OsddIn, CtxtOut, OsddOut)).
    

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform(+Fact, -XFact, +Handle)

Transform 'Fact' to 'XFact'. If the 'Fact' is a type/2 fact, define
a type and write to Handle.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform(F_in, F_out, Handle) :-
    functor(F_in, F, _N),
    (F = type
    ->  process_domain(F_in),
        transform_pred(F_in, F_out, (CtxtIn, OsddIn, CtxtIn, OsddIn)),
        write_domain_intrange(F_out, Handle),
	assert(F_out)
    ;   transform_pred(F_in, F_out, (CtxtIn, OsddIn, CtxtIn, OsddIn))
    ), !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform_body(+Goals, +CtxtHead, +FreeVars, -XGoals, 
                                 (+CtxtIn, +OsddIn, -CtxtOut, -OsddOut))

Transform a sequence of goals 'Goals' to 'XGoals'. After the last goal
has been transformed, add 'project_context' and 'split_if_needed'
goals'. 

Chain the 'Ctxt' and 'Osdd' arguments so that the output of one goal
is the input for the next goal in the sequence.

Final 'CtxtOut' and 'OsddOut' is returned after performing projection
and splitting.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform_body((G_in, Gs_in), CtxtHead, FreeVars, (G_out, Gs_out),
	       (CtxtIn, OsddIn, CtxtOut, OsddOut)) :- !,
    transform_pred(G_in, G_out, (CtxtIn, OsddIn, Ctxt, Osdd)),
    transform_body(Gs_in, CtxtHead, FreeVars, Gs_out,
		   (Ctxt, Osdd, CtxtOut, OsddOut)).

transform_body(G_in, CtxtHead, FreeVars,
	       (G_out, project_context(CtxtHead, Ctxt, FreeVars, CtxtOut),
		split_if_needed(Osdd, OsddOut)),
	       (CtxtIn, OsddIn, CtxtOut, OsddOut)) :-
    transform_pred(G_in, G_out, (CtxtIn, OsddIn, Ctxt, Osdd)).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform_pred(+PredIn, -PredOut, (+CtxtIn, +OsddIn, -CtxtOut, -OsddOut))

The following predicates don't get transformed.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform_pred(true, true, (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(==(X, Y), ==(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(\==(X, Y), \==(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(=(X, Y), =(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(\=(X, Y), \=(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(<(X, Y), <(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(>(X, Y), >(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(=<(X, Y), =<(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(>=(X, Y), >=(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(!, !, (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(.(X, Y), [X | Y], (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(=..(X, Y), =..(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(is(X, Y), is(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.
transform_pred(outcomes(X, Y), outcomes(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :-
    assert(outcomes(X, Y)), !.
transform_pred(concat_atom(X, Y),
	       concat_atom(X, Y), (Ctxt, Osdd, Ctxt, Osdd)) :- !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform_pred(+Constraint, -XConstraint, (+CtxtIn, +OsddIn, 
                                           -CtxtOut, -OsddOut))

Given input constraint 'Constraint' (of the form {X=Y} or {X\=Y})
transform it to 'XConstraint'. If 'Constraint' has some ground domain
element then we map this element to the integer domain.

For example, if 'Constraint' is {X=Y}, 'XConstraint' would be
constraint(X=Y, CtxtIn, OsddIn, CtxtOut, OsddOut).

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform_pred('{}'(C),
	       constraint(XC, CtxtIn, OsddIn, CtxtOut, OsddOut),
	       (CtxtIn, OsddIn, CtxtOut, OsddOut)) :- 
    C =.. [F, Lhs, Rhs],
    (nonvar(Lhs)
    ->
	find_int_mapping(Lhs, I),
        XC =.. [F, I, Rhs]
    ;
        (nonvar(Rhs)
        ->
	    find_int_mapping(Rhs, I),
            XC =.. [F, Lhs, I]
        ;
	    C = XC
        )
    ), !.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform_pred(+msw(S,I,X), -msw(XS, I, X, CtxtIn, OsddIn, CtxtOut, OsddOut),
(+CtxtIn, OsddIn, -CtxtOut, -OsddOut))

Transform msw(S, I, X) by adding extra arguments CtxtIn, OsddIn and
CtxtOut, OsddOut. We also check that 'S' is a ground atom, and fail
otherwise. If 'S' is ground we change ground domain values to their
corresponding integer values.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform_pred(msw(S, I, X),
	       msw(XS, I, X, CtxtIn, OsddIn, CtxtOut, OsddOut),
	       (CtxtIn, OsddIn, CtxtOut, OsddOut)) :-
    (ground(S)
    ->
	S =.. [F | Vs],
	find_int_mappings(Vs, Is),
	XS =.. [F | Is]
    ;
        write('non-ground switch in the program: '), writeln(S),
        fail
    ), !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform_pred(+type(S, V), -type(XS, I), (+Ctxt, +Osdd, -Ctxt, -Osdd))

Transform type/2 facts. Map any arguments of the switch to
corresponding integers and also map the list of values to their
corresponding integer values.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform_pred(type(S, V), type(XS, I), (Ctxt, Osdd, Ctxt, Osdd)) :-
    (ground(S)
    ->
	S =.. [F | Vs],
	find_int_mappings(Vs, Is),
	XS =.. [F | Is]
    ;
        write('non-ground switch in the program: '), writeln(S),
        fail
    ),
    make_numerical(V, I), !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform_pred(+set_sw(S, V), -set_sw(XS, V), (+Ctxt, +Osdd, -Ctxt, -Osdd))

Transform set_sw directives by transforming switch names if they
contain domain constants. The domain constants are mapped to integer
values. At this point assert set_sw/2 facts so they can be used later
on for writing dist/3  facts.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform_pred(set_sw(S, V), set_sw(XS, V), (Ctxt, Osdd, Ctxt, Osdd)) :-
    (ground(S)
    ->
	S =.. [F | Vs],
	find_int_mappings(Vs, Is),
	XS =.. [F | Is],
	assert(set_sw(S, V))
    ;
        write('non-ground switch in the program: '), writeln(S),
        fail
    ), !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
transform_pred(+PredIn, -PredOut, (+CtxtIn, +OsddIn, -CtxtOut, -OsddOut))

Transform any other predicate by adding extra arguments.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
transform_pred(Pred_in, Pred_out, (CtxtIn, OsddIn, CtxtOut, OsddOut)) :-
    Pred_in =.. [P | Args],
    find_int_mappings(Args, IntArgs),
    append(IntArgs, [CtxtIn, OsddIn, CtxtOut, OsddOut], NewArgs),
    Pred_out =.. [P | NewArgs], !.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
process_domain(+type(S, V))

Update the values_list/1 fact by adding the values 'V' if they are not
already part of the values_list.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
process_domain(F_in) :-
    F_in =.. [_ | [_, Values]],
    values_list(L),
    (member(V, Values), member(V, L) % Values is already in L
    ->  true
    ;   append(L, Values, L1),
        assert(values_list(L1)),
        retract(values_list(L))
    ).

:- table write_domain_intrange/2.
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
write_domain_intrange(+type(S, I), +Handle)

The argument 'I' is a list of contiguous integers. Find the first and
last values in the list and write intrange/3 fact.

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
write_domain_intrange(F_out, Handle) :-
    F_out =.. [_, S, V],
    length(V, L),
    ith(1, V, Start),
    ith(L, V, End),
    write(Handle, intrange(S, Start, End)), write(Handle, '.\n'),
    true.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
make_numerical(+Values -Indices)

'Indices' is the list of indices of elements in 'Values' in the list
given by values_list/1.

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
make_numerical([], []).
make_numerical([V|Vs], [I|_Vs]) :-
    values_list(L),
    ith(I, L, V),
    make_numerical(Vs, _Vs).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
find_int_mappings(+List, -Ilist)

Map constants in List to their indices.

Seems to duplicate the functionality of make_numerical/2

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
find_int_mappings([], []).

find_int_mappings([V|Vs], [I|Is]) :-
    find_int_mapping(V, I),
    find_int_mappings(Vs, Is).

find_int_mapping(V, I) :-
    nonvar(V),
    values_list(L),
    basics:ith(I, L, V), !.

%% do we really need this ??
find_int_mapping(V, I) :-
    nonvar(V),
    (V =.. [F|Args], Args \= []
    ->  find_int_mappings(Args, Is),
        I =.. [F|Is]
    ;   values_list(L),
        basics:ith(I, L, V)
    ), !.

 % If V is not in the values_list, do not change V
find_int_mapping(V, V) :- !.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
declare(+Pred, +Arity, +Handle)

Write table declaration for transformation of Pred/Arity. The transformed
predicate will have arity Arity+4. This is reflected below. Also use lattice
answer subsumption for the last argument.

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
:- table declare/3.
declare(F, N, Handle) :-
    N1 is N+3,
    placeholders('', N1, P),
    str_cat(P, 'lattice(or/3)', P1),
    fmt_write(Handle, ':- table %s(%s).\n', args(F, P1)),
    true.

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
write_dists(+Handle)

Write dist/3 facts.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
write_dists(Handle) :-
    % find all switches
    findall(S, set_sw(S, _), Switches),
    write_dists(Switches, Handle).

write_dists([], _).
write_dists([S| R], Handle) :-
    set_sw(S, Dist),
    outcomes(S, Types),
    Types \= [],
    typesets(Types, TypeSets),
    list_product([[]], TypeSets, Table),
    write_dist3(S, Table, Dist, Handle),
    % write_dist4(S, 1, TypeSets, Handle),
    write_dists(R, Handle).

%% write_dist4(Switch, _, [], Handle).
%% write_dist4(Switch, N, [TypeSet|Rest], Handle) :-
%%     write_dist41(Switch, N, TypeSet, Handle),
%%     N1 is N + 1,
%%     write_dist4(Switch, N1, Rest, Handle).

%% write_dist41(_Switch, _I, [], _Handle).
%% write_dist41(Switch, I, [H|R], Handle) :-
%%     setof(Prob, Val^(dist(Switch, Val, Prob),ith(I, Val, H)), Probs),
%%     sum_list(Probs, P),
%%     write(Handle, dist(Switch, I, H, P)), write(Handle, '.\n'),
%%     write_dist41(Switch, I, R, Handle).
    
typesets([], []).
typesets([T|R], [TS|RR]) :-
    type(T, TS),
    typesets(R, RR).
list_product(Table, [], Table).
list_product(TableIn, [Type|Rest], TableOut) :-
    list_product1(TableIn, Type, Table),
    list_product(Table, Rest, TableOut).

list_product1(TableIn, Type, TableOut) :-
    list_product2(TableIn, Type, [], TableOut).

list_product2([], _, Table, Table).
list_product2([Row|Rest], Type, TableIn, TableOut) :-
    list_product3(Row, Type, NewRows),
    append(TableIn, NewRows, Table),
    list_product2(Rest, Type, Table, TableOut).

list_product3(Row, [], []).
list_product3(Row, [H|T], [Row1|T1]) :-
    append(Row, [H], Row1),
    list_product3(Row, T, T1).

write_dist3(_S, [], _D, _H).
write_dist3(Switch, [Row|Rest], [Prob|PRest], Handle) :-
    write(Handle, dist(Switch, Row, Prob)), write(Handle, '.\n'),
    assert(dist(Switch, Row, Prob)),
    write_dist3(Switch, Rest, PRest, Handle).

placeholders(S, 0, S).
placeholders(IS, N, OS):-
    N > 0,
    str_cat(IS, '_,', S),
    N1 is N-1,
    placeholders(S, N1, OS).
