/*
 * Usage: transform_file('input_file', 'output_file').
 * Transforms a Probabilistic Logic Program into an OSDD processing form.
 * It is assumed that all values/2 declarations appear before all other predicates in 'input_file'.
 */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% File processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Read program in File, transform it and write to OutFile
transform_file(File, OutFile) :- !,
    seeing(OF), see(File),
    abolish_table_pred(declare/3),
    assert(values_list(_)),
    read_and_transform(OutFile),
    values_list(L),  % Get the final values_list
    open(OutFile, append, Handle),
    num_vars:numbervars(L),
    write(Handle, 'values_list('), write(Handle, L), writeln(Handle, ').'), 
    close(Handle),
    retract(values_list(L)),
    seen, see(OF).

% Read clauses from current inputstream and write transformed clauses
% to OutFile
read_and_transform(OutFile) :-
    read(Clause),
    (Clause == end_of_file
    ->  true
    ;   transform(Clause, XClause, OutFile),
        (XClause = none
        ->  read_and_transform(OutFile)
        ;   num_vars:numbervars(XClause),
            writeln(XClause),
            write_clause(XClause, OutFile),
            read_and_transform(OutFile)
        )
    ).

% Write transformed clause (including facts) to outfile
% (basically strips off the enclosing parentheses)
write_clause(XClause, OutFile) :-
    open(OutFile, append, Handle),
    ((H :- B) = XClause
    ->  write(Handle, H), write(Handle, ' :- '), write(Handle, B), write(Handle, '.\n')
    ;   write(Handle, XClause), write(Handle, '.\n')
    ), 
    close(Handle).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Transformation definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Defines which queries Q may be invoked with native domain constants
transform((:- export(Q)), (Q :- map_domain(Q, _Q), _Q), File) :- !.

% Transform clauses and write table directives for transformed
% predicates in the head
transform((H_in :- B_in), (H_out :- B_out), File) :- !,
    functor(H_in, F, N),
    declare(F, N, File), % write table directives
    transform_pred(H_in, H_out, ExtraArgs),
    transform_body(B_in, B_out, ExtraArgs).

% Transform facts except values/2 facts. For values/2 facts we define
% types and write them to file.
transform(F_in, F_out, File) :-
    functor(F_in, F, _N),
    (F = values
    ->  process_domain(F_in, File),
        transform_pred(F_in, F_out, (Arg, Arg)),
        write_domain_intrange(F_out, File)
    ;   transform_pred(F_in, F_out, (Arg, Arg))
    ), !.

% Transforms a sequence of goals (G_in, Gs_in) as follows: 
%     Apply transform_body/3 on the single goal G_in to produce G_out, 
%     Recurse on Gs_in
transform_body((G_in, Gs_in), (G_out, Gs_out), (Arg_in, Arg_out)) :- !,
    transform_body(G_in, G_out, (Arg_in, Arg)),
    transform_body(Gs_in, Gs_out, (Arg, Arg_out)).

% Transform a single goal
transform_body(G_in, G_out, Args) :-
    transform_pred(G_in, G_out, Args).

% Transform predicates. The following predicates don't get transformed
transform_pred(true, true, (Arg, Arg)) :- !.
transform_pred(=(_X, _Y), =(_X, _Y), (Arg, Arg)) :- !.
transform_pred(\=(_X, _Y), \=(_X, _Y), (Arg, Arg)) :- !.
transform_pred(!, !, (Arg, Arg)) :- !.
transform_pred(.(X, Y), [X | Y], (Arg, Arg)) :- !.
transform_pred(=..(X, Y), =..(X, Y), (Arg, Arg)) :- !.

% Transform atomic constraints of the form {C} in constraint language
% If C has some ground domain element we map this element to the integer domain
transform_pred('{}'(C), constraint(_C, Arg_in, Arg_out), (Arg_in, Arg_out)) :- 
    C =.. [F, Lhs, Rhs],
    (nonvar(Lhs)
    ->  find_int_mapping(Lhs, I),
        _C =.. [F, I, Rhs]
    ;   (nonvar(Rhs)
        ->  find_int_mapping(Rhs, I),
            _C =.. [F, Lhs, I]
        ;   C = _C
        )
    ), !.

% Transform msw/3 by possibly renaming type elements to integer domains
transform_pred(msw(S,I,X), msw(_S,I,X, Arg_in, Arg_out), (Arg_in, Arg_out)) :- 
    (var(S)
    ->  _S = S
    ;   S =.. [F | Vs],
        find_int_mappings(Vs, Is),
        _S =.. [F | Is]
    ), !.

% Transforms a values/2 declarations by mapping the domain to integers
transform_pred(values(S, V), values(S, _V), (Arg, Arg)) :- 
    make_numerical(S, V, _V), !.

% Transforms set_sw(S, V) declarations by possibly renaming terms in S
transform_pred(set_sw(S, V), set_sw(_S, V), (Arg, Arg)) :-
    (S =.. [F | Vs]
    ->  find_int_mappings(Vs, Is),
        _S =.. [F | Is]
    ;   S = _S
    ), !.

% Any other predicate is also transformed by adding two extra
% arguments for input OSDD and output OSDD
transform_pred(Pred_in, Pred_out, (Arg_in, Arg_out)) :-
    Pred_in =.. [P | Args],
    find_int_mappings(Args, IntArgs),
    basics:append(IntArgs, [Arg_in, Arg_out], NewArgs),
    Pred_out =.. [P | NewArgs], !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Domain processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Processes the domain of a values declaration
% We maintain a list of (Switch, Value) pairs as values_list(List)
% The integer mapping corresponds to the position of (Switch, Value) in List.
process_domain(F_in, File) :-
    F_in =.. [_ | [Switch, Values]],
    create_values_list(Switch, Values, CurrentValues),
    values_list(L),
    basics:append(L, CurrentValues, L1),
    assert(values_list(L1)),
    retract(values_list(L)).

% Creates a list of the current Values to be appended to the global values_list(List) 
create_values_list(_, [], []).
create_values_list(S, [V|Vs], [V|VLs]) :-
    create_values_list(S, Vs, VLs).

% Writes the type/2 and intrange/3 facts to the output file
:- table write_domain_intrange/4.
write_domain_intrange(F_out, OutFile) :-
    F_out =.. [_, S, V],
    basics:length(V, L),
    basics:ith(1, V, Start),
    basics:ith(L, V, End),
    num_vars:numbervars(S),
    open(OutFile, append, Handle),
    write(Handle, intrange(S, Start, End)), write(Handle, '.\n'),
    close(Handle).

% For each value V we find its position I in values_list
%     then we add I to the mapped domain list
make_numerical(_, [], []).
make_numerical(S, [V|Vs], [I|_Vs]) :-
    values_list(L),
    basics:ith(I, L, V),
    make_numerical(S, Vs, _Vs).

% Returns the list of int mappings Is from a list of values Vs
find_int_mappings([], []).

find_int_mappings([V|Vs], [I|Is]) :-
    find_int_mapping(V, I),
    find_int_mappings(Vs, Is).

% Returns the integer mapping I for V in the values_list
find_int_mapping(V, I) :-
    nonvar(V),
    values_list(L),
    basics:ith(I, L, V), !.

 % If V is not in the values_list, do not change V
find_int_mapping(V, V) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tabling definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Write table declarations for predicate F/N
:- table declare/3.
declare(F, N, OutFile) :-
    N1 is N+1,
    placeholders('', N1, P),
    str_cat(P,'lattice(or/3)', P1),
    open(OutFile, append, Handle),
    fmt_write(Handle, ':- table %s(%s).\n', args(F, P1)),
    close(Handle),
    true.

placeholders(S, 0, S).
placeholders(IS, N, OS):-
    N > 0,
    str_cat(IS, '_,', S),
    N1 is N-1,
    placeholders(S, N1, OS).