/*
 * Usage: transform_file('input_file', 'output_file').
 */

% Read program in File, transform it and write to OutFile
transform_file(File, OutFile) :- !,
	seeing(OF),
	see(File),
	abolish_table_pred(declare/3),
	gensym:prepare(0),
	read_and_transform(OutFile),
	seen,
	see(OF).

% Read clauses from current inputstream and write transformed clauses
% to OutFile
read_and_transform(OutFile) :-
	read(Clause),
	(Clause == end_of_file
	->	true
	;	transform(Clause, XClause, OutFile),
		(XClause = none
		-> 	read_and_transform(OutFile)
		;
		num_vars:numbervars(XClause),
		writeln(XClause),
		write_clause(XClause, OutFile),
		read_and_transform(OutFile)
		)
	).

% write transformed clause (including facts) to outfile
% basically strips off the enclosing parentheses
write_clause(XClause, OutFile) :-
    open(OutFile, append, Handle),
    ((H :- B) = XClause
    ->
	write(Handle, H),
	write(Handle, ' :- '),
	write(Handle, B),
	write(Handle, '.\n')
    ;
    write(Handle, XClause),
    write(Handle, '.\n')
    ), 
    close(Handle).
    
% transform clauses and write table directives for transformed
% predicates in the head
transform((H_in :- B_in), (H_out :- B_out), File) :- !,
    functor(H_in, F, N),
    declare(F, N, File), % write table directives
    transform_pred(H_in, H_out, ExtraArgs),
    transform_body(B_in, B_out, ExtraArgs).

% transform facts except values/2 facts. For values/2 facts we define
% types and write them to file. We don't write table directives for
% transformed facts
transform(F_in, F_out, File) :-
    functor(F_in, F, _N),
    (F = values
    -> set_domain_intrange(F_in, File)
    ;
    % declare(F, N, File), don't have to table facts
    true),
    transform_pred(F_in, F_out, (Arg, Arg)).

% write type facts to OutFile
set_domain_intrange(Fin, OutFile) :-
    Fin =.. [values | [S, V]],
    functor(S, Switch, _),
    write_domain_intrange(Switch, V, OutFile).

:- table write_domain_intrange/3.
write_domain_intrange(S, V, OutFile) :-
    basics:length(V, L),
    gensym:gennum(Min),
    Max is Min + L - 1,
    open(OutFile, append, Handle),
    write(Handle, type(S, V)),
    write(Handle, '.\n'),
    write(Handle, intrange(S, Min, Max)),
    write(Handle, '.\n'),
    close(Handle),
    gensym:prepare(Max).

% Transforms a sequence of goals (G_in, Gs_in) as follows: Apply
% transform_body/3 on the single goal G_in to produce G_out, Recurse
% on Gs_in
transform_body((G_in, Gs_in), (G_out, Gs_out), (Arg_in, Arg_out)) :- !,
	transform_body(G_in, G_out, (Arg_in, Arg)),
	transform_body(Gs_in, Gs_out, (Arg, Arg_out)).

% Transform a single goal
transform_body(G_in, G_out, Args) :-
	transform_pred(G_in, G_out, Args).

% Transform predicates. The following three predicates don't get
% transformed
transform_pred(true, true, (Arg, Arg)) :- !.
transform_pred(=(_X, _Y), =(_X, _Y), (Arg, Arg)) :- !.
transform_pred(values(_X, _Y), values(_X, _Y), (Arg, Arg)) :- !.

% Transform atomic constraints of the form {C} in constraint language
transform_pred('{}'(C), constraint(C, Arg_in, Arg_out), (Arg_in, Arg_out)) :- !.

% Transform msw/3
transform_pred(msw(S,I,X), msw(S,I,X, Arg_in, Arg_out), (Arg_in, Arg_out)) :- !.

% Any other predicate is also transformed by adding two extra
% arguments for input OSDD and output OSDD
transform_pred(Pred_in, Pred_out, (Arg_in, Arg_out)) :-
	Pred_in =.. [P | Args],
	basics:append(Args, [Arg_in, Arg_out], NewArgs),
	Pred_out =.. [P | NewArgs].

% write table declarations for predicate F/N
:- table declare/3.
declare(F, N, OutFile) :-
    N1 is N+1,
    placeholders('', N1, P),
    str_cat(P,'lattice(or/3)', P1),
    open(OutFile, append, Handle),
    fmt_write(Handle, ':- table %s(%s).\n', args(F, P1)),
    close(Handle),
    true.

% Misc
placeholders(S, 0, S).
placeholders(IS, N, OS):-
    N > 0,
    str_cat(IS, '_,', S),
    N1 is N-1,
    placeholders(S, N1, OS).
