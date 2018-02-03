/*
 * Usage: transform_file('test_program.txt', 'test_program.osdd').
 */

%%%%%%
% Program transformation definitions
%%%%%%

%%%
% [transform_file/2]
% ---
% INPUT: a File to read from, an OutFile to write to 
% OUTPUT: writes the tranformed program to OutFile
%%%
transform_file(File, OutFile) :- !,
	seeing(OF),
	see(File),
	abolish_table_pred(declare/2),
	read_and_transform(OutFile),
	seen,
	see(OF).

%%%
% [read_and_transform/1]
% ---
% INPUT: a File to write to
% OUTPUT: writes the current Clause to the File
% ---
% If a clause is transformed to none, continue to the next clause.
%%%
read_and_transform(File) :-
	read(Clause),
	(Clause == end_of_file
	->	true
	;	transform(Clause, XClause),
		(XClause = none
		-> 	read_and_transform(File)
		;	num_vars:numbervars(XClause),
			writeln(XClause),
			open(File, append, Handle), 
			writeln(Handle, XClause), 
			close(Handle),
			read_and_transform(File)
		)
	).

%%%
% [transform/2]
% ---
% INPUT: a clause of the form H_in :- B_in
% OUTPUT: a rewritten clause H_out :- B_out
% ---
% First declare/2 writes a table directive for H_in,
% then the rule H_in :- B_in is rewritten by transforming H_in -> H_out followed by B_in -> B_out.
% The transformed predicates will include ExtraArgs which holds SDD subtrees as arguments.
%%%
transform((H_in :- B_in), (H_out :- B_out)) :- !,
	functor(H_in, F, N),
	declare(F, N),
	transform_pred(H_in, H_out, ExtraArgs),
	transform_body(B_in, B_out, ExtraArgs).

%%%
% INPUT: a fact F_in
% OUTPUT: a rewritten fact F_out
% ---
% Handles a fact F_in by tabling F/N,
% then calling transform_pred/3 on F_in to produce F_out.
% If a clause is a values/2 declaration set F_out to none and call set_domain(F_in).
%%%
transform(F_in, F_out) :-
	functor(F_in, F, N),
	(F = values
	->  set_domain(F_in),
		F_out = none
	;	declare(F, N),
		transform_pred(F_in, F_trans, (Arg)),
		F_out = (F_trans :- one(Arg))
	).

%%%
%
%%%
set_domain(X) :-
	X =.. [values | [S, Values]],
	assert(domain(S, Values)).

%%%
% [transform_body/3]
% ---
% INPUT: A sequence of goals (G_in, Gs_in)
% OUTPUT: A transformed sequence of goals (G_out, Gs_out)
% ---
% Transforms a sequence of goals (G_in, Gs_in) as follows:
%     Apply transform_pred/3 on the single goal G_in to produce G_out,
%     Recurse on Gs_in
%%%
transform_body((G_in, Gs_in), (G_out, Gs_out), (Arg_in, Arg_out)) :- !,
	transform_body(G_in, G_out, (Arg_in, Arg)),
	transform_body(Gs_in, Gs_out, (Arg, Arg_out)).

%%%
% INPUT: A goal G_in
% OUTPUT: A transformed goal G_out
% ---
% Calls tranform_pred/3 on G_in to produce G_out.
%%%
transform_body(G_in, G_out, Args) :-
	transform_pred(G_in, G_out, Args).

%%%
% [transform_pred/3]
% ---
% Base case.
%%%
transform_pred(true, true, (Arg, Arg)) :- !.

%%%
% INPUT: A constraint of the form {C}, an argument list (Arg_in, Arg_out)
% OUTPUT: Transformed constraint of the form contraint(C, Arg_in, Arg_out).
%%%
transform_pred('{}'(C), constraint(C, Arg_in, Arg_out), (Arg_in, Arg_out)) :- !.

%%%
% INPUT: An msw/3 predicate, an argument list (Arg_in, Arg_out)
% OUTPUT: Transformed msw which has the appended arguments
%%%
transform_pred(msw(S,I,X), msw(S,I,X, Arg_in, Arg_out), (Arg_in, Arg_out)) :- !.

%%%
% INPUT: A predicate Pred_in, an argument list (Arg_in, Arg_out)
% OUTPUT: Transformed predicate Pred_out
% ---
% Pred_out is Pred_in with (Arg_in, Arg_out) appended to the original arguments of the term.
%%%
transform_pred(Pred_in, Pred_out, (Args_in)) :-
	Pred_in =.. [P | Args],
	basics:append(Args, [Args_in], NewArgs),
	Pred_out =.. [P | NewArgs].

%%%
% [declare/2]
% ---
% INPUT: predicate F/N
% OUTPUT: writes table definition to OutFile
%%%
:- table declare/2.
declare(F, N) :-
    N1 is N+1,
    placeholders('', N1, P),
    str_cat(P,'lattice(or/3)', P1),
    fmt_write(':- table %s(%s).\n', args(F, P1)).
% [?] Should we pass OutFile from tranform_file/2 to handle where to write?

%%%%%%
% OSDD construction definitions
%%%%%%
/*
  TODO
  ---
  For every switch, assume we have a values declaration.
  Each domain specified in a values declaration corresponds to a type.
  We can either name the types using unique generated names, or simply
  use the set of values to stand in for its name.
  Each switch has the type corresponding to its values declaration.
  Each constant has the type corresponds to the declaration it is in.

  get_type: gets the type of any term.
  If it is a variable, then it returns the type attribute of that variable (if defined), and an unbound fresh variable otherwise.
  If it is a constant, it returns its type (based on the definitions above).
  Non-atomic terms are not supported, at least for now.

  add_constraint_to_edges(Ci, Subs, Co):
  Subs is a set of pairs of the form (X,C)
  When we find a node labeled X in Ci, its outgoing constraints are and-ed with C *provided* all variables in C have been seen in the root-to-X path in C.

  Define and/or.
*/

%%%
%
%%%
msw(S, I, X, C_in, C_out) :-
	functor(S, F, N),
	type(F, N, T),
	write_attr(X, type, T),   % revise to ensure X's attribute called "type" is correctly set to T
	write_attr(X, id, (S, I)),
	(contains(C_in, X)
	->  C_out = C_in
	;   read_attr(X, constraint, C),   % ensure read_attr never fails
	    create_osdd_one(One),
	    create_osdd(X, [(C, One)], Osdd),   % osdd: X -- C --> 1
	    and(C_in, Osdd, C_out)
	).

%%%
%
%%%	    
constraint((Lhs=Rhs), C_in, C_out) :-
	get_type(Lhs, T1),
	get_type(Rhs, T2),
	T1 = T2,
	write_attr(Lhs, constraint, (Lhs=Rhs)),
	write_attr(Rhs, constraint, (Lhs=Rhs)),
	add_constraint_to_edges(C_in, [(Lhs, (Lhs=Rhs)), (Rhs, (Lhs=Rhs))], C_out).


placeholders(S, 0, S).
placeholders(IS, N, OS):-
    N > 0,
    str_cat(IS, '_,', S),
    N1 is N-1,
    placeholders(S, N1, OS).

%%%
% [one/1]
%%%
%one(O) :- node(true, [], []).
one(leaf(1)).

% represent trees as tree(Root,[Edge1,Subtree1,Edge2,Subtree2,...])
make_tree(Root, Edges, Subtrees, tree(Root, L)) :-
    lists:zip(Edges,Subtrees,L).

% for now we have dummy predicates for and/or
and(T1, T2, and(T1,T2)).
or(T1, T2, or(T1,T2)).
