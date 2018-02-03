%
% Usage: transform('test_program.txt').
%

%%%
%  [transform/2]
%  ---
%  INPUT: a clause of the form H_in :- B_in
%  OUTPUT: a rewritten clause H_out :- B_out
%  ---
%  First declare/2 writes a table directive for H_in,
%  then the rule H_in :- B_in is rewritten by transforming H_in -> H_out followed by B_in -> B_out.
%  The transformed predicates will include ExtraArgs which holds SDD subtrees as arguments.
%%%
transform((H_in :- B_in), (H_out :- B_out)) :- !,
   functor(H_in, F, N),
   declare(F, N),
   transform_pred(H_in, H_out, ExtraArgs),
   transform_body(B_in, B_out, ExtraArgs).

%%%
%  INPUT: a fact F_in
%  OUTPUT: a rewritten fact F_out
%  ---
%  Handles a fact F_in by tabling F/N,
%  then calling transform_pred/3 on F_in to produce F_out.
%%%
transform(F_in, F_out) :-
   functor(F_in, F, N),
   declare(F, N),
   transform_pred(F_in, F_out, (Arg, Arg)).  % [?] Should a fact f(X) be transformed to F(X, Arg, Arg) or F(X, Arg)?  As implemented it is F(X, Arg, Arg).

%%%
%  [transform_body/3]
%  ---
%  INPUT: A sequence of goals (G_in, Gs_in)
%  OUTPUT: A transformed sequence of goals (G_out, Gs_out)
%  ---
%  Transforms a sequence of goals (G_in, Gs_in) as follows:
%      Apply transform_pred/3 on the single goal G_in to produce G_out,
%      Recurse on Gs_in
%%%
transform_body((G_in, Gs_in), (G_out, Gs_out), (Arg_in, Arg_out)) :- !,
	transform_body(G_in, G_out, (Arg_in, Arg)),
	transform_body(Gs_in, Gs_out, (Arg, Arg_out)).

%%%
%  INPUT: A goal G_in
%  OUTPUT: A transformed goal G_out
%  ---
%  Calls tranform_pred/3 on G_in to produce G_out.
%%%
transform_body(G_in, G_out, Args) :-
	transform_pred(G_in, G_out, Args).

%%%
%  [transform_pred/3]
%  ---
%  INPUT:
%  OUTPUT:
%  ---
%
%%%
transform_pred(true, true, (Arg, Arg)) :- !.

%%%
%  INPUT:
%  OUTPUT:
%  ---
%%%
transform_pred('{}'(C), constraint(C, Arg_in, Arg_out), (Arg_in, Arg_out)) :- !.

%%%
%  INPUT:
%  OUTPUT:
%%%
transform_pred(msw(S,I,X), msw(S,I,X, Arg_in, Arg_out), (Arg_in, Arg_out)) :- !.

%%%
%  INPUT:
%  OUTPUT:
%  ---
%%%
transform_pred(Pred_in, Pred_out, (Arg_in, Arg_out)) :-
	Pred_in =.. [P | Args],
	basics:append(Args, [Arg_in, Arg_out], NewArgs),
	Pred_out =.. [P | NewArgs].


%%%%%%%%%%%%%%%%
transform(File) :-
	seeing(OF),
	see(File),
	abolish_table_pred(declare/2),
	read_and_transform,
	seen,
	see(OF).

read_and_transform :-
	read(Clause),
	(Clause == end_of_file
	->  true
	;   transform(Clause, XClause),
	    num_vars:numbervars(XClause),
	    writeln(XClause),
	    read_and_transform
	).

:- table declare/2.
declare(F, N) :-
	M is N+2,
	fmt_write(':- table %s/%d\n', f(F, M)).

msw(Sw, Inst, X, Ci, Co) :-
	functor(Sw, F, N),
	type(F, N, T),
	write_attr(X, type, T),   % revise to ensure X's attribute called "type" is correctly set to T
	write_attr(X, id, (Sw, Inst)),
	(contains(Ci, X)
	->  Co = Ci
	;   read_attr(X, constraint, C),   % ensure read_attr never fails
	    create_osdd_one(One),
	    create_osdd(X, [(C, One)], Osdd), 	    % osdd:   X -- C --> 1
	    and(Ci, Osdd, Co)
	).
	    
constraint((Lhs=Rhs), Ci, Co) :-
	get_type(Lhs, T1),
	get_type(Rhs, T2),
	T1 = T2,
	write_attr(Lhs, constraint, (Lhs=Rhs)),
	write_attr(Rhs, constraint, (Lhs=Rhs)),
	add_constraint_to_edges(Ci, [(Lhs, (Lhs=Rhs)), (Rhs, (Lhs=Rhs))], Co).
	

/*
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