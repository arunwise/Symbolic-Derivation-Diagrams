%%%
%  transform/2
%  ---
%  INPUT: a clause of the form Hi :- Bi
%  OUTPUT: a rewritten clause Ho :- Bo
%  ---
%  First declare/2 writes a table directive for Hi,
%  then the rule Hi :- Bi is rewritten by transforming the head followed by the body.
%%%
transform((Hi :- Bi), (Ho :- Bo)) :- !,
   functor(Hi, F, N),
   declare(F, N),
   transform_pred(Hi, Ho, ExtraArgs),
   transform_body(Bi, Bo, ExtraArgs).

%%%
%  transform/2
%  ---
%  INPUT: a fact Fi
%  OUTPUT: a rewritten fact Fo
%%%
transform(Fi, Fo) :-
   functor(Fi, F, N),
   declare(F, N),
   transform_pred(Fi, Fo, (Arg, Arg)).

%%%
%
%%%
transform_body((Gi1, Gi2), (Go1, Go2), (Argi, Argo)) :- !,
	transform_body(Gi1, Go1, (Argi, A)),
	transform_body(Gi2, Go2, (A, Argo)).

%%%
%
%%%
transform_body(Gi, Go, Args) :-
	transform_pred(Gi, Go, Args).

transform_pred(true, true, (Arg, Arg)) :- !.
transform_pred('{}'(Ci), constraint(Ci, Argi, Argo), (Argi, Argo)) :- !.
transform_pred(msw(S,I,X), msw(S,I,X, Argi, Argo), (Argi, Argo)) :- !.
transform_pred(Predi, Predo, (Argi, Argo)) :-
	Predi =.. [P | Args],
	basics:append(Args, [Argi, Argo], NewArgs),
	Predo =.. [P | NewArgs].


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