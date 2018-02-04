/*
 * Usage: transform_file('test_program.txt', 'test_program.osdd').
 */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Program transformation definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- import get_attr/3, put_attr/3 from machine.

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
		transform_pred(F_in, F_out, (Arg, Arg))
	).

%%%
%
%%%
set_domain(X) :-
	X =.. [values | [S, Values]],
	assert(type(S, Values)).

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
transform_pred(Pred_in, Pred_out, (Arg_in, Arg_out)) :-
	Pred_in =.. [P | Args],
	basics:append(Args, [Arg_in, Arg_out], NewArgs),
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OSDD construction definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
  TODO
  ---
  For every switch, assume we have a values declaration.
  Each domain specified in a values declaration corresponds to a type.
  We can either name the types using unique generated names, or simply
  use the set of values to stand in for its name.
  Each switch has the type corresponding to its values declaration.
  Each constant has the type corresponding to the declaration it is in.

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
	type(S, T),
	set_type(X, T),   % revise to ensure X's attribute called "type" is correctly set to T
	set_id(X, (S, I)),
	(contains(C_in, X)
	->  C_out = C_in
	;   read_constraint(X, C),
	    one(One),
	    make_tree(X, [C], [One], Osdd),   % osdd: X -- C --> 1
	    and(C_in, Osdd, C_out)
	).

%%%
%
%%%	    
constraint((Lhs=Rhs), C_in, C_out) :-
	get_type(Lhs, T1),
	get_type(Rhs, T2),
	T1 = T2,
	set_constraint(Lhs, (Lhs=Rhs)),
	set_constraint(Rhs, (Lhs=Rhs)),
	add_constraint_to_edges(C_in, [(Lhs, (Lhs=Rhs)), (Rhs, (Lhs=Rhs))], C_out).

%%%
% [set_attribute/2]
% ---
% All follow the same logic...
%%%

% set id if it doesn't exist, otherwise unify with existing id
set_id(X, (S, I)) :-
	read_id(X, (S1, I1)),
	S1=S, I1=I.

% return id if it exists, otherwise create id with fresh variables
read_id(X, (S, I)) :-
	(get_attr(X, id, (S, I))
	->	true
	;	put_attr(X, id, (S1, I1)),
		S1=S, I1=I % [?] Are fresh variables needed?
	).

set_type(X, T) :-    
	read_type(X, T1),
	T1=T.

read_type(X, T) :-
	(get_attr(X, type, T)
	->	true
	;	put_attr(X, type, T1),
		T1=T
	).

set_constraint(X, C) :-
	read_constraint(X, C1),
	(basics:member(C, C1)
	->  true
	;   basics:append(C1, [C], C2),
	    put_attr(X, constraint, C2)
	).

read_constraint(X, C) :-
	(get_attr(X, constraint, C)
	->	true
	;	C=[]
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tree Structure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
one(leaf(1)).

% represent trees as tree(Root,[Edge1,Subtree1,Edge2,Subtree2,...])
make_tree(Root, Edges, Subtrees, tree(Root, L)) :-
    myzip(Edges,Subtrees,L).

contains(X, tree(Y, _)) :-
    X==Y.
contains(X, tree(Y, L)) :-
    X \== Y,
    contains(X, L).

contains(X, [(_C,T)|R]) :-
    (contains(X, T) 
    -> true
    ;  contains(X, R)).

myzip([], [], []).
myzip([A|AR], [B|BR], [(A,B)|R]) :-
    myzip(AR, BR, R).

% for now we have dummy predicates for and/or
and(T1, T2, and(T1,T2)).
or(T1, T2, or(T1,T2)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Misc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
placeholders(S, 0, S).
placeholders(IS, N, OS):-
    N > 0,
    str_cat(IS, '_,', S),
    N1 is N-1,
    placeholders(S, N1, OS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TESTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%
% Usage: test_msw(gene, E, A, C, F).
% To be used after transforming the test program and asserting the type and ID.
%%%
test_msw(S, I, X, C_in, C_out) :-
	functor(S, F, N),
	type(S, T),
	set_type(X, T),
	set_id(X, (S, I)),
	get_attr(X, type, Type),
	get_attr(X, id, ID),
	write('Attribute <test> is '), writeln(Type),
	write('Attribute <id> is '), writeln(ID).

%%%
% Tests constraint attribute setting.
%%%
test_constraint_attribute :-
	set_constraint(Lhs, (lhs=b)),
	set_constraint(Lhs, (lhs=b)),  % Do not add redundant constraint
	set_constraint(Lhs, (lhs<a)),
	set_constraint(Rhs, (rhs=b)),
	set_constraint(Rhs, (rhs>a)),
	set_constraint(Rhs, (rhs>c)),
	get_attr(Lhs, constraint, C_Lhs),
	get_attr(Rhs, constraint, C_Rhs),
	write('Lhs: Attribute <constraint> is '), writeln(C_Lhs),
	write('Rhs: Attribute <constraint> is '), writeln(C_Rhs).