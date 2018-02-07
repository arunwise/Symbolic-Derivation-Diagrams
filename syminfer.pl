/*
 *  Code for symbolic inference using OSDDs.
 */ 
:- import get_attr/3, put_attr/3, install_verify_attribute_handler/4, install_attribute_portray_hook/3 from machine.

:- install_verify_attribute_handler(type, AttrValue, Target, type_handler(AttrValue, Target)).
:- install_verify_attribute_handler(id, AttrValue, Target, id_handler(AttrValue, Target)).
:- install_verify_attribute_handler(constraint, AttrValue, Target, constraint_handler(AttrValue, Target)).

:- install_attribute_portray_hook(type, Attr, display_type(Attr)).
:- install_attribute_portray_hook(id, Attr, display_id(Attr)).
:- install_attribute_portray_hook(constraint, Attr, display_constr(Attr)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraint processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% Definition of msw constraint processing.
%     First set the type of X to be the domain of S,
%     Then set the ID of X to be the pair (S, I),
%     If X is in C_in ...?
%     Otherwise, construct the OSDD rooted at X.
%
msw(S, I, X, C_in, C_out) :-
%   functor(S, F, N),
    type(S, T),
    set_type(X, T),
    set_id(X, (S, I)),
    (contains(C_in, X)
    ->  C_out = C_in
    ;   read_constraint(X, C),
        one(One),
        make_tree(X, [C], [One], Osdd),   % osdd: X -- C --> 1
        and(C_in, Osdd, C_out)
    ).

%
% Definition of atomic constraint processing.
%
constraint(Lhs=Rhs, C_in, C_out) :-
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    (var(Lhs) 
    ->  read_type(Lhs, T1)
    ;   lookup_type(Lhs, T1)
    ),
    (var(Rhs) 
    ->  read_type(Rhs, T2)
    ;   lookup_type(Rhs, T2)
    ),
    T1 = T2,
    (var(Lhs) 
    ->  set_constraint(Lhs, Lhs=Rhs)
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, Lhs=Rhs)
    ;   true
    ),
    update_edges(C_in, Lhs, Lhs=Rhs, C_tmp),
    update_edges(C_tmp, Rhs, Lhs=Rhs, C_out).
    %% (var(Lhs) ->
    %%   set_constraint(Lhs, Lhs=Rhs),
    %%      update_edges(C_in, Lhs, Lhs=Rhs, C_tmp)
    %% ; true),
    %% (var(Rhs) ->
    %%   set_constraint(Rhs, Lhs=Rhs),
    %%   update_edges(C_tmp, Rhs, Lhs=Rhs, C_out)
    %% ; true).

constraint(Lhs\=Rhs, C_in, C_out) :-
    (var(Lhs); var(Rhs)),  % at most one of Lhs and Rhs can be a ground term
    (var(Lhs) 
    ->  read_type(Lhs, T1)
    ;   lookup_type(Lhs, T1)
    ),
    (var(Rhs) 
    ->  read_type(Rhs, T2)
    ;   lookup_type(Rhs, T2)
    ),
    T1 = T2,
    (var(Lhs) 
    ->  set_constraint(Lhs, Lhs\=Rhs)
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, Lhs\=Rhs)
    ;   true),
    update_edges(C_in, Lhs, Lhs\=Rhs, C_tmp),
    update_edges(C_tmp, Rhs, Lhs\=Rhs, C_out).
    %% (var(Lhs) ->
    %%   set_constraint(Lhs, Lhs\=Rhs),
    %%   update_edges(C_in, Lhs, Lhs\=Rhs, C_tmp)
    %% ; true),
    %% (var(Rhs) ->
    %%   set_constraint(Rhs, Lhs\=Rhs),
    %%   update_edges(C_tmp, Rhs, Lhs\=Rhs, C_out)   
    %% ; true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Attribute processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% Type attribute handler
%
type_handler(T, X) :-
    (var(X) 
    ->  (get_attr(X, type, _T)
        ->  T = _T     % X is also attributed variable
        ;   true       % X is not attributed variable
        )
    ;   atomic(X),     % [?] Is this redundant?
        %type(_S, T),
        basics:member(X, T)
    ).

%
% ID attribute handler
% Nothing needs to be done in id attribute handler
%
id_handler(_I, _X) :- true.

%
% Constraint attribute handler
% Constraints will be re-written due to unification
% NOTE: Going forward we may need to invoke a constraint solver to check satisfiability
%
constraint_handler(_C, _X) :- true.

%
% Display handlers
% Assert display_attributes(on) to display the value of the attribute
%
display_type(A) :-
    (display_attributes(on) 
    ->  write(A)
    ;   true
    ).

display_id(A) :-
    (display_attributes(on) 
    ->  write(A)
    ;   true
    ).

display_constr(A) :-
    (display_attributes(on)
    ->  write(A)
    ;   true
    ).

%
% Sets type attribute of a variable to the domain to the variable.
%
set_type(X, T) :-
    var(X),
    (get_attr(X, type, T1)
    ->  T = T1  % We can't change type of a variable
    ;   put_attr(X, type, T)
    ).

%
% Sets id attribute of a random variable to (S, I).
% Where S is the switch name and I is the instance.
%
set_id(X, (S, I)) :-
    var(X),
    (get_attr(X, id, (S1, I1))
    ->  S=S1, I=I1  % We can't change id of a variable
    ;   put_attr(X, id, (S, I))
    ).

%
% Sets constraint attribute of a variable.
% If X already has a constraint list and C is not already in the list, 
%     append C to the constraint list.
% Otherwise initialize the constraint list of X to [C].
%
set_constraint(X, C) :-
    var(X),
    (get_attr(X, constraint, C1)
    ->  (basics:member(C, C1)
        ->  true
        ;   basics:append(C1, [C], C2),
            put_attr(X, constraint, C2)
        )
    ;   put_attr(X, constraint, [C])
    ).

%
% Reads constraint attribute, if it doesn't exist set to empty constraint.
%
read_constraint(X, C) :-
    var(X),
    (get_attr(X, constraint, C)
    ->  true
    ;   C=[],
        put_attr(X, constraint, C)
    ).

%
% Reads type attribute.
% If X is a variable and its type is not set, we set it to an unbound value.
%
read_type(X, T) :-
    var(X),
    (get_attr(X, type, T)
    ->  true
    ;   var(T),
        put_attr(X, type, T)
    ).

%
% Lookup type of a constant by searching for a type T which X is an element of.
% NOTE: Should set T to the greatest superset.
%
lookup_type(X, T) :-
    atomic(X),
    type(_, T),
    basics:member(X, T), !.

%
% Reads id attribute, if it doesn't exist set it to unbound pair of variables.
%
read_id(X, (S, I)) :-
    var(X),
    (get_attr(X, id, (S, I))
    ->  true
    ;   var(S), var(I),  % [?] Is this needed?
        put_attr(X, id, (S, I))
        %S1=S, I1=I % [?] Are fresh variables needed?
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tree Structure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
one(leaf(1)).
zero(leaf(0)).

% represent trees as tree(Root,[(Edge1, Subtree1), (Edge2, Subtree2), ...])
make_tree(Root, Edges, Subtrees, tree(Root, L)) :-
    myzip(Edges, Subtrees, L).

% for now we have dummy predicates for and/or
and(leaf(1), T, T) :- !.
and(T, leaf(1), T) :- !.
and(leaf(0), T, leaf(0)) :- !.
and(T, leaf(0), leaf(0)) :- !.
or(leaf(1), T, leaf(1)) :- !.
or(T, leaf(1), leaf(1)) :- !.
or(leaf(0), T, T) :- !.
or(T, leaf(0), T) :- !.
and(T1, T2, and(T1,T2)).
or(T1, T2, or(T1,T2)).

% Check if OSDD contains a variable X
contains(tree(Y, _), X) :- X==Y, !.
contains(tree(Y, L), X) :-
    X \== Y,
    contains(L, X).
contains([(_C,T)|R], X) :-
    (contains(T, X) 
    -> true
    ;  contains(R, X)).
contains(and(T1, T2), X) :-
    contains(T1, X), !.
contains(and(T1, T2), X) :-
    contains(T2, X), !.
contains(or(T1, T2), X) :-
    contains(T1, X), !.
contains(or(T1, T2), X) :-
    contains(T2, X), !.

myzip([], [], []).
myzip([A|AR], [B|BR], [(A,B)|R]) :-
    myzip(AR, BR, R).

update_edges(C_in, X, _C, C_out) :-
    atomic(X),
    C_in = C_out.
update_edges(and(T1,T2), X, C, and(T1out,T2out)) :-
    var(X),
    update_edges(T1, X, C, T1out),
    update_edges(T2, X, C, T2out).
update_edges(or(T1,T2), X, C, or(T1out,T2out)) :-
    var(X),
    update_edges(T1, X, C, T1out),
    update_edges(T2, X, C, T2out).
update_edges(tree(X, [(C1,S)]), Y, C, tree(X, [(C2, S)])) :-
    X==Y,
    basics:append(C1, [C], C2), !.
update_edges(tree(X, S1), Y, C, tree(X, S2)) :-
    X \== Y,
    update_edges(S1, Y, C, S2).
update_edges([], _Y, _C, []).
update_edges([(_E, T) | R], Y, C, [(_E, T1)| R1]) :-
    update_edges(T, Y, C, T1),
    update_edges(R, Y, C, R1).
update_edges(leaf(_X), _Y, _C, leaf(_X)).

% ordering relation for switch/instance pairs
ord((S1, I1), (S2, I2), C, O) :-
    atomic(I1), atomic(I2),
    (I1 @< I2
    ->
	O = lt
    ;
        (I1 @= I2
	->
	    ord(S1, S2, C, O)
	;
	    O = gt
	)
    ).

ord(S1, S2, C, O) :-
    functor(S1, F1, _),
    functor(S2, F2, _),
    (F1 @< F2
    ->
	O = lt
    ;
        (F1 @= F2
	->
	    S1 =.. [F1| Args1],
	    S2 =.. [F1| Args2],
	    ord(Args1, Args2, C, O)
	;
	    O = gt
	)
    ).

ord([A1 | A1Rest], [A2 | A2Rest], C, O) :-
    % check whether constraint formula (which ?) entails A1 < A2 or A1
    % > A2 or there is no ordering
    true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Misc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
display_attributes(off).  % control display of attributes