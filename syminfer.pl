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
% Query processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Maps the domain of an exported query to the integer representation
map_domain(Q, _Q) :-
    values_list(L),
    Q =.. [F | Args],
    map_args(Args, _Args, L),
    _Q =.. [F | _Args].

% Maps an individual argument to it's corresponding interger representation
map_args([], [], _).
map_args([Arg|Args], [_Arg|_Args], L) :-
    basics:ith(_Arg, L, Arg),
    map_args(Args, _Args, L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraint processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Definition of msw constraint processing.
%     First set the type of X to be the domain of S,
%     Then set the ID of X to be the pair (S, I),
%     If X is in C_in ...?
%     Otherwise, construct the OSDD rooted at X.
msw(S, I, X, C_in, C_out) :-
%   functor(S, F, N),
    values(S, T),
    set_type(X, T),
    set_id(X, (S, I)),
    (contains(C_in, X)
    ->  C_out = C_in
    ;   read_constraint(X, C),
        one(One),
        make_tree(X, [C], [One], Osdd),   % osdd: X -- C --> 1
        and(C_in, Osdd, C_out)
    ).

% Definition of atomic constraint processing.
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
    ->  set_constraint(Lhs, [Lhs=Rhs])
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, [Lhs=Rhs])
    ;   true
    ),
    update_edges(C_in, Lhs, Lhs=Rhs, C_tmp),
    update_edges(C_tmp, Rhs, Lhs=Rhs, C_out).

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
    ->  set_constraint(Lhs, [Lhs\=Rhs])
    ;   true
    ),
    (var(Rhs) 
    ->  set_constraint(Rhs, [Lhs\=Rhs])
    ;   true),
    update_edges(C_in, Lhs, Lhs\=Rhs, C_tmp),
    update_edges(C_tmp, Rhs, Lhs\=Rhs, C_out).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Attribute processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Type attribute handler
type_handler(T, X) :-
    (var(X) 
    ->  (get_attr(X, type, _T)
        ->  T = _T     % X is also attributed variable
        ;   true       % X is not attributed variable
        )
    ;   atomic(X),     % [?] Is this redundant?
        %values(_S, T),
        basics:member(X, T)
    ).

% ID attribute handler
% Nothing needs to be done in id attribute handler
id_handler(I, X) :- true.

% Constraint attribute handler.
% If X is a variable which has a constraint list CX,
%     merge C and CX and see if the new list is satisfiable w.r.t. the domain of X,
%     apply the new constraints and restricted domain as attributes of X.
% Else X is a constant,
%     and X unifies when X is a member of C.
% ---
% TESTS: set_constraint(X, [a = X, X \= b]), set_constraint(Y, [Y = d]), set_type(Y, [c, e, a]), X=Y.  [no]
%        set_constraint(X, [X \= b, a = X]), set_constraint(Y, [Y \= e, Y=Z]), set_type(Y, [c, e, a]), X=Y.  [yes]
%        set_constraint(X, [X \= b, a \= X]), set_constraint(Y, [Y \= e, Y \= c]), set_type(Y, [c, e, a]), X=Y.  [no]
%        set_constraint(X, [X \= b, a = X, X \= Y]), set_constraint(Y, [Y \= e, Y=Z]), set_type(Y, [c, e, a]), X=Y.  [no]
constraint_handler(C, X) :-
    writeln('START constraint_handler'), write(C),
    (var(X), get_attr(X, constraint, CX)
    ->  listutil:merge(C, CX, _C), 
        write('Merged constraints: '), writeln(_C), writeln('END constraint_handler\n'),
        read_type(X, T),
        satisfiable(X, _C, T, T_restricted),
        put_attr(X, type, T_restricted),
        put_attr(X, constraint, _C)
    ;   basics:member(X, C)
    ).

% An empty list of constraints is satisfiable given that the domain is not empty.
satisfiable(_, [], T, T) :- T \= [].

% Handles equality constraints.
% If the constraint is of the form X = a (or a = X) and a is in the domain of X,
%     restrict the domain of X to be a
% Else if the constraint is of the form X = Y (or Y = X),
%     continue without modifying the domain of X
% Else,
%     fail.
satisfiable(X, [Lhs = Rhs|Cs], T_in, T_out) :- 
    writeln('START satisfiable'), write('LHS: '), writeln(Lhs), write('RHS: '), writeln(Rhs), write('Domain: '), writeln(T_in),
    (X = Lhs
    ->  (var(Rhs)
        ->  T = T_in
        ;   basics:member(Rhs, T_in), T = Rhs  % If Rhs is not a variable, check if it is in the domain of T, if so restrict T to Rhs
        )
    ;   (X = Rhs
        ->  (var(Lhs)
            ->  T = T_in
            ;   basics:member(Lhs, T_in), T = Lhs
            )
        ;   false
        )
    ),
    write('Domain Out: '), writeln(T), writeln('END satisfiable\n'),
    satisfiable(X, Cs, T, T_out).

% Handles inequality constraints.
% If the constraint is of the form X \= a (or a \= X) and a is in the domain of X,
%     remove a from the domain of X
% Else if the constraint is of the form X \= Y (or Y \= X), 
%     continue without modifying the domain of X
% Else,
%     fail.
satisfiable(X, [Lhs \= Rhs|Cs], T_in, T_out) :- 
    writeln('START satisfiable'), write('LHS: '), writeln(Lhs), write('RHS: '), writeln(Rhs), write('Domain: '), writeln(T_in),
    (X = Lhs
    ->  (var(Rhs)
        ->  (Rhs = Lhs
            ->  false
            ;   T = T_in
            )
        ;   (basics:member(Rhs, T_in)
            ->  basics:select(Rhs, T_in, T)
            ;   T = T_in
            )
        )
    ;   (X = Rhs
        ->  (var(Lhs)
            ->  (Lhs = Rhs
                ->  false
                ;   T = T_in
                )
            ;   (basics:member(Lhs, T_in)
                ->  basics:select(Lhs, T_in, T)
                ;   T = T_in
                )
            )
        ;   false
        )
    ),
    write('Domain Out: '), writeln(T), writeln('END satisfiable\n'),
    satisfiable(X, Cs, T, T_out).

% Display handlers
% Assert display_attributes(on) to display the value of the attribute
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

% Sets type attribute of a variable to the domain to the variable.
set_type(X, T) :-
    var(X),
    (get_attr(X, type, T1)
    ->  T = T1  % We can't change type of a variable
    ;   put_attr(X, type, T)
    ).

% Sets id attribute of a random variable to (S, I).
% Where S is the switch name and I is the instance.
set_id(X, (S, I)) :-
    var(X),
    (get_attr(X, id, (S1, I1))
    ->  S=S1, I=I1  % We can't change id of a variable
    ;   put_attr(X, id, (S, I))
    ).

% Sets constraint attribute of a variable.
% If X already has a constraint list and C is not already in the list, 
%     append C to the constraint list.
% Otherwise initialize the constraint list of X to C.
set_constraint(X, C) :-
    var(X),
    (get_attr(X, constraint, C1)
    ->  (basics:member(C, C1)
        ->  true
        ;   basics:append(C1, C, C2),
            put_attr(X, constraint, C2)
        )
    ;   put_attr(X, constraint, C)
    ).

% Reads constraint attribute, if it doesn't exist set to empty constraint.
read_constraint(X, C) :-
    var(X),
    (get_attr(X, constraint, C)
    ->  true
    ;   C=[],
        put_attr(X, constraint, C)
    ).

% Reads type attribute.
% If X is a variable and its type is not set, we set it to an unbound value.
read_type(X, T) :-
    var(X),
    (get_attr(X, type, T)
    ->  true
    ;   var(T),
        put_attr(X, type, T)
    ).

% Lookup type of a constant by searching for a type T which X is an element of.
% NOTE: Should set T to the greatest superset.
lookup_type(X, T) :-
    atomic(X),
    values(_, T),
    basics:member(X, T), !.

% Reads id attribute, if it doesn't exist set it to unbound pair of variables.
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
and(leaf(1), _T, _T) :- !.
and(_T, leaf(1), _T) :- !.
and(leaf(0), _T, leaf(0)) :- !.
and(_T, leaf(0), leaf(0)) :- !.
or(leaf(1), _T, leaf(1)) :- !.
or(_T, leaf(1), leaf(1)) :- !.
or(leaf(0), _T, _T) :- !.
or(_T, leaf(0), _T) :- !.
and(_T1, _T2, and(_T1, _T2)).
or(_T1, _T2, or(_T1, _T2)).

% Check if OSDD contains a variable X
contains(tree(Y, _), X) :- X==Y, !.
contains(tree(Y, L), X) :-
    X \== Y,
    contains(L, X).
contains([(_C,T)|R], X) :-
    (contains(T, X) 
    -> true
    ;  contains(R, X)).
contains(and(T1, _T2), X) :-
    contains(T1, X), !.
contains(and(_T1, T2), X) :-
    contains(T2, X), !.
contains(or(T1, _T2), X) :-
    contains(T1, X), !.
contains(or(_T1, T2), X) :-
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

% Computes the ordering relation O between X and Y given constraints C
% O can take the following values {lt, gt, eq, nc} where:
%     lt <=> X < Y
%     gt <=> X > Y
%     eq <=> X == Y
%     nc <=> an order can not be determined
% ---
% TESTS: set_type(X, [a, b, c]), set_type(Y, [a, b, c]), ord_constrvars(X, Y, [c < X, Y < b], O).  [nc]
%        set_type(X, [a, b, c]), set_type(Y, [a, b, c]), ord_constrvars(X, Y, [X = a, X < Y, c = Y], O).  [lt]
%        set_type(X, [a, b, c]), set_type(Y, [a, b, c]), ord_constrvars(X, Y, [Y < Z, Y < X, X = a], O).  [gt]
%        set_type(X, [a, b, c]), set_type(Y, [a, b, c]), ord_constrvars(X, Y, [X = Y, b = Y], O).  [eq]
ord_constrvars(X, Y, C, O) :- 
    write('X: '), writeln(X),
    write('Y: '), writeln(Y),
    write('C: '), writeln(C),
    write('O: '), writeln(O),
    read_type(X, TX),
    read_type(Y, TY),
    process_constraints(X, TX, Y, TY, [], C, O).

% Processes the constraint list
process_constraints(_, _, _, _, _, [], _) :- !.

process_constraints(X, XT, Y, YT, Vars, [Lhs = Rhs|Cs], O) :-
    writeln(Lhs = Rhs),
    (((Lhs = X, Rhs = Y); (Lhs = Y, Rhs = X))
    ->  O = eq
    ;   process_constraints(X, XT, Y, YT, Vars, Cs, O)
    ).

process_constraints(X, XT, Y, YT, Vars, [Lhs \= Rhs|Cs], O) :-
    writeln(Lhs \= Rhs),
    process_constraints(X, XT, Y, YT, Vars, Cs, O).

process_constraints(X, XT, Y, YT, Vars, [Lhs < Rhs|Cs], O) :-
    writeln(Lhs < Rhs),
    (Lhs = X, Rhs = Y, Lhs \== Rhs
    ->  O = lt
    ;   (Lhs = Y, Rhs = X, Lhs \== Rhs
        ->  O = gt
        ;   process_constraints(X, XT, Y, YT, Vars, Cs, O)
        )
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Misc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
display_attributes(on).  % control display of attributes

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Visualization using DOT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
writeDot(OSDD, DotFile) :-
    paths(OSDD, Paths),
    current_prolog_flag(write_attributes, F),
    set_prolog_flag(write_attributes, ignore),
    open(DotFile, write, Handle),
    write(Handle, 'strict digraph osdd {\n'),
    writeDotPaths(Paths, Handle),
    write(Handle, '}\n'),
    close(Handle),
    set_prolog_flag(write_attributes, F).

writeDotPaths([], _H).
writeDotPaths([P|R], Handle) :-
    writeDotPath(P, Handle),
    writeDotPaths(R, Handle).

writeDotPath([(Var,Label)], Handle) :-
    (Label=0;Label=1),
    write(Handle, Var),
    write(Handle, ' [label='),
    write(Handle, Label),
    write(Handle, '];\n').

writeDotPath([(V1,L1), E| R], Handle) :-
    R = [(V2,_L2)|_],
    write(Handle, V1), write(Handle, ' [label='), write(Handle, L1), write(Handle, '];\n'),
    write(Handle, V1), write(Handle, ' -> '), write(Handle, V2), write(Handle, ' [label='), write(Handle, '"'),writeDotConstraint(Handle, E), write(Handle, '"'), write(Handle, '];\n'),
    writeDotPath(R, Handle).

writeDotConstraint(Handle, null) :-
    write(Handle, '').
writeDotConstraint(Handle, []) :-
    write(Handle, '').
writeDotConstraint(Handle, [C]) :-
    write1(Handle, C).
writeDotConstraint(Handle, [C|R]) :-
    R \= [],
    write1(Handle, C), write(Handle, ','),
    writeDotConstraint(Handle, R).

write1(Handle, X=Y) :-
    write(Handle, X=Y).
write1(Handle, X\=Y) :-
    write(Handle, X), write(Handle, '\\\='), write(Handle, Y).
write1(Handle, X<Y) :-
    write(Handle, X<Y).

%% collect paths in an OSDD
% paths are simply sequences (lists) of node,edge,node... values nodes
% are represented by pairs (VarName, Label). This is needed because,
% otherwise leaves "and", "or" nodes will get combined.
paths(leaf(X), [[(_Y,X)]]). % fresh variable Y helps distinguish from other nodes with same value of X

paths(and(T1, T2), P) :-
    paths(T1, P1),
    addprefix([(Y,and),null], P1, P1A),
    paths(T2, P2),
    addprefix([(Y,and),null], P2, P2A),
    basics:append(P1A, P2A, P).

paths(or(T1, T2), P) :-
    paths(T1, P1),
    addprefix([(Y,or),null], P1, P1A),
    paths(T2, P2),
    addprefix([(Y,or),null], P2, P2A),
    basics:append(P1A, P2A, P).

paths(tree(Root, Subtrees), P) :-
    paths1(Root, Subtrees, [], P).

paths1(_Root, [], _P, _P).
paths1(Root, [(E,T)|R], Pin, Pout) :-
    paths(T, P1),
    addprefix([(Root,Root),E], P1, P2),
    basics:append(Pin, P2, P3),
    paths1(Root, R, P3, Pout).

addprefix(_L, [], []).
addprefix(L, [P|R], [P1|RR]) :-
    basics:append(L, P, P1),
    addprefix(L, R, RR).
