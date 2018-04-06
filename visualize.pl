%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Visualization using DOT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- export writeDotFile/2.

:- import ith/3 from basics.

writeDotFile(OSDD, DotFile) :-
    open(DotFile, write, Handle),
    write(Handle, ' digraph osdd {\n'),
    traverse(OSDD, Handle),
    write(Handle, '}\n'),
    close(Handle),
    true.

traverse(T, Handle) :-
    traverse(T, _, Handle).

traverse(Osdd, ID, Handle) :-
    usermod:'$unique_table'(Osdd, Node),
    (Node = 0
    ->
	write(Handle, ID),
	write(Handle, ' [label='),
	write(Handle, Node),
	write(Handle, '];\n')
    ;
        (Node = 1
	->
	    write(Handle, ID),
	    write(Handle, ' [label='),
	    write(Handle, Node),
	    write(Handle, '];\n')
	;
	    Node = tree(R, Es),
	    write(Handle, ID),
	    write(Handle, ' [label='),
	    write(Handle, R),
	    write(Handle, '];\n'),
	    traverse_edges(Es, ID, Handle)
	)
    ).
		
traverse_edges([], _, _).
traverse_edges([edge_subtree(C,T)|Es], ParentID, Handle) :-
    ChildID=_, % fresh
    write(Handle, ParentID), write(Handle, ' -> '), write(Handle, ChildID),
    write(Handle, ' [label='), write(Handle, '"'),writeDotConstraint(Handle, C), write(Handle, '"'), write(Handle, '];\n'),
    traverse(T, ChildID, Handle),
    traverse_edges(Es, ParentID, Handle).

writeDotConstraint(Handle, []) :-
    write(Handle, '').
writeDotConstraint(Handle, [C]) :-
    map_to_domain(C, C1),
    write1(Handle, C1).
writeDotConstraint(Handle, [C|R]) :-
    R \= [],
    map_to_domain(C, C1),
    write1(Handle, C1), write(Handle, ','),
    writeDotConstraint(Handle, R).

map_to_domain(X = Y, X1 = Y1) :-
    (integer(X)
    ->
	usermod:values_list(L),
	ith(X, L, X1)
    ;
        X = X1
    ),
    (integer(Y)
    ->
	usermod:values_list(L),
	ith(Y, L, Y1)
    ;
        Y = Y1
    ).

map_to_domain(X \= Y, X1 \= Y1) :-
    (integer(X)
    ->
	usermod:values_list(L),
	ith(X, L, X1)
    ;
        X = X1
    ),
    (integer(Y)
    ->
	usermod:values_list(L),
	ith(Y, L, Y1)
    ;
        Y = Y1
    ).

map_to_domain(X < Y, X1 < Y1) :-
    (integer(X)
    ->
	usermod:values_list(L),
	ith(X, L, X1)
    ;
        X = X1
    ),
    (integer(Y)
    ->
	usermod:values_list(L),
	ith(Y, L, Y1)
    ;
        Y = Y1
    ).

       
write1(Handle, X=Y) :-
    write(Handle, X=Y).
write1(Handle, X\=Y) :-
    write(Handle, X),
    %write(Handle, '\\\='),
    write(Handle, '\u2260\'),
    write(Handle, Y).
write1(Handle, X<Y) :-
    write(Handle, X<Y).
