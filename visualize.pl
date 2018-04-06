%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Visualization using DOT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- export writeDotFile/2.

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
