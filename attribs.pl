%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Attribute processing definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- import get_attr/3, put_attr/3, install_verify_attribute_handler/4, install_attribute_portray_hook/3 from machine.

:- install_verify_attribute_handler(type, AttrValue, Target, type_handler(AttrValue, Target)).
:- install_verify_attribute_handler(id, AttrValue, Target, id_handler(AttrValue, Target)).

:- install_attribute_portray_hook(type, Attr, display_type(Attr)).
:- install_attribute_portray_hook(id, Attr, display_id(Attr)).

:- export set_type/2, set_id/2, read_type/2, read_id/2.

% Type attribute handler
type_handler(T, X) :-
    (var(X) 
    ->  (get_attr(X, type, _T)
        ->  T = _T     % X is also attributed variable
        ;   true       % X is not attributed variable
        )
    ;   nonvar(X),
        basics:member(X, T)
    ).

% Attribute handlers
id_handler(_,_).

% Sets type attribute of a variable to the domain to the variable.
set_type(X, T) :-
    var(X),
    (get_attr(X, type, T1)
    ->  T = T1  % We can't change type of a variable
    ;   put_attr(X, type, T)
    ).

% Sets id attribute of a random variable to (S, I).
% Where S is the switch name and I is the instance.
set_id(X, id(S, I)) :-
    var(X),
    (get_attr(X, id, id(S1, I1))
    ->  S=S1, I=I1  % We can't change id of a variable
    ;   put_attr(X, id, id(S, I))
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

% Reads id attribute, if it doesn't exist set it to unbound pair of variables.
read_id(X, id(S, I)) :-
    var(X),
    (get_attr(X, id, id(S, I))
    ->  true
    ;   var(S), var(I),  % [?] Is this needed?
        put_attr(X, id, id(S, I))
    ).

% Display handlers
% Assert display_attributes(on) to display the value of the attribute
display_type(A) :- (display_attributes(on) -> write(A); true).
display_id(A) :- (display_attributes(on) -> write(A); true).

display_attributes(on).  % control display of attributes
