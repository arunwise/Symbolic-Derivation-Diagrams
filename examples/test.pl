values(s1, [t,f]).
values(s2(_), [r,g,b]).

set_sw(s1, [0.5, 0.5]).
set_sw(s2(t), [0.33, 0.33, 0.33]).
set_sw(s2(f), [0.5, 0.25, 0.25]).

p1(X) :- msw(s1, 1, X).
p2(Y) :- p1(X), msw(s2(X), 1, Y).

q(Z) :- p2(Y), {Z=Y}.