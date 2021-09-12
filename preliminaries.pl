
% Preliminaries

member(E, [E|_]).
member(E, [_|T]) :-
  member(E, T).

append([], L, L).
append([H|T], L, [H|NT]) :-
  append(T, L, NT).

concatd(X, Y, Z) :- X = A-B, Y = B-C, Z = A-C.

set_eq(S1, S2) :-
  card(S1, C),
  card(S2, C),
  subset(S1, S2).

card(L, C) :-
  card(L, 0, C).
card([], C, C).
card([_|T], C, R) :-
  NC is C + 1,
card(T, NC, R).

min([H|T], R) :-
  min(T, H, R).
min([], R, R).
min([H|T], N, R) :-
  H < N,
  min(T, H, R).
min([H|T], N, R) :-
  H >= N,
  min(T, N, R).

max([H|T], R) :-
  max(T, H, R).
max([], R, R).
max([H|T], N, R) :-
  H > N,
  max(T, H, R).
max([H|T], N, R) :-
  H =< N,
  max(T, N, R).

strsubset(R, S) :-
  card(R, C1),
  card(S, C2),
  C1 \= C2,
  subset(R, S).

% subsetvs(R, S) :-
%   R \= S,
%   subsetv(R, S).

subset([], _).
subset([H|T], S) :-
  member(H, S),
  subset(T, S).

% subsetv(R, S) :-
%   subsetv([], S, R).
% subsetv(R, [], R).
% subsetv(S, [H|T], R) :-
%   subsetv([H|S], T, R).
% subsetv(S, [_|T], R) :-
%   subsetv(S, T, R).

union(S1, S2, R) :-
  union(S1, S2, S2, R).
union([], _, R, R).
union([H|T], S, NS, R) :-
  member(H, S),
  union(T, S, NS, R).
union([H|T], S, NS, R) :-
  not member(H, S),
  union(T, S, [H|NS], R).

inter(S1, S2, R) :-
  inter(S1, S2, [], R).
inter([], _, R, R).
inter([H|T], S, NS, R) :-
  member(H, S),
  inter(T, S, [H|NS], R).
inter([H|T], S, NS, R) :-
  not member(H, S),
  inter(T, S, NS, R).

subtract(S1, S2, R) :-
  subtract(S1, S2, [], R).
subtract([], _, R, R).
subtract([H|T], S, NS, R) :-
  member(H, S),
  subtract(T, S, NS, R).
subtract([H|T], S, NS, R) :-
  not member(H, S),
  subtract(T, S, [H|NS], R).

range(End, End, [End]).
range(Start, End, [Start|NT]) :-
  Start #< End,
  NS #= Start + 1,
  range(NS, End, NT).

cartesian(S1, S2, R) :-
  cartesian(S1, S2, S2, [], R).
cartesian([], _, _, R, R).
cartesian([_|T1], [], S2, Acc, R) :-
  cartesian(T1, S2, S2, Acc, R).
cartesian([H1|T1], [H2|T2], S2, Acc, R) :-
  cartesian([H1|T1], T2, S2, [t(H1, H2)|Acc], R).

pow(S, P) :-
  findall(A, pow(S, [], A), P).
pow1(S, P) :-
  pow(S, [_|P]).
pow([], R, R).
pow([_|T], S, R) :-
  pow(T, S, R).
pow([H|T], NT, R) :-
  pow(T, [H|NT], R).

relation(S1, S2, R) :-
  cartesian(S1, S2, M),
  pow(M, R).

dom(S, D) :-
  dom(S, [], D).
dom([], R, R).
dom([t(D, _)|S], NS, R) :-
  member(D, NS),
  dom(S, NS, R).
dom([t(D, _)|S], NS, R) :-
  not member(D, NS),
  dom(S, [D|NS], R).

ran(S, D) :-
  ran(S, [], D).
ran([], R, R).
ran([t(_, D)|S], NS, R) :-
  member(D, NS),
  ran(S, NS, R).
ran([t(_, D)|S], NS, R) :-
  not member(D, NS),
  ran(S, [D|NS], R).

% comp(S1, S2, R) :-
%   comp(S1, S2, [], R).
% comp([], _, R, R).
% comp([t(D1, R1)|S1], S2, S, R) :-
%   findall(t(D1, D2), member(t(R1, D2), S2), T),
%   append(S, T, NS),
%   comp(S1, S2, NS, R).

comp(S1, S2, R) :-
  D = A-A,
  comp(S1, S2, D, R).
comp([], _, S, R) :-
  S = R-[].
comp([E|S1], S2, S, R) :-
  D = A-A,
  comp_aux(S2, E, D, NEs),
  concatd(S, NEs, NS),
  comp(S1, S2, NS, R).
comp_aux([], _, R, R).
comp_aux([t(R1, R2)|S1], t(D1, R1), S, R) :-
  D = [t(D1, R2)|A]-A,
  concatd(S, D, NS),
  comp_aux(S1, t(D1, R1), NS, R).
comp_aux([t(D2, _)|S1], t(D1, R1), S, R) :-
  R1 \= D2,
  comp_aux(S1, t(D1, R1), S, R).


id(S, R) :-
  id(S, [], R).
id([], R, R).
id([H|T], NS, R) :-
  id(T, [t(H, H)|NS], R).

inverse(S, R) :-
  inverse(S, [], R).
inverse([], R, R).
inverse([t(H1, H2)|T], NS, R) :-
  inverse(T, [t(H2, H1)|NS], R).

pfun(S, T, Result) :-
  relation(S, T, Relation),
  id(T, ID),
  findall(R, pfun_cond(R, Relation, ID), Result).
pfun_cond(R, Relation, ID) :-
  member(R, Relation),
  inverse(R, InvR),
  comp(InvR, R, Comp),
  subset(Comp, ID).

tfun(S, T, Result) :-
  pfun(S, T, PF),
  findall(F, tfun_cond(F, S, PF), Result).
tfun_cond(F, S, PF) :-
  member(F, PF),
  dom(F, D),
  set_eq(D, S).

pinj(S, T, Result) :-
  pfun(S, T, PF1),
  pfun(T, S, PF2),
  findall(F, pinj_cond(F, PF1, PF2), Result).
pinj_cond(F, PF1, PF2) :-
  member(F, PF1),
  inverse(F, InvF),
  member(F2, PF2),
  set_eq(InvF, F2).

tinj(S, T, Result) :-
  tfun(S, T, TF),
  pinj(S, T, PI),
  inter(TF, PI, Result).

psur(S, T, Result) :-
  pfun(S, T, PF),
  findall(F, psur_cond(F, T, PF), Result).
psur_cond(F, T, PF) :-
  member(F, PF),
  ran(F, R),
  set_eq(R, T).

tsur(S, T, Result) :-
  psur(S, T, PS),
  tfun(S, T, TF),
  inter(PS, TF, Result).

tbij(S, T, Result) :-
  tinj(S, T, TI),
  tsur(S, T, TS),
  inter(TI, TS, Result).

image(S1, S2, R) :-
  D = A-A,
  image(S2, S1, D, R).
image([], _, D, R) :-
  D = R-[].
image([H|T], S, CR, R) :-
  D = A-A,
  image_aux(S, H, D, Is),
  concatd(CR, Is, NR),
  image(T, S, NR, R).
image_aux([], _, R, R).
image_aux([t(E, X)|T], E, CR, R) :-
  D = [X|A]-A,
  concatd(CR, D, NR),
  image_aux(T, E, NR, R).
image_aux([t(NOT_E, X)|T], E, CR, R) :-
  E \= NOT_E,
  image_aux(T, E, CR, R).

domres(S, T, R) :-
  D = A-A,
  domres(T, S, D, R).
domres([], _, D, R) :-
  D = R-[].
domres([t(X, Y)|T], S, CR, R) :-
  member(X, S),
  D = [t(X, Y)|A]-A,
  concatd(CR, D, NR),
  domres(T, S, NR, R).
domres([t(X, Y)|T], S, CR, R) :-
  not member(X, S),
  domres(T, S, CR, R).

domsub(S, T, R) :-
  D = A-A,
  domsub(T, S, D, R).
domsub([], _, D, R) :-
  D = R-[].
domsub([t(X, Y)|T], S, CR, R) :-
  not member(X, S),
  D = [t(X, Y)|A]-A,
  concatd(CR, D, NR),
  domsub(T, S, NR, R).
domsub([t(X, Y)|T], S, CR, R) :-
  member(X, S),
  domsub(T, S, CR, R).

ranres(S, T, R) :-
  D = A-A,
  ranres(S, T, D, R).
ranres([], _, D, R) :-
  D = R-[].
ranres([t(X, Y)|T], S, CR, R) :-
  member(Y, S),
  D = [t(X, Y)|A]-A,
  concatd(CR, D, NR),
  ranres(T, S, NR, R).
ranres([t(X, Y)|T], S, CR, R) :-
  not member(Y, S),
  ranres(T, S, CR, R).

ransub(S, T, R) :-
  D = A-A,
  ransub(S, T, D, R).
ransub([], _, D, R) :-
  D = R-[].
ransub([t(X, Y)|T], S, CR, R) :-
  not member(Y, S),
  D = [t(X, Y)|A]-A,
  concatd(CR, D, NR),
  ransub(T, S, NR, R).
ransub([t(X, Y)|T], S, CR, R) :-
  member(Y, S),
  ransub(T, S, CR, R).

override(S, T, R) :-
  dom(T, D),
  domsub(D, S, DS),
  union(T, DS, R).

dpro(S, T, R) :-
  D = A-A,
  dpro(S, T, D, R).
dpro([], _, D, R) :-
  D = R-[].
dpro([t(X, Y)|T], S, CR, R) :-
  D = A-A,
  dpro(S, X, Y, D, RR),
  concatd(CR, RR, NR),
  dpro(T, S, NR, R).
dpro([], _, _, R, R).
dpro([t(X, Z)|T], X, Y, CR, R) :-
  D = [t(X, t(Y, Z))|A]-A,
  concatd(CR, D, NR),
  dpro(T, X, Y, NR, R).
dpro([t(NOT_X, _)|T], X, Y, CR, R) :-
  X \= NOT_X,
  dpro(T, X, Y, CR, R).

ppro(S, T, R) :-
  D = A-A,
  ppro(S, T, D, R).
ppro([], _, D, R) :-
  D = R-[].
ppro([H|T], S, CR, R) :-
  D = A-A,
  ppro_aux(S, H, D, RR),
  concatd(CR, RR, NR),
  ppro(T, S, NR, R).
ppro_aux([], _, R, R).
ppro_aux([t(Y, N)|T], t(X, M), CR, R) :-
  D = [t(t(X, Y), t(M, N))|A]-A,
  concatd(CR, D, NR),
  ppro_aux(T, t(X, M), NR, R).

% assuming that the function is well defined
fun(S, E, F) :-
  member(t(E, F), S).
