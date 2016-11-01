% verifiera att filen innehåller ett korrekt bevis.
verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

% kontrollera att ett logiskt bevis är syntaktiskt korrekt.
valid_proof(_,_,[[_,_,K|_]|_]) :- K = assumption,fail,!.
valid_proof(Prems, Goal, Proof) :-
	reverse(Proof,Foorp),
	Foorp = [[_,Result|_]|_],
	Goal = Result,
	prove(Prems,Foorp,[]).

% bevisa en rad, P = premisser, F = bakbevis, E = tidigare rader, K = konnektiv.
prove(_,[],_) :- !.
prove(P,F,E) :- F = [[_,_,K]|T], K = premise, premise(F,P), prove(P,T,E),!.
prove(P,F,E) :- F = [[_,_,K]|T], call(K,F,E), prove(P,T,E),!.
% nästa rad är box. B = box, X = xob, Y = Förra boxens rest och tidigare rader.
prove(P,[B|T],E) :- reverse(B,X), append(T,E,Y), prove(P,X,Y), prove(P,T,E).

% introducerar rader från premisser, S = sekvens, P = premisser.
premise([[_,S|_]|_],P) :- in_list(S,P).

% antagande, bara möjligt i början av en box, T = bevissvans.
assumption([_|T],_) :- T = [].

% kopiera en tidigare rad, I = index, R = resultat, V = värde
copy(I,F,E) :-
	F = [[_,R|_]|_],
	get_seq(I,F,E,V),
	R = V.

% introducerar implikation, Bi = begin, Ei = end, A = assumption, C = konsekvens
impint(Bi,Ei,F,_) :-
	F = [[_,R|_],B|_],
	B = [[_,A|_]|_],
	check_box(B,[[_,C|_]|_],Bi,Ei),
	R = imp(A,C).

% tar bort implikation, Vi = värdeindex, Ii = implikationindex, F = bakbevis.
impel(Vi,Ii,F,E) :-
	F = [[_,R|_]|_],
	get_seq(Vi,F,E,V),
	get_seq(Ii,F,E,I),
	I = imp(V,R).

% introducerar dubbelnegation, Vi = värdets index, F = bakbevis, R = resultat
negnegint(Vi,F,E) :- 
	F = [[_,R|_]|_],
	get_seq(Vi,F,E,V),
	R = neg(neg(V)).

get_seq(I,F,_,S) :- get_seqh(I,F,S),!.
get_seq(I,_,E,S) :- get_seqh(I,E,S).
% hämtar sekvens mhja index, I = index, H = huvud, T = bevissvans S = sekvens.
get_seqh(_,[],_) :- fail.
get_seqh(I,[[H,S|_]|_],S) :- I = H,!.
get_seqh(I,[_|T],S) :- get_seqh(I,T,S).

% se om box har rätt egenskaper, B = box, X = xob, Bi = begin, Ei = end.
check_box(B,X,Bi,Ei) :-
	reverse(B,X),
	B = [[Pi,_,A]|_],
	X = [[Fi|_]|_],
	Pi = Bi,
	Fi = Ei,
	A = assumption.

% kolla om element finns i lista ( därför att member förstör tester.. )
in_list(_,[]) :- fail.
in_list(X,[H|_]) :- X = H,!.
in_list(X,[_|T]) :- in_list(X,T).
