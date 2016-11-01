% verifiera att filen innehåller ett korrekt bevis.
verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

% kontrollera att ett logiskt bevis är syntaktiskt korrekt.
valid_proof(_,_,[[_,_,assumption]|_]) :- fail,!.
valid_proof(Prems, Goal, Proof) :-
	reverse(Proof,Foorp),
	Foorp = [[_,Goal|_]|_],
	prove(Prems,Foorp,Foorp).

% bevisa en rad, P = premisser, F = bakbevis, C = nuvarande box, K = konnektiv.
prove(_,_,[]) :- !.
prove(P,[_|FT],C) :- C = [[_,S,K]|CT], K = premise,!,premise(P,S),prove(P,FT,CT).
prove(P,[_|FT],C) :- C = [[_,_,K]|CT], K = assumption,!,assumption(C),prove(P,FT,CT).
prove(P,F,[_|CT]) :- F = [[_,R,K]|FT], call(K,F,R),prove(P,FT,CT),!.
% nästa rad är box. B = box, X = xob, Y = Förra boxens rest och tidigare rader.
prove(P,[B|F],[B|C]) :- reverse(B,X), append(X,F,Y), prove(P,Y,X), prove(P,F,C).

% introducerar rader från premisser, S = sekvens, P = premisser.
premise(P,S) :-
	in_list(S,P).

% antagande, bara möjligt i början av en box, T = bevissvans.
assumption([_|T]) :-
	T = [].

% kopiera en tidigare rad, I = index, P = bevis, R = resultat, V = värde
copy(I,P,R) :-
	get_seq(I,P,V),
	R = V.

% introducerar implikation, Bi = begin, Ei = end, A = antagande, C = konsekvens
impint(Bi,Ei,P,R) :-
	get_box(Bi,Ei,P,A,C),
	R = imp(A,C).

% tar bort implikation, Vi = värdets index, Ii = implikationens index, P = bevis.
impel(Vi,Ii,P,R) :-
	get_seq(Vi,P,V),
	get_seq(Ii,P,I),
	I = imp(V,R).

% introducerar dubbelnegation, Vi = värdets index, P = bevis, R = resultat
negnegint(Vi,P,R) :-
	get_seq(Vi,P,V),
	R = neg(neg(V)).

% hämtar sekvens mhja index, I = index, H = huvud, T = bevissvans S = sekvens.
get_seq(_,[],_) :- fail.
get_seq(I,[[H,S,_]|_],S) :- I = H,!.
get_seq(I,[_|T],S) :- get_seq(I,T,S).

% hitta rätt box, Bi = begin, Ei = end, P = bevis, A = antagande, C = resultat
get_box(_,_,[],_,_) :- fail.
get_box(Bi,Ei,[B|_],A,C) :- B = [[Bi,A,assumption]|_],reverse(B,[[Ei,C,_]|_]),!.
get_box(Bi,Ei,[_|T],A,C) :- get_box(Bi,Ei,T,A,C).

% kolla om element finns i lista ( därför att member förstör tester.. )
in_list(_,[]) :- fail.
in_list(X,[H|_]) :- X = H,!.
in_list(X,[_|T]) :- in_list(X,T).
