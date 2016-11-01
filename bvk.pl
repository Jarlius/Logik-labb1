% verifiera att filen innehåller ett korrekt bevis.
verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

% kontrollera att ett logiskt bevis är syntaktiskt korrekt.
valid_proof(Prems, Goal, Proof) :-
	reverse(Proof,Foorp),
	Foorp = [[_,Result|_]|_],
	Goal = Result,
	prove(Foorp,Prems).

% bevisa en rad, F = bakbevis, P = premisser, K = konnektiv, T = bevissvans.
prove([],_) :- !.
prove(F,P) :- F = [[_,_,K|_]|T], K = premise, premise(F,P), prove(T,P),!.
prove(F,P) :- F = [[_,_,K|_]|T], call(K,F), prove(T,P).

% Introducerar rader från premisser, S = sekvens, P = premisser.
premise([[_,S|_]|_],P) :- in_list(S,P).

% Tar bort implikation, Vi = värdeindex, Ii = implikationindex, F = bakbevis.
impel(Vi,Ii,F) :-
	F = [[_,R|_]|_],
	get_seq(Vi,F,V),
	get_seq(Ii,F,I),
	I = imp(V,R).

% Introducerar dubbelnegation, Vi = värdets index, F = bakbevis, R = resultat
negnegint(Vi,F) :- 
	F = [[_,R|_]|_],
	get_seq(Vi,F,V),
	R = neg(neg(V)).

% Hämtar sekvens mhja index, I = index, R = rad, T = bevissvans S = sekvens.
get_seq(_,[],_) :- fail.
get_seq(I,[[H,S|_]|_],S) :- I = H,!.
get_seq(I,[_|T],S) :- get_seq(I,T,S).

% kolla om element finns i lista ( därför att member förstör tester.. )
in_list(_,[]) :- fail.
in_list(X,[H|_]) :- X = H,!.
in_list(X,[_|T]) :- in_list(X,T).
