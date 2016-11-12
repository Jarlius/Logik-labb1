:- module(rules,[
		copy/3,andint/4,andel1/3,andel2/3,
		orint1/3,orint2/3,orel/7,impint/4,impel/4,
		negint/4,negel/4,contel/3,negnegint/3,negnegel/3,
		mt/4,pbc/4,lem/2
	]).

% copy a previous row, X = index, P = proof, R = result, V = value
copy(Xi,P,R) :-
	get_seq(Xi,P,X),
	R = X.

andint(Xi,Yi,P,R).

andel1(Xi,P,R).

andel2(Xi,P,R).

orint1(Xi,P,R).

orint2(Xi,P,R).

orel(Xi,Yi,Ui,Vi,Wi,P,R).

% implication, Bi = begin, Ei = end, A = assumption, C = consequence
impint(Xi,Yi,P,R) :-
	get_box(Xi,Yi,P,A,C),
	R = imp(A,C).

% removes implication, Vi = value index, Ii = implication index, P = proof.
impel(Xi,Yi,P,R) :-
	get_seq(Xi,P,X),
	get_seq(Yi,P,Y),
	Y = imp(X,R).

negint(Xi,Yi,P,R).

negel(Xi,Yi,P,R).

contel(Xi,P,R).

% introduces doublenegation, Vi = value index, P = proof, R = result
negnegint(Xi,P,R) :-
	get_seq(Xi,P,X),
	R = neg(neg(X)).

negnegel(Xi,P,R).

mt(Xi,Yi,P,R).

pbc(Xi,Yi,P,R).

lem(P,R).

% find sequence at index, I = index, H = head, T = tail S = sequence.
get_seq(_,[],_) :- fail.
get_seq(I,[[H,S,_]|_],S) :- I = H,!.
get_seq(I,[_|T],S) :- get_seq(I,T,S).

% find correct box, Bi = begin, Ei = end, P = proof, A = assumption, C = result
get_box(_,_,[],_,_) :- fail.
get_box(Bi,Ei,[B|_],A,C) :- B = [[Bi,A,assumption]|_],reverse(B,[[Ei,C,_]|_]),!.
get_box(Bi,Ei,[_|T],A,C) :- get_box(Bi,Ei,T,A,C).

