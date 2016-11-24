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

andint(Xi,Yi,P,R) :- 
	get_seq(Xi,P,X),
	get_seq(Yi,P,Y),
	R = and(X,Y).		
		
andel1(Xi,P,R) :-
	get_seq(Xi,P,X),
	X = and(Z,_),	
	R = Z.

andel2(Xi,P,R) :-
	get_seq(Xi,P,X),
	X = and(_,Z),	
	R = Z.

orint1(Xi,P,R) :-
	get_seq(Xi,P,X),
	X = or(Z,_),
	R = Z.

orint2(Xi,P,R) :-
	get_seq(Xi,P,X),
	X = or(_,Z),
	R = Z.

% x or sats utanför box,y-u box 1,v-w box 2
orel(Xi,Yi,Ui,Vi,Wi,P,R) :-
	get_seq(Xi,P,X),
	get_box(Yi,Ui,P,A1,R),
	get_box(Vi,Wi,P,A2,R), 
	X = or(A1,A2).

% implication, Bi = begin, Ei = end, A = assumption, C = consequence
impint(Xi,Yi,P,R) :-
	get_box(Xi,Yi,P,A,C),
	R = imp(A,C).

% removes implication, Vi = value index, Ii = implication index, P = proof.
impel(Xi,Yi,P,R) :-
	get_seq(Xi,P,X),
	get_seq(Yi,P,Y),
	Y = imp(X,R).

negint(Xi,Yi,P,R) :-
	get_box(Xi,Yi,P,A,cont),
	R = neg(A).

negel(Xi,Yi,P,R) :-
	get_seq(Xi,P,X),
	get_seq(Yi,P,neg(X)),	
	R = cont.

%?R can be anything?
contel(Xi,P,R) :- 
	get_seq(Xi,P,cont).

% introduces doublenegation, Vi = value index, P = proof, R = result
negnegint(Xi,P,R) :-
	get_seq(Xi,P,X),
	R = neg(neg(X)).

negnegel(Xi,P,R) :- 
	get_seq(Xi,P,X),
	neg(neg(R)) = X.

mt(Xi,Yi,P,R):-
	get_seq(Xi,P,imp(A,B)),
	get_seq(Yi,P,neg(B)),
	R= neg(A).

pbc(Xi,Yi,P,R) :-
	get_box(Xi,Yi,P,A,cont),
	A = neg(R).

%?kanske behöver göra en bakvänd version oxå men osäker?
lem(P,R) :-
	R = or(X,neg(X)).
	

% find sequence at index, I = index, H = head, T = tail S = sequence.
get_seq(_,[],_) :- fail.
get_seq(I,[[H,S,_]|_],S) :- I = H,!.
get_seq(I,[_|T],S) :- get_seq(I,T,S).

% find correct box, Bi = begin, Ei = end, P = proof, A = assumption, C = result
get_box(_,_,[],_,_) :- fail.
get_box(Bi,Ei,[B|_],A,C) :- B = [[Bi,A,assumption]|_],reverse(B,[[Ei,C,_]|_]),!.
get_box(Bi,Ei,[_|T],A,C) :- get_box(Bi,Ei,T,A,C).

