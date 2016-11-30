:- module(rules,[
		copy/3,andint/4,andel1/3,andel2/3,
		orint1/3,orint2/3,orel/7,impint/4,impel/4,
		negint/4,negel/4,contel/3,negnegint/3,negnegel/3,
		mt/4,pbc/4,lem/2
	]).

% General variable naming pattern:
% Xi = index x, X = value at x, Yi = index y, Y = value at y,
% P = proof, R = result, C = Result of box, A = Assumption.

% copy a previous row.
copy(Xi,P,R) :-
	get_seq(Xi,P,X),
	R = X.
	
% and introduction from Xi and Yi
andint(Xi,Yi,P,R) :- 
	get_seq(Xi,P,X),
	get_seq(Yi,P,Y),
	R = and(X,Y).		

% and elimination at xi first element.
andel1(Xi,P,R) :-
	get_seq(Xi,P,and(R,_)).

% and elimination at xi second element. 
andel2(Xi,P,R) :-
	get_seq(Xi,P,and(_,R)).

% or introduction at xi first element.
orint1(Xi,P,R) :-
	get_seq(Xi,P,X),
	R = or(X,_).

% or introduction at xi second element.
orint2(Xi,P,R) :-
	get_seq(Xi,P,X),
	R = or(X,_).

% or elimination from Xi. or: Xi  box1: Yi-Ui box2: Vi-Wi, A1-2= Assumptions
orel(Xi,Yi,Ui,Vi,Wi,P,R) :-
	get_seq(Xi,P,X),
	get_box(Yi,Ui,P,A1,R),
	get_box(Vi,Wi,P,A2,R), 
	X = or(A1,A2).

% implication introduction
impint(Xi,Yi,P,R) :-
	get_box(Xi,Yi,P,A,C),
	R = imp(A,C).

% removes implication.
impel(Xi,Yi,P,R) :-
	get_seq(Xi,P,X),
	get_seq(Yi,P,Y),
	Y = imp(X,R).

% negation introduction.
negint(Xi,Yi,P,R) :-
	get_box(Xi,Yi,P,A,cont),
	R = neg(A).

% negation elimination.
negel(Xi,Yi,P,R) :-
	get_seq(Xi,P,X),
	get_seq(Yi,P,neg(X)),	
	R = cont.

% contradiction elimination.
contel(Xi,P,_R) :- 
	get_seq(Xi,P,cont).

% introduces doublenegation.
negnegint(Xi,P,R) :-
	get_seq(Xi,P,X),
	R = neg(neg(X)).

% eliminates double negation.
negnegel(Xi,P,R) :-
	get_seq(Xi,P,neg(neg(R))).
	
% MT, modus tolens, x->y if y is false x cannot be true. 
mt(Xi,Yi,P,R):-
	get_seq(Xi,P,imp(A,B)),
	get_seq(Yi,P,neg(B)),
	R= neg(A).
	
%Proof by contradiction, if neg(x) leads to contradiction x must be true. 
pbc(Xi,Yi,P,R) :-
	get_box(Xi,Yi,P,A,cont),
	A = neg(R).
	
%Law of excluded middle, X or Neg(X) must be true.
lem(_P,R) :-
	R = or(X,neg(X)).
lem(_P,R) :-
	R = or(neg(X),X).

% find sequence at index, I = index, H = head, T = tail S = sequence.
get_seq(_,[],_) :- fail.
get_seq(I,[[H,S,_]|_],S) :- I = H,!.
get_seq(I,[_|T],S) :- get_seq(I,T,S).

% find correct box, Bi = begin, Ei = end, P = proof, A = assumption, C = result
get_box(_,_,[],_,_) :- fail.
get_box(Bi,Ei,[B|_],A,C) :- B = [[Bi,A,_]|_],reverse(B,[[Ei,C,_]|_]),!.
get_box(Bi,Ei,[_|T],A,C) :- get_box(Bi,Ei,T,A,C).

