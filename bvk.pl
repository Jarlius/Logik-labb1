:- use_module(rules).

% verify that the file contains a valid proof
verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

% the main proof box cannot start with an assumption
valid_proof(_,_,[[_,_,assumption]|_]) :- !,fail.
% make sure a logical proof is syntactically correct
valid_proof(Prems, Goal, Proof) :-
	reverse(Proof,Foorp),
	Foorp = [[_,Goal|_]|_],
	prove(Prems,Foorp,Foorp).

% prove one row, P = premises, F = foorp, C = current box, K = connective
prove(_,_,[]) :- !.
% introducing rows from premises, only predicate that uses P
prove(P,[_|FT],C) :- C = [[_,S,K]|CT], K = premise,!,
	in_list(S,P), prove(P,FT,CT).
% assumption, only possible at the start of a box
prove(P,[_|FT],C) :- C = [[_,_,K]|CT], K = assumption,!,
	CT = [], prove(P,FT,CT).
% rules, each take its result and the tail of the proof as extra parameters
prove(P,F,[_|CT]) :- F = [[_,R,K]|FT], 
	catch((functor(K,N,A),B is A + 2,functor(L,N,B)),error(_,_),fail),
	predicate_property(L,imported_from(rules)), % check that predicate is a rule
	call(K,FT,R),prove(P,FT,CT),!.
% next row must be a box, B = box, X = xob, Y = rest of proof including box
prove(P,[B|F],[B|C]) :- B = [[_,_,assumption]|_], reverse(B,X), append(X,F,Y),
	prove(P,Y,X), prove(P,F,C).

% check if element is in list ( because member ruins testing.. )
in_list(_,[]) :- fail.
in_list(X,[H|_]) :- X = H,!.
in_list(X,[_|T]) :- in_list(X,T).
