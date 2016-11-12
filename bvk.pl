:- use_module(rules).

% verify that the file contains a valid proof
verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

% make sure a logical proof is syntactically correct
valid_proof(_,_,[[_,_,assumption]|_]) :- !,fail.
valid_proof(Prems, Goal, Proof) :-
	reverse(Proof,Foorp),
	Foorp = [[_,Goal|_]|_],
	prove(Prems,Foorp,Foorp).

% prove one row, P = premises, F = foorp, C = current box, K = connective
prove(_,_,[]) :- !.
prove(P,[_|FT],C) :- C = [[_,S,K]|CT], K = premise,!,premise(P,S),prove(P,FT,CT).
prove(P,[_|FT],C) :- C = [[_,_,K]|CT], K = assumption,!,assumption(C),prove(P,FT,CT).
prove(P,F,[_|CT]) :- F = [[_,R,K]|FT], catch(call(K,FT,R),error(E,_),fail),prove(P,FT,CT),!.
% next row must be a box, B = box, X = xob, Y = rest of proof including box.
prove(P,[B|F],[B|C]) :- reverse(B,X), append(X,F,Y), prove(P,Y,X), prove(P,F,C).

% introducing rows from premises, S = sequence, P = premises.
premise(P,S) :-
	in_list(S,P).

% assumption, only possible at the start of a box, T = tail of proof.
assumption([_|T]) :-
	T = [].

% check if element is in list ( because member ruins testing.. )
in_list(_,[]) :- fail.
in_list(X,[H|_]) :- X = H,!.
in_list(X,[_|T]) :- in_list(X,T).
