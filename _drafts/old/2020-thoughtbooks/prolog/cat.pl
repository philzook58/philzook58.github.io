

% comp of list instead so that intrnisically asscoiative

% comp([], hom(A,A)). % convention that empty list is identity
%ty(comp([F]), ty(F))
% ty(comp([F|FS]), hom(A,C) :- ty(F,hom(A,B)), ty(comp(FS),   
:- set_prolog_flag(occurs_check, true).


ty(id, hom(A,A)). % yeah identity is just blasting out
ty(g, hom(b,d)).
ty(f, hom(a,c)).
ty(fan(F,G), hom(A, tup(B,C)) ) :- ty(F, hom(A,B)), ty(G, hom(A,C)).
ty(snd, hom(tup(A,B), B)).           % :- dif(A,B).
ty(fst, hom(tup(A,B), A)).           % :- dif(A,B).
ty(comp(F,G), hom(A,C)) :- simp(F), ty(F,hom(A,B)), ty(G,hom(B,C)).


%ty(comp([F|Gs]), hom(A,C)) :- dif(F,comp()), ty(F,hom(A,B)), ty(G,hom(B,C)).)

% reassoc(comp(comp(F,G),H), FGH) :- reassoc(comp(G,H), GH), reassoc(comp(F,GH), FGH).

%ty(id, hom(A,A)).
%simp(id).
simp(snd).
simp(fst).
simp(f).
simp(g).
%simp(fan(A,B)).


nat(z).
sat(s(X)) :- nat(X).

depth(snd, z).
depth(fst, z).
depth(snd, z).
depth(fan(F,G), N) :- depth(F,NF), depth(G,NG), N is max(NF,NG) + 1.
depth(comp(F,G), N) :- depth(F,NF), depth(G,NG), N is max(NF,NG) + 1. 


% suspcious rule. We seem to be recursing into ourselves possibly
%ty(comp(F,G), hom(A,C)) :- dif(F,id), dif(G,id), ty(F,hom(A,B)), ty(G,hom(B,C)). % do not use id here.




% queries
%  ty(F, hom(tup(a,b),tup(a,a))).
%  ty(F, hom(tup(a,b), tup(c,d))).
% 

