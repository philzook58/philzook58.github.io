<https://people.math.harvard.edu/~knill/>

# Mit PL review

custom bit stealing for adt
memory types

bottom up syntehsis with observation equivalence.
Do top down search to build possible contexts and fill in with bottom up?

algerbaic efects
plotkin and power
bauer's tutorial <https://arxiv.org/abs/1807.05923>

urnge kutta correctors for keeping games in sync
moment generating functions and higher order exact probabilstic programming langs.

html in lean... <https://voidma.in/> <https://github.com/leanprover-community/ProofWidgets4>
Scilean
lean-hog house of frpah in lean <https://github.com/katjabercic/Lean-HoG>
penrose for automatic daigramming <https://penrose.cs.cmu.edu/>
venn diragrsm

string diagrams and commutiative sdiagrams

verbose lean by matrick massot <https://github.com/PatrickMassot/verbose-lean4> writes in
a lean port of tarksi's world

vlada sedlacek ecudiean geneotry <https://github.com/ianjauslin-rutgers/pythagoras4> ?
tarksi world

<https://github.com/vbeffara/RMT4> riemann mapping theorem

<https://github.com/ianjauslin-rutgers/leanblueprint-extract> extacrt blueprints

lean extensible
html tags
 #html
robert lewis discrete math <https://github.com/brown-cs22/CS22-Lean-2024>

regster tiling
unroll and jam
cache tiling - runtime
resgiter tiling  - compile time

##

create table gamma(formula , clause)
.decl gamma(f : form, c : clause)

Yea, wait. Duh, clingo is easier.
Well clingo doesn't have cusbsumption which is a bummer.

```clingo

simp(t1,t2) :- simp(t1, t2), sub(t2,t3), simp(t3,t4)

simp(t1,t2) :- simp(t1,t2),   

```

Wait, but I only need size. KBO

```clingo

size(var(N),1) :- term(var(N)).
size(plus(X,Y), Nx + Ny + 1) :- term(plus(X,Y)), size(X,Nx), size(Y,Ny).



eq(X,Y).
rw(X,Y).

rw(X,Y):- eq(X,Y), size(X,Nx), size(Y,Ny), Nx > Ny.

```

you know, I've probably written a ton of variations of this.
