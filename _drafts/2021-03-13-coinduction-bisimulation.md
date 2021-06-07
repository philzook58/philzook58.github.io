
A pointery circular list is a labelled transition system if which node you're on is the state, and tail takes you to the nexxt state and head is an action that takes you to the same state.
Two observationally eqauivalnt cirucils lists ones = 1 : 1 : ones and   ones = 1 : ones
are bisimilar

A more natural definition is observation O, S states, A actions.
head would then be an observation on the state.

Egraphs as transition systems? Observations of head, argument choice as action?
This suggests we don't have to canonicalize it?

The existential form of a coinduccutive type
exists s, (s, s -> f s)
Is the analog of a closure form  exists s. (s, (s,a) -> b)
We can defunctionalize the possible states and put all the s -> f s things in the apply function?

Ones | Inc1 n |

apply (Inc1 n) = Cons a (Inc1 (1 + n))
A closed data type of all my possible streams


CoCaml

bisimulation goes hand in hand with condicution.

What does it mean for two systems to be equal?

Automata traditionally just worry about the trace they accept.
Nodes are labelled with somethign and edges are labelled with somethign. not persay atomic actions.

Hmm. So the record type condictive in coq. Each accessor is a message or action
And I suppose each value of the conidcutive is a state.
Is this a bisimulation under that understanding?
```
CoInductive bisim {A : Set} (x y : stream A) : Set :=
  | bisim_eq : head x = head y -> bisim (tail x) (tail y) -> bisim x y.
```

https://poisson.chat/aquarium/defunctionalization.pdf - lusxia - shows an interesting defunctionalization trick to define fix.
Is the point to close the universe of possible functions so that coq can see that we're only using productive ones

https://arxiv.org/pdf/1906.00046.pdf interaction trees
conor mcbride turing completeness


A process in coq.
The labelled trasnition relation. Ok sure.
Inductive trans s1 a s2 :=

Then what?
Definition bisim ta tb sa1 sa2 := 
   forall s1
Definition IsBisim r ta t2 := forall sa1 



https://blog.sigplan.org/2019/10/14/how-to-design-co-programs/
Howw to design co-porgrams - gibbonsd

Coinduction. What up?
https://en.wikipedia.org/wiki/Coinduction
https://en.wikipedia.org/wiki/Corecursion

Sangiorgi Book
Rutten and Bart Jacobs

Connection to recursion schemes. Categorical perspective. Meijer.


"Biggest Fixed Point"

`a -> f a` building up a functor f

`f a -> a` breaking down a functor f



Coinduction ~ object oriented.
Observations / messages are sent to a data object
Existential encoding - Strymonas paper
exists s, {state : s ;  observation1 : s -> yada ; observation2 : s -> yada  }
As compared to universal encoding (Bohm berarducci) of inductive types (their fold)

codata is productive, meaning recursion is guarded by applications of constructors



copatterns
https://agda.readthedocs.io/en/v2.6.1.3/language/copatterns.html
Are copatterns simple? They just explain what to do on every application of an accessor functiojn
on a record. This is the same thing as giving the record explicility
https://www.youtube.com/watch?v=-fhaZvgDaZk&ab_channel=OlafChitil altenrkirch coinduction in agda


LogTalk -
Co-LP (logic programming), rational trees. Could one fold together the lambda prolog perspective and 
https://www.youtube.com/watch?v=nOqO5OlC920&t=3644s&ab_channel=MicrosoftResearch a talk by gupta
Vicisou Circle - book
Aczel in 80s?


Co-LP is dual to tabling
The metinterpeter looks very simple. What is a metaintepreter for tabling. Is it similarly simple?
https://personal.utdallas.edu/~gupta/meta.html
Keep list of previous calls. Attempt to unify with a previous call. This recognizes cycles.
co-auto for Coq? Does paco do something like this?
Interesting connection: Sequent as a virtual machine, lambnda prolog sequents describe logic programming, This coniductive metainterpreter reifies the goal stack. So does the delmittied continuation based tabling. Coinductive = negative types
Sequent calc as a virtual machine is already kind of how lambda prolog is described. But Downen was talking classical logic, and Miller nadathur almost exclusively constructive logic. Miller and nadathur do have function types, distinct from implication (I think). 
Could one make a prolog on this basis. Should the coinductive predicates somehow be connected to continuations? The tabled version reifies a goal stack for delimitted continuations. No wait. I'm remembering achieving tabling via delimitted conts.

<   |   > :- < | >,  <  |  >
Or this as a notation for callcc, shift/reset? In scheme or whatever the conitnuation is not omnipresent in notation.
p(X,Y) :-  < K |     >  % this is binding a K with callCC or something
Downen and Ariloa are saing classical logic does have an operational semantics, some what maybe in contradictin to the feel of what Miller is saying,.


https://personal.utdallas.edu/~gupta/ppdp06.pdf  Co-Logic Programming: Extending Logic Programming
with Coinduction L. Simon, A. Mallya, A. Bansal, G. Gupta
https://twitter.com/sivawashere/status/1364734181545238532
https://logtalk.org/papers/colp2012/coinduction_colp2012_slides.pdf



Downen. Connections back to sequent calculus papers. Computing with classical connectives.
https://arxiv.org/abs/2103.06913v1 - Classical (Co)Recursion: Programming
Paul Downen, Zena M. Ariola, examples in python scheme, agda



Bisimulation
Coinductive proof


Coq and coidnuction
Chlipala's chapter
Breitner blog post - https://www.joachim-breitner.de/blog/726-Coinduction_in_Coq_and_Isabelle
https://www.joachim-breitner.de/blog/727-How_is_coinduction_the_dual_of_induction_

Older notes - Nice ones by
Eduardo Giménez and Pierre Castéran (2007). "A Tutorial on [Co-]Inductive Types in Coq"  http://www.labri.fr/perso/casteran/RecTutorial.pdf
Paco
Computability theory library

Basic interesting proofs:

techniques - unfold via a match function.
Condinductive records are smarter?
Positive and negative types


https://www.cs.cornell.edu/~kozen/Papers/MetricCoind.pdf metric donictuction
What is this

https://www.cs.cornell.edu/~kozen/Papers/Structural.pdf practical coinduction - kozen

https://github.com/dpndnt/library/blob/master/doc/pdf/abel-adelsberger-setzer-2017.pdf
Interactive programming Agda - Objects and GUIs.


The smallest coinductive is unit
The smallest inductive   is void

Finite enum types = inductives

Mixing in enums, you can make finite product types as coindcutives.

Taking it more hard core, you could make a record for every body of an inductive.

Primitive inifinite condinductive is Forever
primitive infiniter indcutive     is nat


Negative types and positive types. They come together to create activity.
Push streams and pull streams

Neel - 
Hi, this is a surprisingly complicated question.
For lazy languages, least and greatest fixed points coincide. (The jargon is "limit-colimit coincidence" or "bilimit-compactness".)
For strict languages, they do not coincide, and while you can still encode them, the absence of coinductive types is arguably a language deficiency.
For languages with first class continuations, they are perfect duals -- the negation of an inductive type is a coinductive type, and vice versa. This also means that the eliminator for an inductive value is a coinductively defined continuation, and vice versa. (See David Baelde's Least and Greatest Fixed Points in Linear Logic.)
This duality does not hold in languages without first class continuations, since there is an asymmetry between how you can use values and how you can use continuations.
You will sometimes see people talking about how inductive types are strict and coinductive types are lazy. This is a misconception -- in a language with continuations, you can have both strict and lazy inductive types, and strict and lazy coinductive types. Due to the aforementioned asymmetry, in a language withouts control, you can have strict and lazy inductives, but only lazy coinductive types. (This is in Baelde's paper, but you have to squint to realize it, because he was doing proof theory rather than language design.)
https://arxiv.org/pdf/0910.3383.pdf Balede's paper