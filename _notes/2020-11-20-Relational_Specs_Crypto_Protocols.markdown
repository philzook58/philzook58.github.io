---
author: philzook58
comments: true
date: 2020-11-20 19:07:10+00:00
layout: post
link: https://www.philipzucker.com/?p=3009

slug: Crypto, Protocols, Relational Specs, Concurrency
title: Crypto, Protocols, Relational Specs, Concurrency
wordpress_id: 3009
---

Noninterference and information flow control

ghost variables have a non interference property http://why3.lri.fr/ejcp-2016/ejcp16-slides.pdf
polymorphic types have a non interference property
staged metaprogramming has a noninterference

"The Trick" is an indirect control flow leak. This may be exactly what carette was getting at
Obvious information leakage is assignments from high security variables to low security ones.
Indirect is when yuou branch on high security and then do something different to low security in each side. It is hard to really put your finger on why this is bad. Noninterference properties nail it down.

"Implicit" taint. https://www.cs.cmu.edu/~ckaestne/15313/2018/20181023-taint-analysis.pdf

You can't really determine just by looking at the values at the end of an execution where their information came from. It really is more about the correlation between high and low variables over multiple runs.
You can see it if you're propagating a joint probability distribution. If you start with independent variables, at the end they are no longer independent. You can use a `p ln p` formula for entropy to quantify an amount of leakage.

It may be desirable to not take this approach for some reasons. Computer scientists are not comfortable with the continuum. To bring the the reals or fractions to deal with probabilities feels like too much. Sometimes what you want is a binary answer of leak of no leak. For this it is desirable or reasonable to wonder if there is a more discrete combinatorial formulation.

Probability and combinatorics have similarities. In fair situations, probabilities follow from combinatorics.  Consider for example the microcanonical ensemble of statistical mechanics, or fair dice or playing card questions.


Leakage may not be binary (leaked or not leaked). You can ask questions and receive one of many answers. So you can aks for any number of bits via "The Trick".
Actual security can kind of be a full continuum if you make probablistic choices. Can partial evaluation be a continuum? Since you're optimzing for performance, perhaps you might make choices based on probablilities of certain inputs. Hmm.



So one can look at security vulnerabilities and side channels for metaprogramming tricks. Staged metaprogramming _doesn't_ have non interference in some sense because implicit information flow is allowed.

Cody was throroughly unimpressed when I said that staged metaprogramming and verification were very similar. What was the context I was saying it? Was it the python-z3 connection? It probably was. That you can unroll loops at the metalevel and other such things. The whole thing of veirfication and proving is dealing with abstract symbolic quantities.

There is "something" here that feels like entanglement. Can I be more specific?


Taint and separation logic and points to analysis. Sources are kind of like `new` statements creating new stuff. We want to know if variables are possibly aliasing onto particular introduction points. Maybe this is a stretch? Anyway, perhaps context dependence is good here to avoid overtainting in the presence of implicit control flow https://yanniss.github.io/ptaint-oopsla17.pdf seems like I was onto something. Information leaking and memory leaking.

I guess one thing that might be cool is to prove that no better partial evaluation is possible. A countermodel of some kind (a PER? )

positive  and negative ofrmation flow?

Relational verification using WP tech?
post = R( x_a, x_b)
Nothing that works independently?
We need new language constructs?

https://www.cse.chalmers.se/~andrei/esop99.pdf hmm this describes binding time analysis and seucirty types as already being folk knowledge
A Per Model of Secure Information Flow in Sequential Programs. Wow this paper is popping off.


## Crypto Protocol Verification

  * https://www.ccs.neu.edu/home/riccardo/courses/csg399-sp06/
  * model checking. http://seclab.stanford.edu/pcl/mc/mc.html
  * CSP - communicating sequential logic
  * pi calculus. spi calculus https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/ic99spi.pdf
  * BAN logic https://en.wikipedia.org/wiki/Burrows%E2%80%93Abadi%E2%80%93Needham_logic
  * protocol logic  https://en.wikipedia.org/wiki/Protocol_composition_logic
  * protocol verification
  * https://www.cl.cam.ac.uk/~lp15/papers/Auth/lics.pdf paulson 
  * https://www.easycrypt.info/trac/ easycrypt
  * http://certicrypt.gforge.inria.fr/ certicrypt
  * infromation flow
  * noninterference. Low and high security information https://unsat.cs.washington.edu/papers/sigurbjarnarson-nickel.pdf
  * dolev yao model
  * proverif
  * spin
  * isabelle book 
  * https://www.cl.cam.ac.uk/~lp15/papers/Auth/
  * https://www.dmi.unict.it/giamp/ giampaulo bella
  * https://crypto.stackexchange.com/questions/34304/formal-verification-in-cryptography https://crypto.stackexchange.com/questions/5834/tools-for-modelling-and-analysis-of-cryptographic-protocols?rq=1
  * http://tamarin-prover.github.io/
  * Scyther?
  * Alloy? TLA+
  * The Mike Stay Vicary paper that started this for me
  * https://www.anilada.com/courses/15251f17/www/notes/modular-arith-crypto.pdf greg notes on crypto. Not very useful
  * https://verdi.uwplse.org/ - diostributed systesm, different but related
  * https://www.cs.cornell.edu/~shmat/shmat_survey.pdf






Relational verification

Yeah so securtity high information to low infornmation is formulated as relational execution of programs. The information is held in a "spooky" correlation of two executions. Does this give an interesting persepctive on the paramtricity theorem?

That mike stay vicary stuff

noninterference for free- bowman.

https://arxiv.org/pdf/1912.08788.pdf - binsec/rel
https://dodisturb.me/posts/2021-06-27-Typed-Programs-Dont-Leak-Data.html - imp like interpeter with securty levels.

Jif - suecrity properties in Java https://www.cs.cornell.edu/jif/

language based security https://en.wikipedia.org/wiki/Language-based_security https://www.cs.cornell.edu/andru/papers/jsac/sm-jsac03.pdf
infromation flow security
myers zdanvenic
pottier and siomething flow caml
goguen mesegauer - original nonterference paper

https://en.wikipedia.org/wiki/Information_flow_(information_theory)

is negative information flow related to declassification?

https://www.cs.cornell.edu/andru/papers/InfoFlowBelief.pdf - probability distrubtions. finite but small leakage is ok, for example checking a password.+-

Haskell embedding of DCC
http://www.cse.chalmers.se/~russo/publications_files/plas2017.pdf
https://hackage.haskell.org/package/mac
http://www.cse.chalmers.se/~russo/publications_files/pearl-russo.pdf

This Russo guy is good to look at
Secure-multi execution
information flow securioty
Doin it in idris https://link.springer.com/chapter/10.1007/978-3-030-17138-4_3

An embedding of tags into rust
https://willcrichton.net/notes/type-level-programming/



  * https://www.cs.cornell.edu/fbs/publications/HyperpropertiesCSFW.pdf hyperproperties
  * https://www.cs.purdue.edu/homes/bendy/cs590-mpl/#Barthe+SecSelfComp
  * https://alastairreid.github.io/RelatedWork/notes/information-flow/



Carette in his email, it isn't clear if he is saying finally tagless and information flow go together in some sense.
One could imagine taking the above tagged encodings and making them finally tagless.


Concurrency. 



https://www.humprog.org/~stephen//blog/research/talking-about-polymorphism.html - polymorphism is a kind of specializilation (partial evaluation is also a kind of specialization)
Boxed vs unobxed
https://thume.ca/2019/07/14/a-tour-of-metaprogramming-models-for-generics/



The abstraction theorem - is a kind of security theorem



  * O'Hearn , reynolds 70 birthday https://www.sciencedirect.com/science/article/pii/S030439750600925X
  * book of semaphores https://greenteapress.com/wp/semaphores/
  * https://danluu.com/programming-books/
  * Andrews - concurrent programming book - interesting that is starts from hoare logic. This might be a great book
  * https://www.cs.cmu.edu/~brookes/papers/seplogicrevisedfinal.pdf Brookes
  * Brinch Per Hansen - concurrent
  * Pacheco - Intro to parallel programming
  * operating systems - tenenbaum
  * principles concurrent - Ben-Ari
  * Owicki-Gries, Ashcroft. Floyd is different from hoare?
  * Resource invariant
  * schneider - on concurrent programming
  * safety v livness. safety is abscence of bad. liveness is guarantee of good. Terminating is liveness. asbence of deadlock is safety
  * mutex, semaphore, monitor
  * threads, processes, coroutines.
  * https://deadlockempire.github.io/#3-simpleCounter
  * https://lamport.azurewebsites.net/pubs/lamport-verification.pdf  https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf Specifying systems I like this lamport guy. 
  * https://github.com/cfsamson/book-green-threads-explained
  * https://pdos.csail.mit.edu/6.824/ mit dist sys course

WHat's the deal with ivy