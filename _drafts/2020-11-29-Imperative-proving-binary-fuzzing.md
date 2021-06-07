





Fuzzing is so fuckin useful. To not beusing dynamic techniques
https://github.com/mykter/afl-training afl fuzzing training

https://www.youtube.com/watch?v=sjLFf9q2NRc&ab_channel=FuzzingLabs-PatrickVentuzelo afl++ qemy
libfuzzer vs afl vs honggfuzz
corpus grammar based fuzzing, differential fuzzing




What changes do yoiu need to make to use arbitrary control flow graphs vs structured programs




https://www.lulu.com/en/us/shop/k-rustan-m-leino-and-kaleb-leino/program-proofs/paperback/product-wqy8w5.html?page=1&pageSize=4
Rustan leino book
https://github.com/backtracking/program-proofs-with-why3

Djikstra monads - this might be a stretch
F* 
Djikstra moand + interaciton trees https://www.seas.upenn.edu/~lucsil/papers/dmf.pdf
Interaction trees ~ free monad rearranged for total language
related to freer monads - kiselyov thing. This is what lexi king was working on yea?
http://hackage.haskell.org/package/freer
http://okmij.org/ftp/Haskell/extensible/more.pdf


General Monad mcbride
https://www.cis.upenn.edu/~bcpierce/papers/deepweb-overview.pdf from C to interaction trees li-yao xia






Disjkstra and Scholten
That link off of Leino

Could I make an equation style system in Z3py? Probably, right?
Take Agda as an example
Backhouse
Hehner
https://news.ycombinator.com/item?id=11797522



I've been feeling like i should be doing manual hoare logic/ imperative proofs

There is a vast assortment of tools out there that aren't proof assistants.

Boogie, dafny, frama-c, viper, verifast, whyml, why3, liquidhaskell, spark/ada, spec#
JML, ESC/java https://www.openjml.org/ whiley
esc/modula-3 

dafny
vs code plugin
https://rise4fun.com/Dafny/tutorial
https://web.cecs.pdx.edu/~apt/cs510spec/
https://dafny-lang.github.io/dafny/DafnyReferenceManual/DafnyRef
http://leino.science/dafny-power-user/ 
http://web.cecs.pdx.edu/~apt/cs510spec/


viper
vs code plugin
http://viper.ethz.ch/tutorial/


frama-c
https://alhassy.github.io/InteractiveWayToC.html
https://github.com/fraunhoferfokus/acsl-by-example


verifast tutorial
https://people.cs.kuleuven.be/~bart.jacobs/verifast/tutorial.pdf


https://github.com/hwayne/lets-prove-leftpad
vcc
ZetZZ https://github.com/zetzit/zz https://news.ycombinator.com/item?id=22245409
https://news.ycombinator.com/item?id=23997128 dafny discussion
Verilog + symbiyosys, 
KeY, KeymaeraX
CBMC, ESBMC http://www.esbmc.org/ , EBMC
cpa-checker https://cpachecker.sosy-lab.org/
TLA might be in this category
Event-B alloy


https://github.com/johnyf/tool_lists/blob/master/verification_synthesis.md god this list is nuts
https://www.pm.inf.ethz.ch/research/verifythis.html verify this
https://sv-comp.sosy-lab.org/2020/ sv-comp


https://github.com/tofgarion/spark-by-example

Eiffel for pre post conditions

https://github.com/microsoft/Armada
chalice
ATS

F*, Iris, 
VST, Bedrock
Isabelle?


It's interesting that logical psecs are so foreign, and somewhat longwinded when applied to imperative code,
that they aren't that much more understandable or high assurance.
Really it might be about formally proving equaivlance between just specs in different languages.
Python and C for example.


A good question is: what are interesting programs to prove?
1. List manipulation
2. sorts
3. red black trees
4. find

