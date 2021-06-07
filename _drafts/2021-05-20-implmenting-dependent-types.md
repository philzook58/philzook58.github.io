
http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html
http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/
https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf a tutorial implementation of dependtly typed lambda calc http://lambda-the-ultimate.org/node/2340
https://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf - Brady thesis
https://asset-pdf.scinapse.io/prod/2145108549/2145108549.pdf - idris design and implementation
mini-tt  http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf
Weirich OPLSS 2013 https://www.seas.upenn.edu/~sweirich/papers/tfp07.pdf easy as pie



Notes on Simply Easy
They choose values in HOAS but terms in locally nameless
This is NBE?

whnf - weak head normal form
neutral term
normal form
head normal form

Notes on bauer
- Bauer 1 2 3 use different implementation techniques?
- 1 tries to gensym everything
- 2 tries to use NBE
- 3 does de bruijn substitution


Untyped
Simply typed
Dependently types




https://www.youtube.com/watch?v=MhYbLS6XiZo&ab_channel=LecturesbyProf.EadesatAU
Atkey
resource constrained programming. implicit computational compelxity theory


notes:
Elaborator is hard cody says
3 ideas:
1. terms types and kinds as 3 variants of same process (PTS)
2. bidirectional typing
3. hoas / nbe


They use de bruijn indices on term and hoas on vlaues.
Is this necessary? Obvious?
Quote is some kind of reflection.
infer -check inversion is where you do conversion check


Only normal forms
values and neutral
Value vs neutral is a distinction you need to define normal forms
not allowed to put construcotr in eleimination form
By construction these are stuck
Kind of like how non empty list is `data NonEmpty a = Head a [a]`

normal forms = value + neutral. 

borithogonality?


type checking does or doesn't need subsitution
