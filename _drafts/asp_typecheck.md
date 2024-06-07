
I really liked
<https://arxiv.org/abs/1908.05839>

Demand transformation.
Datalog with constructors or arithmetic can go off into the stratosphere. One way to control this is to create demand relations.

For example, we can comute a fibonacci function

```souffle
.decl fib(n : number, m : number)
.decl needfib(n : number)

needfib(n-1) :- needfib(n), n >= 1.
needfib(n-2) :- needfib(n), n >= 2.

fib(0,1).
fib(1,1).
fib(n,a + b) :- needfib(n), fib(n-1,a), fib(n-2 ,b).

needfib(5).
.output fib
.output needfib
```

```clingo
needfib(N - 1) :- needfib(N), N >= 1.
needfib(N - 2) :- needfib(N), N >= 2.

fib(0,1).
fib(1,1).
fib(N,A + B) :- needfib(N), fib(N-1,A), fib(N-2,B).

```

```souffle
type
.decl need-type()


```

```clingo
need()
need()

checks()
synth()

```

See frank pfenning where he has different notions of arrow.
slog
egglog
functional compiling

Another related idea:
Pick priorities for parser operators to mnimize parentheses
Pick juxtaposition operator to minimize parentheses. How would I do this?
