---
date: 2024-01-22
layout: post
title: Metamath for Datalog Provenance
---

One of the interesting things about Datalog is that it has a fairly simple notion of proof or provenance. Souffle supports this feature <https://souffle-lang.github.io/provenance>. What you want to know is how a row ended up in your database. Which rule fired and what extra variables were matched on?
I really love that the canonical Datalog program is the edge-path transitivity query and the simple obvious notion of "proof object" for connectivity in a graph is a path. There's something quite nice, elementary, and deep there.

There are a number of ways to record this provenance information. One is to add an extra field/column to every table that will contain a record datatype stating the rule used and any extra info necessary.

Another is to just log out the records as you find them in linear order (or timestamps). Then a simple backwards search (prolog-like) process can reconstruct the proof. This is easier than not having this data because you only needs to search in the log above the current fact in question.

Or you can log out both the record and rule used.

Clingo <https://potassco.org/clingo/> is the easiest to install and metaprogram datalog system available today. You can pip install it, easily inject python functions into the grounding. This is extremely cool and useful. It is however actually advertised as an Answer Set Programming solver. Answer Set Programming is a logic programming paradigm which is sort of like datalog + SAT. It is commonly split into two stages, a grounder and solver. The grounder is more or less a datalog. Because it needs to share it's justification with the SAT-like solver it outputs a format that contains it.

`gringo` is the grounder and you can tell it to output a textual format. This is provenance in the first simple "loglike" style

```bash
echo "
edge(X,X+1) :- X = 1..3.
path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).
 " | gringo --text
```

```
edge(1,2).
edge(2,3).
edge(3,4).
path(1,2).
path(2,3).
path(3,4).
path(2,4).
path(1,3).
path(1,4).
```

If you attach a "choice" `{myrule}` tag to every rule, gringo has to output that also. This is provenance in the second style. This is the kind of program you write using clingo for rule selection synthesis btw.

```bash
echo "
{rule(base_path;fact;trans_path)}.
edge(X,X+1) :- X = 1..3, rule(fact).
path(X,Y) :- edge(X,Y), rule(base_path).
path(X,Z) :- edge(X,Y), path(Y,Z), rule(trans_path).

%*
Bash Command: gringo path.lp --text
Result:
{rule(base_path);rule(fact);rule(trans_path)}.
edge(1,2):-rule(fact).
edge(2,3):-rule(fact).
edge(3,4):-rule(fact).
path(1,2):-rule(base_path),edge(1,2).
path(2,3):-rule(base_path),edge(2,3).
path(3,4):-rule(base_path),edge(3,4).
path(2,4):-rule(trans_path),path(3,4),edge(2,3).
path(1,3):-rule(trans_path),path(2,3),edge(1,2).
path(1,4):-rule(trans_path),path(2,4),edge(1,2).
*%
 " | gringo --text
```

# Metamath

Metamath <https://us.metamath.org/downloads/metamath.pdf> <https://us.metamath.org/> is a really interesting proof system. I

- Not new. It was started in the early nineties
- Significant set theory library.
- Requires way less background in my opinion to understand what they are talking about. The church of dependent type theory has many many (cool) concepts that can bve overwhelming.
- It also has a compressed proof format.
- It is constructed in such a way that it is not burdensome to write a fast low level verifier. Mario Carneiro's metamath zero <https://github.com/digama0/mm0> is a case in point. This is perhaps the system closest to the needs of extremely descriptive proof carrying code. It's very stack-y.
- It has the minimal but direct constructs you need to describe inference rules.
`$e` tags introduce assumptions for rules, and `$a` introduces the conclusion to inference rules

```metamath
l1 $e stuff1 $.
l2 $e stuff2 $.
myax $a mydude $.
```

is like asserting an inference rule

```metamath
l1 stuff1      l2 stuff2
----------------------- myax
      mydude
```

Proofs are described in a depth first manner. It's not that different from writing a bussproof in latex if you have done such a think. It can also be thought of as manipulating a stack of obligations and goals.

Encoding datalog provenance to metamath seems quite directly possible like so:

We need constants for every relation. A relation is stored as a string `reltag entry1 entry2 entry3`. Each inference/datalog rule becomes a metamath rule. bada bing bada boom.

```bash
echo '
$c path edge vert 1 2 3 4 $.
$v x y z $.
vert1 $a vert 1 $.
vert2 $a vert 2 $.
vert3 $a vert 3 $.
edge12 $a edge 1 2 $.
edge23 $a edge 2 3 $.
vertx $f vert x $.
verty $f vert y $.
vertz $f vert z $.
edgexy $e edge x y $.
basepath $a path x y $.
path12 $p path 1 2 $=
  vert1 vert2 edge12 basepath $.
path23 $p path 2 3 $=
  vert2 vert3 edge23 basepath $.
pathyz $e path y z $.
transpath $a path x z $.
path13 $p path 1 3 $=
  edge12 vert1 vert2 vert3 path23 transpath $.

' > /tmp/path.mm
metamath 'read "/tmp/path.mm"' "verify proof *" "exit"
```

# Bits and Bobbles

There are other systems in the running for intermediate proof formats. [Dedukti](https://deducteam.github.io/), [alethe](https://arxiv.org/abs/2107.02354), LFSC, straight coq or lean etc.

 Now this very raw encoding may not play nice with set.mm. Maybe it should be more refined

Does this enable datalog as a automated theorem prover for metamath developments?

Sorry, I ran out of steam bringing the edges together between the clingo provenance and metamath. It's just muscle grease (I think)

You can also observe the grounding from the python interface.

I've been thinking there could be utility in expanding mmverify.py <https://github.com/david-a-wheeler/mmverify.py> into a library perhaps for use in knuckedragger

```python
import clingo

prog = """
{rule(base_path;fact;trans_path)}.
edge(X,X+1) :- X = 1..3, rule(fact).
path(X,Y) :- edge(X,Y), rule(base_path).
path(X,Z) :- edge(X,Y), path(Y,Z), rule(trans_path).
"""
ctl = clingo.Control()
ctl.add("base", [], prog)


def lit2symbol(n):
  return list(ctl.symbolic_atoms)[n-1].symbol

class Provenance(clingo.Observer):
  def rule(self, choice, head, body):
    print(choice, list(map(lit2symbol,head)), list(map(lit2symbol,body)))

ctl.register_observer(Provenance())
ctl.ground([("base", [])])
```

path proofs in metamath

```metamath
$c vert path edge a b c d e f $.
$v x y z $.
$f vert x $.
$f vert y $.
$f vert z $.

min $e edge x y $.
base-path $a path x y $.

maj $e path y z $.
trans-path $a path x z $.

verta $a vert a $.
vertb $a vert b $.
vertc $a vert c $.
$a vert d $.
$a vert e $.

edgeab $a edge a b $.
edgebc $a edge b c $.

pathac $p path a c $.

```

In many cases, a "proof" is some artifact containing enough breadcrumbs to figure out the relevant bits of a trace of some proof search. If a system does not support this, it can be added sometimes as a tracing parameter.

Every rule can store the appropriate bindings in an extra parameter. Then you can know what rules fired

The "proof" of a connectivity query is the path.

You often need some kind of lattice action to make this converge since there are infinitely many paths in any grph with cycles.

A timestamp can be sufficnet breadcrumb. Timestamp is similar to proof depth. Take the min lattice.

Optimization over datalog provenances?

Set of support provenance. This doesn't work in datalog, because we can't detect loops. But we could use ASP negation.

```
{support(path(A,B), edge(X,Y))} :- path(A,B), edge(X,Y), path(Y,Z), not support(edge(X,Y), path(Y,Z))
```

Does the search aspect of ASP add anything to this datalog provenance story? Hmm.
In SAT, the "proof" object is the unsat certificate, a resolution chain. I don't know if stock ASP solvers output something like this for UNSAT. The extra twist is that it may be unsat for justification issues.

```clingo



```

Using gringo.
Gringo grounds datalog programs, but it does so online. Actually since it requires

Outputting the datalog derivations in order actually does help a lot in terms of reonctructing proofs. Facts can only have been derived by facts appearing above. A prolog process can now reconstruct proofs without getting nto loops

These are essentially timestamps.

If we make everything conditional on a nondetermisitc variable, the grounder will actually display the entire rule derivation body. Cute huh?

```bash
echo "
{c}.
edge(X,X+1) :- X = 1..5, c.
path(X,Y) :- edge(X,Y), c.
path(X,Z) :- edge(X,Y), path(Y,Z), c.
 " | gringo --text
```

```prolog
{c}.
edge(1,2):-c.
edge(2,3):-c.
edge(3,4):-c.
edge(4,5):-c.
edge(5,6):-c.
path(1,2):-c,edge(1,2).
path(2,3):-c,edge(2,3).
path(3,4):-c,edge(3,4).
path(4,5):-c,edge(4,5).
path(5,6):-c,edge(5,6).
path(4,6):-c,path(5,6),edge(4,5).
path(3,5):-c,path(4,5),edge(3,4).
path(2,4):-c,path(3,4),edge(2,3).
path(1,3):-c,path(2,3),edge(1,2).
path(1,4):-c,path(2,4),edge(1,2).
path(2,5):-c,path(3,5),edge(2,3).
path(3,6):-c,path(4,6),edge(3,4).
path(2,6):-c,path(3,6),edge(2,3).
path(1,5):-c,path(2,5),edge(1,2).
path(1,6):-c,path(2,6),edge(1,2).
```

You could use such a trace to do differential datalog. You can delete facts. Then delete any rule that depends on that fact. If that is the last rule with that head, recursively delete derivations using that rule.
You can also delete or add rules similarly. Just delete any instantiations with the rule tag.

 You can also name rules if you like

This is the same sort of program you would write for conditionaly turning rules on an off (selecting datalog rules under some criteria).

```
#script(python)

path_ = {}
def path(x,y):
  if (x,y) in path_:
    return False
  else:
    return clingo.Const("true")

#end.

% a "lattice" like effect of only recording first derivation
path(X,Y) :- edge(X,Y), path(X,Y), @path(X,Z) = true.
```

What about negation?

# Metmath Proofs
