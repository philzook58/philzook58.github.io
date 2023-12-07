
# Datalog Pronenance

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

```bash
echo "
edge(X,X+1) :- X = 1..5.
path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).

 " | gringo --text
```

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

%edge(1,5) :- rule(fact). % just to see what multiple proof pathways looks like


% negation
% hmm doesn't work. Because maybe the rules don't fire.
%{rule(not_path)}.
%vert(X) :- edge(X,Y).
%vert(Y) :- edge(X,Y).
%not_path(X,Y) :- vert(X), vert(Y), not path(X,Y), rule(not_path).
 " | gringo --text
```

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
