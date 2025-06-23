---
title: "Telescopes Are Tries: A Dependent Type Shellac on SQLite" 
date: 2025-06-22
---

It seems to me that telescopes <https://ncatlab.org/nlab/show/type+telescope> , the dependently typed notion of context, is more central to the topic of dependent types than the dependent types are.

A telescope is a sequence of variables and their type such that later types in the sequence can depend on the earlier variables.

`[x : A, y : B(x), z : C(x,y)]`

These are the things often written as $\Gamma$ in a typing judgement $\Gamma \vash t : A$ if you've seen such a thing. Another example might be `[A : Type, n : Nat, x : Vec n A]` for a having a list that is type constrained to be of length `n` in your current context.

I have continued to think about this blog post <https://www.philipzucker.com/frozenset_dtt/> which I rather like. By being vague and borrowing from the metalevel of python, I can kind of outline combinators that describe the simple finite set theoretic model of dependent type theory. This is a highly semantic approach to thinking about type theory and rarely the direction I see people go. Maybe they think it is so obvious it isn't worth mentioning or also they approach type theory as foundational and hence don't really want to appeal to some shitty half correct set-ty intuition to justify their inference rules. <https://ncatlab.org/nlab/files/MartinLofOnTheMeaning96.pdf>

The connection I made in that blog post is that this nested binding in telescopes is very similar to the binding structure you can have with nested for loops in an ordinary programming language

```python
for x in A:
    for y in B(x):
        for z in C(x,y):
            pass
```

Then, somewhat vaguely, the set of python contexts that appear inside that loop represents of models the syntax of the telescope. In other words, the runtime environments $\rho$ are the things in the typing context $\Gamma$.

# Telescopes Are Tries

On a walk I realized really that there is a more straightforward and less weird direct "thing" we can talk about to represent telescopes: Tries. <https://en.wikipedia.org/wiki/Trie>

Tries are mappings that takes keys that are sequences. They are very useful data structures for string algorithms for example, because strings are sequences of characters.

Tries can be implemented multiple ways, but one way is as nested dictionaries. These dictionaries can be seen as kind of lazy iterated cartesian products.

```python
{ x : {  y : {z : () for z in C(x,y)}  for y in B(x) }  for x in A}
```

Here's a simple example of a dependent context

```python
from enum import Enum
Bool = frozenset([True, False])
RGB = Enum("RGB", "R G B")
Unit = frozenset([()])

# [x : Bool, y : if x then RGB else Unit |- str(y) : String
ex1 = {x :{ y : str(y) for y in (RGB if x else Unit)} for x in Bool } 
ex1

```

    {False: {(): '()'},
     True: {<RGB.R: 1>: 'RGB.R', <RGB.G: 2>: 'RGB.G', <RGB.B: 3>: 'RGB.B'}}

In Lean, this example written as a function might look like

```python
%%file /tmp/tele.lean
inductive RGB where
    | R : RGB
    | G : RGB
    | B : RGB

-- You would have a tough time writing this exact program in Haskell or Ocaml
def ex1 (x : Bool) (y : if x then RGB else Unit) : String :=
    match x with
    | true => match y with
        | RGB.R => "Red"
        | RGB.G => "Green"
        | RGB.B => "Blue"
    | false => match y with
        | () => "Unit"

def main : IO Unit := do
    IO.println (ex1 true RGB.R)
    IO.println (ex1 true RGB.G)
    IO.println (ex1 true RGB.B)
    IO.println (ex1 false ())
```

    Overwriting /tmp/tele.lean

```python
! lean --run /tmp/tele.lean
```

    Red
    Green
    Blue
    Unit

It is indeed a very mild usage of dependent types. It would not be so easy to write such a thing with these types in Haskell / Ocaml etc without some trickiness (singletons gadts etc).

# Relating Relational and Telescope Style Conjunctive Queries

Any telescope can be rewritten as a conjunctive query <https://en.wikipedia.org/wiki/Conjunctive_query> . Conjunctive queries look the like bodies of datalog rules.

If we take the convention that every n-argument "dependent type" is actually just a notation for an n+1 relation, we can turn telescopes into conjunctive queries. `[x : A, y : B(x), z : C(x,y)]` becomes $A(x) \land B(x,y) \land C(x,y,z)$. Perhaps writing `z : C(x,y)` as `elem(C(x,y),z)` and then fusing/flattening `elem` with `C` to `C'(x,y,z)` makes this more clear. We do have a notation to refer to a first class set, which is kind of interesing. Not sure how important this is.

This can in turn can be written as the SQL query. SQL binds rows rather than the elements in the rows like a conjunctive query / datalog body does. It is however quite mechanical to translate them.  <https://www.philipzucker.com/tiny-sqlite-datalog/>

```SQL
FROM A as a 
FROM B as b 
FROM C as c 
WHERE
a.v0 = b.v0 AND
b.v1 = c.v1 AND
a.v0 = c.v0
```

Vice versa can also be achieved in various ways.

$T(x,y) \land T(y,z) \land T(z,x)$ becomes `[x : Int, y : Int, z : Int, p1 : T(x,y), p2 : T(y,z), p3 : T(z,x)]`  or we could try to move the telescope around a little, which corresponds to lifting up loop invariant code in a for loop to `[x : Int, y : Int, p1 : T(x,y), z : Int, p2 : T(y,z), p3 : T(z,x)]`

It seems in general it is easier to convert a telescope to a nice conjunctive query form than vice versa. Conjunctive queries have no restrictions on there being a nice ordering to the variables. There may not be a nice ordering or finding it is a task.

I've notice in knuckledragger, which is a Hilbert style system that having your theorems in a "standard form" helps you write proof combinators that correspond to dependent type or sequent calculus rules. John Harrison's book makes a similar observation.

Telescopes and Conjunctive queries kind of correspond to two "standard forms" you might like your logical formulas to appear as

- "Sequent form" $\forall x y z ... , ( A \land B \land C ...)  \implies P$
- Telescope form $\forall x, A(x) \implies (\forall y, B(x,y) \implies (... \implies P))$

Always working in these two forms let's you form Hilbert style combinators that corresponds to sequence calculus rules or rules that look more like dependent type theory rules.

## SQL-izing telescopes

The thing that tries also triggers in my brain is database queries and worst case optimal join <https://arxiv.org/pdf/2301.10841> which also are intimately connected to `for` loops.

There is also strong correspondence between basic SQL queries and `for` loops. <https://www.philipzucker.com/sql_graph_csp/>

Basically, the for loops correspond to the `FROM` statements, `if` statements correspond to `WHERE` clauses, and `yield` corresponds to `SELECT`

I'm abusing the python ast parsers like here <https://github.com/true-grue/python-dsls/blob/main/datalog/datalog_test.py> to get a DSL without writing a parser. I'm reusing the python type comment syntax which if you squint lookx like a typing judgement. To make this more complete, I should support more interesting expressions inside the arguments of types and in the result type.

```python
def to_query(has_type : str):
    x = ast.parse(has_type, mode="func_type")
    body = x.argtypes
    FROMS = []
    WHERES = []
    env = {}
    for bind_num, binding in enumerate(body):
        match binding:
            case ast.Compare(left=ast.Name(id=var_name), ops=[ast.In()], comparators=[ast.Call(func=ast.Name(id=type_name), args=args, keywords=[])]):
                row = var_name + "_row"
                FROMS.append(f"{type_name} as {row}")
                env[var_name] = row + ".elem"
                for n,arg in enumerate(args):
                    WHERES.append(f"{env[arg.id]} = {row}.x{n}")
            case _:
                raise ValueError(f"Ill formed binding", ast.unparse(binding), ast.dump(binding))
            
    match x.returns:
        case ast.Compare(left=ast.Name(id=t), ops=[ast.In()], comparators=[ast.Call(func=ast.Name(id=type_name), args=args, keywords=[])]):
            selects = [f"{env[arg.id]}" for arg in args] + [env[t]]
            return f"INSERT INTO {type_name} SELECT {", ".join(selects)}" + "\nFROM\n" + ",\n". join(FROMS) + "\nWHERE\n" + " AND\n".join(WHERES)
        case _ :
            raise ValueError("Ill formed return type", ast.unparse(x.returns), ast.dump(x.returns))




```

    INSERT INTO Path SELECT x_row.elem, y_row.elem, p_row.elem
    FROM
    Vert as x_row,
    Vert as y_row,
    Edge as p_row
    WHERE
    x_row.elem = p_row.x0 AND
    y_row.elem = p_row.x1

We can show a transitive closure query.

Read the following as `x : Vert, y : Vert, p : Edge(x,y), z : Vert, q : Path(y,z) |- p : Path(x,z)`

```python
print(to_query("(x in Vert(), y in Vert(), p in Edge(x,y), z in Vert(), q in Path(y,z)) -> p in Path(x,z)"))
```

    INSERT INTO Path SELECT x_row.elem, z_row.elem, p_row.elem
    FROM
    Vert as x_row,
    Vert as y_row,
    Edge as p_row,
    Vert as z_row,
    Path as q_row
    WHERE
    x_row.elem = p_row.x0 AND
    y_row.elem = p_row.x1 AND
    y_row.elem = q_row.x0 AND
    z_row.elem = q_row.x1

```python
print(to_query("(x in Vert(), y in Vert(), p in Edge(x,y)) -> p in Path(x,y)"))
```

    INSERT INTO Path SELECT x_row.elem, y_row.elem, p_row.elem
    FROM
    Vert as x_row,
    Vert as y_row,
    Edge as p_row
    WHERE
    x_row.elem = p_row.x0 AND
    y_row.elem = p_row.x1

And lo and behold, we can actually run them too.

```python
import sqlite3
db = sqlite3.connect(":memory:")
db.execute("CREATE TABLE Vert (elem INTEGER)")
db.execute("CREATE TABLE Edge (x0 INTEGER, x1 INTEGER, elem INTEGER)")
db.execute("CREATE TABLE Path (x0 INTEGER, x1 INTEGER, elem INTEGER)")
db.execute("INSERT INTO Vert VALUES (1), (2), (3)")
db.execute("INSERT INTO Edge VALUES (1,2, -1), (2,3,-1)")
db.execute(to_query("(x in Vert(), y in Vert(), p in Edge(x,y)) -> p in Path(x,y)"))
db.execute("SELECT * FROM Path").fetchall()
```

    [(1, 2, -1), (2, 3, -1)]

```python
db.execute(to_query("(x in Vert(), y in Vert(),  p in Edge(x,y), z in Vert(), q in Path(y,z)) -> p in Path(x,z)"))
db.execute("SELECT * FROM Path").fetchall()
```

    [(1, 2, -1), (2, 3, -1), (1, 3, -1)]

```python

```

# Bits and Bobbles

It would be interesting to take Telescopes are tries deeply into the database system. I think down this road lies an interesting idea of a dependently typed egraph. Asserting definitional equality would be the analog of an egglog union. This is ultimately not that surprising. Generalized Algebraic theories was one of the original motivations of egglog. See also Bidlingmaier Eqlog.

Something interesting is that the "Type" gives you a way to refer to the collection of things that all have the same first N columns. These are first class sets.

Singleton tables are a way of removing WHERE statements in favor of more FROM clauses.

Would `Id x y` want to be a first class union find? Bolting in theories, one could make `p : Id x y` be the sense in which x and y are equal, such that the group element that connects them.
`7 : Id x y` <===> `x + 7 = y` . We may want to quotient by these notions of equality sometimes, but still be able to observe them sometimes also. Such as slotted egraphs, quotienting by alpha in one sense, and not quotiented by another.

# Provenance and Proof objects

An interesting topic in datalog / database is provenance, knowing how a fact ended up in the database. This is a richer notion of truth value / proof object that just being in there or not.

This also jives with the above perspective of `p : Path(x, y)` being kind of having a secret extra parameter in te relation `Path(x,y,p)` because this is basically how provenance is implemented. Souffle only records a single best provenance. This is evocative of proof irrelevance in type theory. We could also choose to store _all_ possible proof objects, which probably doesn't terminate, or some more sophisticated truncation like semiring provenance.

<https://arxiv.org/abs/2202.10766> Revisiting Semiring Provenance for Datalog
<https://souffle-lang.github.io/provenance>

Using sympy it might be easy ish to actually do this stuff on sqlite. You can make connectors to store python objects in sqlite databases

# Category of Tries

If we lookup a trie with an incomplete key, that's kind of like currying the trie. The value the trie mapping maps to from that perspective is another trie.

If you makes tries map to trie keys, tries actually can be composed. They form a category. This category corresponds to context mappings in type theory <https://www.philipzucker.com/tele/>  <https://proofassistants.stackexchange.com/questions/2557/what-is-a-context-mapping-in-dependent-type-checking>

Tries are mappings from their keys to their values. Tries are themselves kind of the set of their keys. Any mapping data structure is kind of a set if you just put `()` as the held value.

```python
def lookup(trie, key):
    subtrie = trie
    for v in key:
        subtrie = subtrie.get(v)
        if trie is None:
            return None
    return subtrie

lookup( ex1 , [True, RGB.R])
```

```python
#type trie_morph = tuple["trie", int] # a trie morphism is a trie and an integer saying at which point the domain is separate from the codomain. Maybe carrying more dom/cod data would be better.
type trie_morph = object

def id_(trie0, n) -> trie_morph:
    def worker(trie, curkey):
        if trie == ():
            return curkey
        else:
            return {k: worker(v, curkey + [k]) for k, v in trie.items()}

def items(trie):
    def worker(trie, curkey):
        if not isinstance(trie, dict):
            yield (curkey, trie)
        else:
            for k, v in trie.items():
                yield from  worker(v, curkey + [k]) 
    return worker(trie, [])

def trie_map(trie, f):
    def worker(trie):
        if not isinstance(trie, dict):
            return f(trie)
        else:
            return {k: worker(v) for k, v in trie.items()}
    return worker(trie)

def trie_map_with_key(trie, f):
    def worker(trie, curkey):
        if not isinstance(trie, dict):
            return f(curkey, trie)
        else:
            return {k: worker(v, curkey + [k]) for k, v in trie.items()}
    return worker(trie, [])

def id1(trie0): # alternative way of writing id
    trie_map_with_key(trie0, lambda k, x: k)

def compose(trie0 : trie_morph, trie1 : trie_morph) -> trie_morph:
    return trie_map(trie0, lambda x: lookup(trie1, x))
```

The judgements that go under a context are

- $\Gamma \vdash A type$ - A trie with keys $\Gamma$ that has a type (frozenset) as it's held value
- $\Gamma \vdash t : A$ - A trie with keys $\Gamma$ that has the pair of a type and a value in the type as it's held value.

The things to the right of $\vdash$ should be the values being held in the trie.

This helps me reconcile for example that `True` and `False` aren't the only things in Bool if you're not in an empty context like `x : Bool |- t : Bool`. This is because there are tries that have `True` at every leaf, which is sort of the trie-lift or trie-const form of bool, but there are also tries of course who's value depends on which branch of the trie you're in. These trie correspond to terms `t` that depend on the context variables.

```python
def const_trie(trie, ntrie, value):
    if ntrie <= 0:
        return value
    else:
        return {k: const_trie(subtrie, ntrie - 1, value) for k,subtrie in trie.items()}
const_trie(ex1, 2, 42)
```

# Knuckledragger style telescope to sqlite

i made a small datalong in knuckledragger
<https://github.com/philzook58/knuckledragger/blob/main/kdrag/solvers/datalog.py>

```python

```

```python
from kdrag.all import *
type tele_env = dict[smt.ExprRef, str] # a mapping from variable name to where to find there in the sql query

def compile(tele_rule : smt.ExprRef):
    FROMS = []
    WHERES = ["true"]
    while isinstance(tele_rule, smt.QuantifierRef):
        assert smt.is_forall(tele_rule)
        [v], body = kd.open_binder_unhygienc(tele_rule)
        assert smt.is_implies(body)
        typ, tele__rule = body.arg(0), body.arg(1)
    SELECT = f"INSERT INTO {f.decl().name()} SELECT {", ".join(f.children())}"
    query = f"{SELECT} FROM {', '.join(FROMS)} WHERE {' AND '.join(WHERES)}"
    return query

IntSet = smt.SetSort(smt.IntSort())
Vert = smt.Const("Vert", IntSet)
Unit = kd.Enum("unit", "tt")
Edge = smt.Function("Edge", smt.IntSort(), smt.IntSort(), Unit)
Path = smt.Function("Path", smt.IntSort(), smt.IntSort(), Unit)
kd.QForAll([x], Vert, kd.QForAll([y], Vert, kd.QForAll([p], edge(x,y))))

x,y,z = smt.Ints("x y z")
kd.TForAll([(x)])



```

Relations `Set (A,B)` are the same thing (isomorphic to) functions/dictionaries to sets aka multivalued functions.

```python
from collections import defaultdict
rel1 = {(1,True,2), (2,False,3), (2,False,4)}
fun1 = {(1,True) : {2},  (2,False) : {3, 4}}

def rel_to_fun(rel):
    fun = defaultdict(set)
    for xs in rel:
        key, res = xs[:-1], xs[-1]
        fun[key].add(res)
    return fun

rel_to_fun(rel1)

```

    defaultdict(set, {(2, False): {3, 4}, (1, True): {2}})

```python
def fun_to_rel(fun):
    rel = set()
    for key, res in fun.items():
        for r in res:
            rel.add(key + (r,))
    return rel
fun_to_rel(fun1)
```

    {(1, True, 2), (2, False, 3), (2, False, 4)}

So we can take the convention on SQL tables that the table `C` with 3 columns is actually representing a multivalued function from the first 2 columns to the third.

Subsingleton/Propositions <https://ncatlab.org/nlab/show/subsingleton> are tables with an actual functional dependency between the inputs and output. There is either no key or just one.

This is kind of a cute way to replace an `if` statements with a `for` loop.

Analogously, in SQL, a `WHERE` clause can be replaced by a table that is either empty or has one row for that key.

```python
if True:
    print("its true")

if False:
    print("shouldn't print")
```

    its true

```python
for x in ["just one thing"]:
    print("also true")

for x in []:
    print("shouldn't print")
```

    also true

```python
import sqlite3

con = sqlite3.connect(":memory:")
cur = con.cursor()
cur.execute("CREATE TABLE rel1 (x,y,z)")
cur.executemany("INSERT INTO rel1 VALUES (?,?,?)", rel1)
cur.execute("SELECT * FROM rel1").fetchall()
```

```python
from sympy import *
x, y, z = symbols('x y z')
# make a semiring mod x**2 - 1
from sympy.abc import x
from sympy import QQ
QQ.old_poly_ring(x).quotient_ring(QQ.old_poly_ring(x).ideal(x**2))
QQ.old_poly_ring(x).quotient_ring([x**2])

s, c = symbols('s, c')
QQ.old_poly_ring(s, c) / [s**2 + c**2 - 1]
```

    QQ[s,c]/<c**2 + s**2 - 1>

```python

```

```python

```

```python

```

# Bits and Bobbles

<https://github.com/true-grue/python-dsls/blob/main/datalog/datalog_test.py>

```python
#def Tele(x, A, cb):
import ast
#print(ast.dump(ast.parse("[x in int, b in int] >= t in A", mode="eval"), indent=4))
ast.dump(ast.parse("(x in A, y in B) -> t == t1 in A", mode="func_type"), indent=4)
print(ast.dump(ast.parse("x : A; y : B; t == t1 in A", mode="exec"), indent=4)) # yield, asset
#print(ast.dump(ast.parse("[x in int, b in int] => x in B")))

```

    Module(
        body=[
            AnnAssign(
                target=Name(id='x', ctx=Store()),
                annotation=Name(id='A', ctx=Load()),
                simple=1),
            AnnAssign(
                target=Name(id='y', ctx=Store()),
                annotation=Name(id='B', ctx=Load()),
                simple=1),
            Expr(
                value=Compare(
                    left=Name(id='t', ctx=Load()),
                    ops=[
                        Eq(),
                        In()],
                    comparators=[
                        Name(id='t1', ctx=Load()),
                        Name(id='A', ctx=Load())]))],
        type_ignores=[])

What does cross stage get us? We get to produce python code.

```python
import z3
# cross stage persistence
def cross(e : z3.ExprRef) -> str:
    return f"z3.deserialize(\"{e.serialize()}\")".replace("\n", "")

def mypow(n : int, e : z3.ExprRef) -> str:
    if n == 0:
        return cross(e)
    else:
        return f"{cross(e)} * {mypow(n - 1, e)}"

eval(cross(z3.Int('x')))
eval(mypow(3, z3.Int('x')))

def mypow1(n, e):
    if n == 0:
        return e
    else:
        return e * mypow1(n - 1, e)
mypow1(3, z3.Int('x'))
```

x&middot;x&middot;x&middot;x

```python
z3.deserialize("(declare-fun F (Int) Bool)\n(declare-fun x () Int)\n(assert (F x))\n")
```

x

```python
print(ast.dump(ast.parse("""
for x in range(7): # type: int
    print(x)
""",type_comments=True), indent=4))
ast.unparse
ast.literal_eval("(1,2)")
ast.literal_eval("")
```

    Module(
        body=[
            For(
                target=Name(id='x', ctx=Store()),
                iter=Call(
                    func=Name(id='range', ctx=Load()),
                    args=[
                        Constant(value=7)],
                    keywords=[]),
                body=[
                    Expr(
                        value=Call(
                            func=Name(id='print', ctx=Load()),
                            args=[
                                Name(id='x', ctx=Load())],
                            keywords=[]))],
                orelse=[],
                type_comment='int')],
        type_ignores=[])





    (1, 2)
