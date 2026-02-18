---
title: "Weighted Union Find and Ground Knuth Bendix Completion"
date: 2026-02-18
---

A union find variant I think is simple and interesting is the "weighted" union find. This is distinguished from "size" or "rank" in that weight is considered a property of the id given by the user, not a internal property of the data structure <https://en.wikipedia.org/wiki/Disjoint-set_data_structure#Union_by_size> . Deciding who becomes parent of whom in a call to `union` is decided by comparing weights.

```python
from dataclasses import dataclass,field

@dataclass
class WUF():
    parents : list[int] = field(default_factory=list)
    weights : list[int] = field(default_factory=list)

    def makeset(self, weight):
        id = len(self.parents)
        self.parents.append(id)
        self.weights.append(weight)
        return id
    
    def find(self, x):
        while self.parents[x] != x:
            x = self.parents[x] 
        return x

    def tiebreak(self, x, y):
        wx, wy = self.weights[x], self.weights[y]
        if wx > wy:
            return True
        elif wy > wx:
            return False
        else:
            return True # arbitrary tie break

    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            if self.tiebreak(x,y):
                self.parents[x] = y
            else:
                self.parents[y] = x


uf = WUF()
x = uf.makeset(3)
y = uf.makeset(4)
z = uf.makeset(5)
uf.union(x, y)
uf.union(y, z)
assert uf.find(x) == x
assert uf.find(y) == x
assert uf.find(z) == x

```

# Egraph / Ground Knuth Bendix

The reason I think this is interesting is we can then lift this to use on an egraph that more closely matches ground knuth bendix completion <https://www.philipzucker.com/egraph2024_talk_done/> using a knuth bendix ordering <https://www.philipzucker.com/ground_kbo/> . Ground knuth bendix ordering is basically comparing terms by size with tie breaking.

The memo table is _for serious_ a hash cons. Each "id" describes exactly one term, not an eclass.

In hash consing it often makes sense to memoize other properties of your terms immediately at construction. This can include precomputing the hash of the node and also the size, which is merely the sum of the memoized size of the children + 1. You can also do depth or any other variation you like.

Extraction becomes trivial as it is just turning the hash consed tree with `Id` indirection back into a regular tree. The ordering makes the smallest size term extracted. Extraction is online, which may be useful.

Because `self.nodes` is in construction ordering, sweeping from front to back feels kind of nice and should hit children before parents.

Pointing to the best new terms is more like what compiler writers use Union finds for <https://pypy.org/posts/2022/07/toy-optimizer.html>

```python
type Id = int

@dataclass(frozen=True)
class App:
    f : str
    args : tuple[Id, ...]

@dataclass
class GKB():
    memo : dict[App, Id] = field(default_factory=dict) # App to Id
    nodes : list[App] = field(default_factory=list) # from Id to App
    parents : list[Id] = field(default_factory=list) # Id to Id
    weights : list[int] = field(default_factory=list) # memoized term size

    def mk_app(self, f, args):
        id = self.memo.get(App(f, args))
        if id is not None:
            return id
        else:
            id = len(self.parents)
            self.memo[App(f, args)] = id
            self.parents.append(id)
            self.nodes.append(App(f, args))
            self.weights.append(1 + sum(self.weights[arg] for arg in args))
            return id

    def find(self, x):
        while self.parents[x] != x:
            x = self.parents[x] 
        return x
    
    def tiebreak(self, x, y): # does Ground KBO basically
        wx, wy = self.weights[x], self.weights[y]
        if wx > wy:
            return True
        elif wy > wx:
            return False
        else:
            appx, appy = self.nodes[x], self.nodes[y]
            if appx.f > appy.f:
                return True
            elif appy.f > appx.f:
                return False
            else:
                assert len(appx.args) == len(appy.args) # assume same length args for now
                for ax, ay in zip(appx.args, appy.args):
                    #ax, ay = self.find(argx), self.find(argy) # perhaps do this. Changes meaning awat from terms though
                    if ax != ay:
                        return self.tiebreak(ax,ay)
                assert False, "should never reach here, tiebreak should have been resolved by now"

    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            if self.tiebreak(x, y):
                self.parents[x] = y
            else:
                self.parents[y] = x
        
    def rebuild(self):
        done = False
        while not done:
            done = True
            for id in range(len(self.nodes)):
                app = self.nodes[id]
                id1 = self.mk_app(app.f, tuple(self.find(arg) for arg in app.args))
                if self.find(id) != self.find(id1):
                    done = False
                    self.union(id, id1)


    def extract(self, id : Id):
        app = self.nodes[self.find(id)]
        return (app.f, tuple(self.extract(arg) for arg in app.args))

gkb = GKB()
a = gkb.mk_app("a", ())
a1 = gkb.mk_app("a", ())
assert a == a1
b = gkb.mk_app("b", ())
fa = gkb.mk_app("f", (a,))
fb = gkb.mk_app("f", (b,))
ffa = gkb.mk_app("f", (fa,))
ffb = gkb.mk_app("f", (fb,))
gkb.union(a, b)
gkb.rebuild()

assert gkb.find(ffa) == gkb.find(ffb)
print(gkb.extract(ffb))
gkb.union(ffa, a)
gkb.rebuild()
print(gkb.extract(ffb))
```

    ('f', (('f', (('a', ()),)),))





    ('a', ())

# Bits and Bobbles

This is another in a sequence of union find variation posts

- <https://www.philipzucker.com/context_uf2/>
- <https://www.philipzucker.com/asymmetric_complete/>
- <https://www.philipzucker.com/prim_level_uf/>
- <https://www.philipzucker.com/le_find/>
- <https://www.philipzucker.com/union-find-groupoid/>

Max has a nice small egraph implementation <https://github.com/mwillsey/microegg>
I was tinkering on some variations here <https://github.com/philzook58/microegg>

We've also been rambling up a storm on how you combine group and lattice union finds. Probably a post to come!

I liked his top down pattern matcher so I copied it into python. It's cute!
<https://github.com/philzook58/egraph-zoo/tree/main> <https://github.com/philzook58/egraph-zoo/blob/main/microegg.py>

I should show a the "linked list" version of the eclass maintenance. basically maintain a `siblings : list[int]` and splice together the chains when you union. It's an alternative to unodes.

```python
   def ematch(self, pattern: Pattern, id: Id) -> list[Subst]:
        return self.ematch_rec(pattern, id, {})

    def ematch_rec(self, pattern: Pattern, id: Id, subst: Subst) -> list[Subst]:
        id = self.find(id)
        match pattern:
            case Var(name):
                if name in subst:
                    if self.is_eq(subst[name], id):
                        return [subst]
                    else:
                        return []
                else:
                    return [{**subst, name: id}]
            case PApp(f, args):
                results = []
                for obj in self.nodes_in_class(id):
                    match obj:
                        case (f0, arg_ids) if f0 == f and len(arg_ids) == len(args):
                            todo = [subst]
                            for arg_pattern, arg_id in zip(args, arg_ids):
                                todo = [
                                    subst1
                                    for subst0 in todo
                                    for subst1 in self.ematch_rec(
                                        arg_pattern, arg_id, subst0
                                    )
                                ]
                            results.extend(todo)
                        case _:
                            raise ValueError(f"Unexpected object in e-graph: {obj}")
                return results
```
