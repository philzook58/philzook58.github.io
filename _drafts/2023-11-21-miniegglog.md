
```python



grammar = """

"""


class EGraph:
    uf: List[int]
    funcs: Dict[str,Dict[Any, int]]

    def find(self,x):
        while x != self.uf[x]:
            x = self.uf[x]
        return x
    def union(self,x,y)
        x = self.find(x)
        y = self.find(y)
        if x != y:
            self.uf[x] = y
        return y
    def rebuild(self):
        for f,tbl in self.funcs.items():
            for x,y in tbl.items()
                x1 = map(self.find, x)
                y1 = find(y)
                tbl[x1] = y1
    def matcher(self, name, *args):
        def res(*args):
            #if len(args) == 1 and args[0] == None:
            #    return None
            #return self.funcs[name].get[map(self.find,args)]
            return self.funcs[name][map(self.find,args)]
        return res
    def add(self, name, *args):
        if name not in self.funcs:
            self.funcs[name] = {} # MergeDict
        if args not in self.funcs[name]:
            self.funcs[name][args] = len(self.uf)
            self.uf.append(len(self.uf))
        return self.funcs[name][args]
    def bind(self, varnum, f):
        for x in range(len(self.uf)):
            pass
    def __iter__(self):
        return iter(self.uf)    



egraph = Egraph()
f = egraph.matcher("f")
a = egraph.matcher("a")

# This is nice. Shallow embedding of the environment.
for x in range(len(self.uf)): # self.funcs.values()
    for y in range(len(self.uf)):
        try:
            t1 = egraph.matcher("f")
            t2 = f(x)
            egraph.union(t1,t2)
        except KeyError:
            pass

egraph.bind(2, lambda (x,y): egraph.union(f(x,y), f_(y,x))) # f[(x,y)] = f[(y,x)]
# [f[(x,y)] := g[z,w] for z in egraph for w in egraph]
egraph.rebuild()

class MergeDict(dict): # defaultdict
    def __init__(self,merge,default):
        self.merge = merge
        self.default = default
    def __getitem__(self, key):
        if key in self:
            return super().__getitem__(key)
        else:
            super().__setitem__(key, self.default) # ?
            return self.default
    def __setitem__(self, key, value):
        if key in self:
            super().__setitem__(key, self.merge(super().__getitem__(key), value))
        else:
            super().__setitem__(key, value)
```

```python

egraph = {
    ("a", ()) : 1,
    ("b", ()) : 2,
    ("+", (1,2)) : 3
}
# eh, why bother.

```
