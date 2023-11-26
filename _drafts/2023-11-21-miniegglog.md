
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
                x1 = tuple(self.find(z) for z in x)
                y1 = find(y)
    def matcher(egraph, name):
        func

```
