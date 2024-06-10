
Logical relations. A relation defined inductively on types (often)

But then we induct on typing derivations to show that terms stay in the semantic relation.

```python
from z3 import *
Type = Datatype("Type")
Type.declare("Bool")
Type.declare("Arr", ("a", Type), (b, Type))
Type.declare("ForAll", ("a", ArraySort(StringSort(),Type)))
Type.declare("TVar", ("v", StringSort()))

# Any = Term
Any = Datatype("Any")
Any.declare("Fun", ("x", ArraySort(StringSort(),Any))) # not ok. But if I stick to wf, it is ok. hmm
Any.declare("Bool", ("x", BoolSort()))
Any.declare("BigLambda", ("x", ArraySort(Type, Any)))



def typeof(sort): #wf
    wf = Function("wtypeof", sort, Type, BoolSort())
    match sort:


parametric = Function("para", Type, Any, Any, BoolSort()) #?


Context = ArraySort(StringSort(), Type)
C
Subst = ArraySort(StringSort(), Any)

wf_def = ForAll([x], wf(ctx, x, ty) == Or(ty == Type.Bool,  And(Type.is_TVar(ty), ctx[Type.t(ty)) == Type.Bool))
```

```python

Bool = [(True, True), (False,False)]
Int = [(i,i) for i in range(8)]

# a function
Not = [(x, not x) for x in [True,False]]


# imagine a world where we implement using strings?
[(i, str(i)) for i in range(10)]  # decimal strrings/ hex strings
[(i, "1" * i) for i in range(10)]  # unary strings

# This is a parametric function. 
id_ = Bool + Int



Arr = Callable

# a test if parametric?
def parametric(ty):
    def res(R):
        match ty:
            case bool:
                return R in Bool
            case int:
                return R in Int
            case Arr[a,b]:
                input = parametric(a)
                [f[x], g[y]  for (x,y) in input for (f,g) in R for]

#step indexing



```

The opening paragraph to Reynolds paper is more interesting maybe than the body.

It considers constructing complex numbers as t-theta radius angle pairs vs x-y cartesian components.

Similarly we can talk about Z vs R

"Types are a syntactic discipline for enforcing levels of abstraction."

Relational interpretations seem unnatural to me. Less so now.

System F is beside the point, and so is the lambda calculus.

Consider simple algebra expressiions (Hutton's razor)

Information hiding / Abstraction is supposedly the point of parametricity.

The relational definition of entanglement is kind of neat. I am used to defining probability distributions and then defining some expressions involving pln(p) to define entropy/information content.
There is also however a more combinatorial definition. In the microcanonical ensemble there is stuff more like this. On Boltzmann's grave I believe it is inscribed that $S=k ln Omega$, so these counting arguments show up in physics too.

To define information secrutiy in a program, that information from secret (high) variables does not leak into public (low) variables. This is actually kind of tricky to define. Give it a try. A specific execution state `(h = 1, l = 2)` doesn't have something to hold on to that describes secrecy.
One can maybe define single state semantics involving some notion of taint. But that doesn't directly correspond t the actual data in the variables. Does your definition of taint actually track information? Is there some kind of leakage side channel still exist? How can you know.

So a solution is that information is not a property of a single state. It can be seen as some kind of correlation between multiple executions. If you can execute a program twice with the same low values but different high values, and somehow the low results change, you've got a leak.

If you want

There is some rule of thumb about how to define implementation define vs undefind behavior of an imperatve program. Undefined is modelled as `state -> option state` where if you perform an undefined op, the state trasnformation is partial. Implementation defined however takes in a definition (is parametrized) on how those operations are implemented. In fact a parametric definition.

For a simple int32 calculator, we may perhaps be on a little endian or big endian machine. Everything should be fine no matter what. In what sense is it fine? In what sense is there any meaning to the bit patterns on our machines at all?
Well, it's fine because the calculations take related bit patterns to related bit patterns. If we start with bit patterns we want to consider related, and we do operations that are appropriately related, we end up with results that are appropriately related.
