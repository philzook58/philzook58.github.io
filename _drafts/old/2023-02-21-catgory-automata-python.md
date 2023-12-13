

We accept graphs. But graphs aren't a primitive feature of python
We can represent graphs in many ways


# F-Algebra

F-algebras are a way of a bundling an interpretation of a signature into a single object

For a given sgnature (a collecton of function signatures), an interpretation is a mapping from these symbols to actual functions. The symbol `+` can be interpreted as addtion over integers, over reals, or as boolean `or`. These are interpetations that obey the equational laws expected of plus.

If we have multiple symbols, we need to map to multiple things.
Programmaticaly, this is something like this:

```
{
    "+" : {(1,2) : 3},
    "-" : {}
}


{
    "+" : {(True,False) : True, (False,False): False},
    "-" : {}
}
```

We are somewhat used to this notion as overloading in python. There are many meanings of the symbols `a + b` depending on how we overload the `__add__` method. However, using just dictionaries and data really makes it feel like I'm not playing any funny tricks.

We can flatten this dictionary. For some purposes this is elegant, for others it is inelegant. 

{
    ("+",1,2) : 3,
    ("-",1,2) : -1
}





