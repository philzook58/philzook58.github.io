

An interesting idea was suggested by Zach Tatlock about emulating a very very tiny subset of Herbie in datalog

Herbie is a system to automatically improve the accuracy of floating point calculations. 

I think the core ideas of herbie are actually fairly simple? 

Different mathematically equivalent ways of calculating a quantity give slightly (or vastly) different answers when computed using floating point.
For example, mathematically the two following expressions are the same:
`(1e30 - 1e30) + 1 =  (1e30 + 1) - 1e30`
However in the latter, adding 1 to such a huge number does not change the floating point representation. It gets swamped in the finite precision of the floating point, so if you put these expressions into python you get pretty different answers `1.0 = 0.0`. Not so good.

How do we pick from these different mathematically different options? Well we can do sophisticated mathematical analysis. If the calculation only involves arithmetic operations, we can compute it exactly in rational arithmetic. If the calculation involves irrational numbers like `sin(7)`, we can compute the answer in a higher precision representation and consider this a good enough ground truth value.

However, we don't want to calculate just a single number, we want a good representation for _functions_ that are accurate for many values of a variable `x`. Again, you can use sophisticated pen and paper mathematical analysis, interval arithmetic, or you can just sample points and see how they do.

So given candidate expressions we have a reasonable means to estimate their relative accuracy: Calculate "true" answer in higher precision or rationals and sample domain points.

Ok, then how to we produce candidates? Well we can use rewrite rules. These rewrite rules might encode clever gleaned tricks from the numerical computing literature, significant domain knowledge. A big part of the special sauce is figuring out what rewrite rules to have.

We want to maintain a collection of equivalent expressions, so destructive rewriting is not ideal. E-graphs are a efficient compact data structure for storing many expressions and equivalences between them.

The egg boys and I have been discussing how to hookup datalog and egraphs. This seems like an interesting example in which to apply the ideas. Zach's suggestion was to restrict to arithmetic expressions, for which we can use the GNU multiprecision library to calculate exact expressions.



Even for pure addition expressions, some associativities and commutativities are better than others.


We can exactly compute the true answer of expressions only involving `+ - * /` using exact rational arithemtic supplied by the gnu multiprecision library. 

Part of datalog's thing is it needs to know when two things are equal. If I put `7/4` into the relation `foo` multiple times, that should reduce to only one entry. We could perhaps use the pointers of the returned gmp values if we could overload hashing and equality. As an inefficient but simple cheat, we can hash cons these numbers by serializing to and from souffle's built in symbol datatype, which is basically a string. Strings are the ultimate universal type and serialization/deserialization is packing and unpacking to this type.



