
Stillwell book Reverse Mathematics

Z2

Recursive Arithmetic RCA0
WKL weak konig's lemma
ACA0

Bounded Formula. Bounded comprehension allows us to only convert bounded qunatifiers into sets. This is a an interesting way of modelling some computations. Finite python comprehensions

ZF let's use talk about sets of sets.
Second Order Arithemtc is only talking about sets of integers.

Higher Order RCA

Pairing functions are a pain.
<https://en.wikipedia.org/wiki/Pairing_function>

```python

def pair(x,y):
    return (x+y)*(x+y+1)//2 + y
# hmm not working
def unpair(z):
    w = int( ((8*z+1)**0.5 - 1) // 2)
    t = (w**2 + w)//2
    y = z - t
    x = w - y
    return (x,y)
print(unpair(pair(100,90)))
print([ (x,y) for x in range(10) for y in range(10) if unpair(pair(x,y)) != (x,y)])

# brute search.
def nat():
    i = 0
    while True:
        yield i
        i += 1

def diagonal():
    n = 0
    for i in nat():
        for j in range(i):
            yield n, j, i - j - 1
            n += 1

def pair(x,y):
    for n,i,j in diagonal():
        if (i,j) == (x,y):
            return n
def unpair(z):
    for n,i,j in diagonal():
        if n == z:
            return i,j

print([ (x,y) for x in range(10) for y in range(10) if unpair(pair(x,y)) != (x,y)])
#print(pair(0,0))

```
