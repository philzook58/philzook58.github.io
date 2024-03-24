---
title: Manifolds in Equational Logic
---



I don't know that there can be a canonical formulation of any logic.

But equational logic is trees of symbols, some of which are variable symbols. The 0-arity constant symbol `x` is very different from the variable `X` `?x`.
This distinction is useful. A statement `f(x) = 1` is a statement about the interaction of a particular `f` on a particular `x`. This may be an equation we'd like to solve for possibille values of `x`. `f(X) = 1` however is a universal statement. If we were working in forist order logic, which throws exists and forall quantifiers into the mix, this statement is the analog of `forall x, f_fol(x) =_fol 1_fol`. It is now stating nothing about a particular `x` but instead stating a global property of the function `f`, that `f` is the constant function.

Coordinate systems are a tricky concept. The notation is quite slippery and you learn your way around it.

Coordinates are an address book for points. They parametrize points such that.
In other words a coordinate system _is_ a function of the type `R^n -> M`

The concept of a point is discussed in the textbooks, but it is an abstract entity. Since it doesn't really have calculational properties the way numbers, matrices, and numerical functions do. Even abstract things like quantum operators, kind of we have some matrix implementation in the back of my head. Points kind of have no operations on them in general. They can be in relation to other entities like curve, surfaces, etc, but there isn't a notion of point multiplication or addition or scaling except in very special spaces.

There is a related notion for a coordinate system of `x : M -> R`.

A coorindate transformation such as translation is written like `x' = x + a`. What are these `x`? This is certainly nonsensical as `X' = X + a`. It is also not exactly that we mean are talking about a particular `x` or `x'`. This might be so if we had a particular point of interest, `x'(p) = x(p) + a` but we are talking about transforming the coordinate _system_ everywhere.
Actually what we are saying is that for any point `x'(P) = x(P) + a`.

Anyway, I think the appropriate notation here is

```
coord'(X,Y,Z) = coord(X - a, Y, Z)
```

Again, we get used to that if you have an expression `f(x')`,

```bash
cart : R^3 -> M
cart(_,_,_)

x y z : M -> R

x(cart(X,Y,Z)) = X
y(cart(X,Y,Z)) = Y

cyl(R,T,Z) = cart(Rcos(T), Rsin(T), Z)
cart(X,Y,Z) = cyl(sqrt(X^2 + Y^2), atan2(X,Y), Z)

point : M

dist : M -> M -> R
dist(P1,P2) 

% hyperreals?


a curve.
p : R -> M
p(T) = cart(T,T,0)


%vector derivative
% a rate of change of a function
dp : (M -> R) -> R -> R  % (?)
dp(f)(T) = f'(p(T)) * 2

% vector field
v : (M -> R) -> M -> R




a surface
q : M2 -> M

chart : R^2 -> M2
x(q(chart(X,Y))) =

% exterior deriavtive
d : (M -> R) -> M -> ?

% a different cartersian coordinate system
x(cart'(X,Y,Z)) = x(cart(X,Y,Z)) + a
```

it would be nice for the charts to be partial.
