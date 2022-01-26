
# Monad

```haskell
return :: a -> m a
(>>=) :: m a -> (a -> m b) -> m b
```

"monoid in the category of endofunctors"

type constructors are endofunctors. A functor is 
1. a mapping ofobjects
2. a mapping of morphisms

The standard model of category theory in haskell is
1. types are objects
2. morphisms are functions

Composition is `(.)`. `id` are identity morphisms. 

Note how weird this is. We've in some sense put types and values (haskell functions are values that inhabit function types) on the same level.


Maybe maps any type `a` to the the  `Maybe a`


## Free Monads

## F-Algebras and Recursion Schemes

A different category

`f a -> a`
- objects are _haskell functions of this type_ and the type `a`. Again a bizarre (depending on your background) mixing of values and types
- morphisms are squares. Very very weird.


a -> f a

Initiality


## Unboxed types
kinds are calling conventions
levity polymorphism