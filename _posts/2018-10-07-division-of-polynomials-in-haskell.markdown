---
author: philzook58
comments: true
date: 2018-10-07 22:59:16+00:00
layout: post
link: https://www.philipzucker.com/division-of-polynomials-in-haskell/
slug: division-of-polynomials-in-haskell
title: Division of Polynomials in Haskell
wordpress_id: 1339
tags:
- haskell
- math
- polynomials
---

I've been been on a kick learning about some cool math topics. In particular, I busted out my copy of Concrete Mathematics (awesome book) and was reading up on the number theory section. Bezout's identity is that if you have ma+nb=d for some m,n and d divides a and b, then d is the greatest divisor of a and b. Bezout's identity is a certificate theorem like the dual solution to a linear program. It doesn't matter how you found m and n or d, Euclid's algorithm or brute search, but once you've found that certificate, you know you have the biggest divisor. Pretty cool. Suppose you have some other common divisor d'. That means xd'=a and yd'=b. Subsitute this into the certificate. m(xd')+n(yd')=(mx+ny)d' =d. This means d' is a divisor of d. But the divisor relation implies the inequality relation (a divisor is always less than or equal to the thing it divides). Therefore d'<=d.

But another thing I've been checking out is algebraic geometry and Groebner bases. Groebner bases are a method for solving multivariate polynomial equations. The method is a relative of euclidean division and also in a sense Gaussian elimination. Groebner basis are a special recombination of a set of polynomial equations such that polynomial division works uniquely on them (in many variables polynomial division doesn't work like you'd expect from the one variable case anymore). Somewhat surprisingly other good properties come along for the ride. More on this in posts to come

Some interesting stuff in the Haskell arena:

https://oleksandrmanzyuk.wordpress.com/2012/10/25/grobner-bases-in-haskell-part-i/

[https://konn.github.io/computational-algebra/](https://konn.github.io/computational-algebra/)

I love Doug McIlroy's powser. It is my favorite functional pearl. [https://www.cs.dartmouth.edu/~doug/powser.html](https://www.cs.dartmouth.edu/~doug/powser.html)

One interesting aspect not much explored is that you can compose multiple layers of [] like [[[Double]]] to get multivariate power series. You can then also tuple up m of these series to make power series from R^n -> R^m. An interesting example of a category and a nonlinear relative of the matrix category going from V^n -> V^m. I'm having a hell of a time getting composition to work automatically though. I'm a little stumped.

I made a version of division that uses the Integral typeclass rather than the fractional typeclass with an eye towards these applications. It was kind of annoying but I think it is right now.

I thought that in order to make things more Groebner basis like, I should make polynomials that start with the highest power first. It also makes sense for a division algorithm, but now I'm not so sure. I should also have probably used Vector and not List.





https://www.youtube.com/watch?v=1EryuvBLY80&t=752s





    
    bezout x 0 = (1, 0, x)
    bezout x y = (n, m - n*z , d) where 
                                    r = x `mod` y
                                    z = x `div` y
                                    (m, n, d) = bezout y r 
                                    -- my + nr = d
        -- my + n(x - zy) = d
        -- (m-nz)y + nx = d
    
    -- newtype Poly a = P [a]
    instance Num a => Num [a] where
        (+) xs [] = xs
        (+) [] ys = ys
        (+) xss@(x : xs) yss@(y : ys) | nx > ny = x : (xs + yss)
                                      | nx < ny = y : (xss + ys) 
                                      | otherwise = x + y : (xs + ys) where 
                    nx = length xs
                    ny = length ys
        (*) _ [] = []
        (*) [] _ = []
        (*) (x:xs) ys = ((* x) <$> ys ++ (replicate nx 0)) + (xs * ys) where nx = length xs
            -- (pure x * ys) * xpow nx + (xs * ys) where nx = length xs
            --
        negate = fmap negate
        abs = error "no don't do this"
        signum = error "or this"
        fromInteger 0 = []
        fromInteger x = (pure . fromInteger) x 
    
    
    xpow n = 1 : replicate n 0 
    {-
    class DivMod a where
        divmod :: a -> a -> (a, a)
    
    instance Integral a => DivMod a where
        divmod = quotRem
    -}
    
    -- 
    
    instance Integral a => Integral [a] where
        quotRem [] _ = ([], [])
        quotRem xss@(x : xs) yss@(y : ys) | nx < ny = ([], xss)
                                          | otherwise = (d' + d'', r' + r'') where
    
                                           -- | nx > ny = (d' + d'',r' + r'')    
                                         
                                        --  | otherwise = ( pure d, r : xs - (pure d) * ys) where 
                                            -- (pure d , xss - (pure d) * yss)                                       
                                          -- ( pure d, r : xs - (pure d) * ys) 
                                          -- | x == 0 = quotRem xs yss
                    nx = length xs
                    ny = length ys
                    (d , r) = x `quotRem` y 
                    d' = d : (replicate (nx - ny) 0)
                    r' = r : (replicate (nx - ny) 0)
                    -- (d'' ,r'') =  quotRem (xss - d' * yss) yss
                    (d'' , r'') = quotRem (xs - (pure d) * ys) yss 
        toInteger = error "don't do this" 
    
    instance (Num a, Ord a) => Real [a] where
      toRational = error "screw you haskell" 
    
    instance (Enum a) => Enum [a] where
      toEnum = error " crew you" -- pure . toEnum
      fromEnum = error "screw yo "  -- fromEnum . head
    {-
    -- actually this is a different Ord instance from the main library
    
    instance Ord a => Ord [a] where
      compare xs yy = case compare nx ny of
                           EQ -> compare (head xs) (head ys)
                           z -> z where
                                nx = length xs
                                ny = length ys
                                -}
    
    
    -- if we use powser with Vector, 
        -- we can just grab the tail for the remainer.
        --it makes sense to grab the end
    -- we can just reuse the powser infracsture
    -- with a tail. 
    -- tail view in agda for that purpose also.
    
    example :: [[Double]]
    example = [1, 1]
    
    var :: Num a => [a]
    var = [1,0]
    x :: Num a => [a]
    x = var
    
    y :: Num a => [[a]]
    y = pure x
    
    z :: Num a => [[[a]]]
    z = pure y
    
    x' (x, _, _) = x
    y' (_, y, _) = y
    
    f :: [[Double]]
    f = 1 + 2 * x + 3 * x * y + 3 * y
    
    --(a , (a ,( a ,())))
    -- '[a , b, c, d]
    
    f1 :: (Num a) => (a, a, a) -> (a, a)
    f1 (x, y, z) = (x, y + z)
    
    f2 :: (Num a) => (a, a) -> a
    f2 (x, y) = x*x
    
    g = f2 . f1
    
    example2 = g (x, y, z)
    -- only a single variable
    -- we need something else 
    use :: Num a => [a] -> a -> a
    use [] z = 0 
    use (x : xs) z = x * (z ^ (length xs)) + (use xs z)



