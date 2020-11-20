---
author: philzook58
comments: true
date: 2016-08-26 02:59:05+00:00
layout: post
link: https://www.philipzucker.com/some-parsing-in-haskell/
slug: some-parsing-in-haskell
title: Some parsing in Haskell
wordpress_id: 494
---

[http://dev.stephendiehl.com/fun/002_parsers.html](http://dev.stephendiehl.com/fun/002_parsers.html)

[https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours/Parsing](https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours/Parsing)

[http://book.realworldhaskell.org/read/using-parsec.html](http://book.realworldhaskell.org/read/using-parsec.html)

> import Control.Applicative hiding (many)
> import Control.Monad (liftM, ap)
> import Control.Monad.Plus
I'm going based on [http://www.cs.nott.ac.uk/~pszgmh/pearl.pdf](http://www.cs.nott.ac.uk/~pszgmh/pearl.pdf) A paper on monadic parsing by Hutton. More than based. I'm copying code.
I'm just writing down what I think as I'm going through this paper.
So what is going on here.
A parser is a little guy that will try to pull off all it can that patches from a string. If it can't find anything
it will return an empty list. If it can match more than one option, it'll return a list of possibilities

It feels more like a little regular expression guy
Its kind of a combo of a state monad and the list monad.
The state is the current string that is left to be chewed up
the list monad is for nondeterminstic computation, it returns all possible results
One wonders if this could be constructed useful using monad transformers
Don't know much aout those but that is how the feel. For composing multiple monads.
> newtype Parser a = Parser (String -> [(a,String)])
> parse (Parser x) = x

Now, why is the type a function? What is going to happen is we're going to define a way to compose these little
functions in a way to build up the big parser from the little ones. The a type parameter is interesting.
Maybe it returns a token representing what it found. Or maybe it just returns the string that matches

> item :: Parser Char
> item = Parser (\cs -> case cs of
> "" -> []
> (c:cs) -> [(c,cs)])

So item produces a parser that will match any character.

How do we grab all items? Well we need to compose up a bunch of these item guys.
What we kind of want is something that feels like
item3 = item $ item $ item
This doesn't work because the types in and out down't match. So it needs to be a monad to replace function application $ with
the monaidc bind >>=

> instance Monad Parser where
> return a = Parser (\cs -> [(a,cs)])
> p >>= f = Parser (\cs -> concat [parse (f a) cs' |
> (a,cs') <- parse p cs])

return makes a trivial parser: A function that doesn't change the string at all and returns the object a no matter what the string said.
The bind operation composes the operations. What does it need to do?
1. It needs to return a function String -> [(a,String)] wrapper in a Parser constructor
2. It needs to strip the left over string coming out of p's function and pass it into the function f makes
3. f might need to know what came before it to decide what parser to makes?
4. For every possibility that comes out of p you need to try what comes out of (f a)

I think 4 is non obvious. We'll see if I change my mind.

So he used a list comprehension. Not what I would've thought of. It's clean though. Here's a very shitty construction process

Needs to return a function from strings
p >>= f = Parser (\cs
Need to use (parse p) to start. Then we have that list [(a,cs')]
p >>= f = Parser (\cs -> (parse p) cs )
Probably map over the list we need to do something for every element
p >>= f = Parser (\cs -> map (parse p) cs )
What are we applying? f I guess. We need to apply f the the first argument to make a parser. Now we have a list of parsers.
p >>= f = Parser (\cs -> map (f . fst) (parse p) cs )
Now get those functions out
p >>= f = Parser (\cs -> map parse (map (f . fst) (parse p) cs))
This is getting too long. Things are getting out of hand. So I define intermediate expressions.
Now apply them
p >>= f = Parser (\cs -> map fs (map snd acs)
where
acs = (parse p) cs
fs = map parse (map (f . fst) acs)

eh screw it

The list monad has a similar bind.
God Do I have to implement Functor too? Probably.

> instance Functor Parser where
> fmap = liftM

> instance Applicative Parser where
> pure = return
> (<*>) = ap

Monad is automatically a functor and applicatibe. I should look up the defintions of those functions
> p :: Parser (Char,Char)
> p = do {c <- item; item; d <- item; return (c,d)}

ghci returns
*Main> (parse p) "qwerty"
[(('q','e'),"rty")]

So to add parsers allows you to take different routes.
The zero parser does jack all

> instance MonadPlus Parser where
> mzero = Parser (\cs -> [])
> mplus f g = Parser (\cs -> (parse f) cs ++ (parse g) cs)

> instance Alternative Parser where
> (<|>) = mplus
> empty = mzero
> sat :: (Char -> Bool) -> Parser Char
> sat p = do c <- item
> if (p c) then (return c) else mzero

> findq = sat (== 'q')

*Main> parse findq "qwerr"
[('q',"werr")]
*Main> parse findq "werr"
[]

> char :: Char -> Parser Char
> char c = sat (c ==)

> string :: String -> Parser String
> string "" = return ""
> string (c:cs) = do char c
> string cs
> return (c:cs)
> many :: Parser a -> Parser [a]
> many p = many1 p `mplus` (return [])
> many1 :: Parser a -> Parser [a]
> many1 p = do a <- p
> as <- many p
> return (a:as)

*Main> parse (many (char 'c')) "yoyoyoc"
[("","yoyoyoc")]
*Main> parse (many (char 'c')) "ccyoyoyoc"
[("cc","yoyoyoc"),("c","cyoyoyoc"),("","ccyoyoyoc")]
> isSpace s = s == ' ' || s == '\t' || s == '\n' || s == '\r'
> space :: Parser String
> space = many (sat isSpace)

> token :: Parser a -> Parser a
> token p = do {a <- p; space; return a}

> symb :: String -> Parser String
> symb cs = token (string cs)

> apply :: Parser a -> String -> [(a,String)]
> apply p = parse (do {space; p})

> data Expr = Expr Addop Term | Term
> data Term = Val Int

and I'm tired So I'll stop.
