---
layout: post
title: Parsing and Lexing
---

# Lexing

## Regular Expressions

https://regex101.com/
https://regexr.com/

# Parsing
I personally do not enjoy front end issues as much as back end. And yet a front to back compiler course starts there. Kind of off putting.

BNF
Context Free Grammars
[Parsing Expression Grammar](https://en.wikipedia.org/wiki/Parsing_expression_grammar)
LL
LALR

[How do you get good error messages](https://twitter.com/SandMouth/status/1513173009976147975?s=20&t=5y91-I1SPrIGomAWSqs69w)

[sy brand paper on how compilter diagnostics could be imporved](https://twitter.com/TartanLlama/status/1527327581464567809?s=20&t=C_oktCkKA7nprGoHnJpglQ)

## Algorithms
[List of algorithms - parsing](https://en.wikipedia.org/wiki/List_of_algorithms#Parsing)
Recursive Descent
Earley parser
Pratt Parser
LL Parser
LR Parser
packrat
allstar

## Parser Combinators
`String -> [(a,String)]` A non deterministic search that consumes a prefix of the input.
parsec

Alternative persecptive - each production is string `position -> [nextposition]`

Just making a parse tree acceptor vs something that outputs something.


[Leermakers 1993- The functional treatement of parsing](https://link.springer.com/book/10.1007/978-1-4615-3186-9)
Memoizing parser combinators
tabling

## Parser Generators


Flex
yacc/bison
antlr
Menhir [error handling the new way](http://cambium.inria.fr/~fpottier/menhir/manual.html#sec68)
Sam's coq stuff <https://github.com/slasser/AllStar> <https://github.com/slasser/CoStar>



Semantic Actions

menhir manual
http://gallium.inria.fr/~fpottier/menhir/manual.html
LR(1) parser
menhir offers a coq mode?

[Generating LR syntax error messages from examples](https://dl.acm.org/doi/10.1145/937563.937566)

## Shift Reduce Parsing
See Appell's book
<https://en.wikipedia.org/wiki/Shift-reduce_parser>

shift takes token off stream and puts onto stack
reduce takes top of atxckc

Shift reduce conflicts
