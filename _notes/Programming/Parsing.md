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


[recursive acent parsing](https://en.wikipedia.org/wiki/Recursive_ascent_parser)



Treesitter



```python
test = """ (hi there 
    (my guy     
((how's () it going ()))))"""

stack = [[]]
depth = 0
tok = []
for n, c in enumerate(test):
    if c == "(":
        depth += 1
        stack.append([])
    elif c == ")":
        depth -= 1
        if depth < 0:
            raise Exception(f"Unbalanced paren at char {n}")
        else:
            e = stack.pop()
            stack[-1].append(e)
    elif c in " \t\n":
        if len(tok) > 0:
            stack[-1].append("".join(tok))
            tok = []
    else:
        tok.append(c)
if depth != 0:
    raise Exception("unclosed paren")
print(stack[0][0])

# recursive descent parser
def parse(n,s):
    ns = len(s)
    sexp = []
    tok = []
    while n < ns:
        c = s[n]
        n += 1
        if c == "(":
            n,x = parse(n,s)
            sexp.append(x)
        elif c == ")":
            return n, sexp
        elif c in " \t\n":
            if len(tok) > 0:
                sexp.append("".join(tok))
                tok = []
        else:
            tok.append(c)
    return n,sexp

print(parse(0,test))
```

https://rosettacode.org/wiki/S-expressions#Python
use regex. We will want to parse numbers and strings.


## Antlr
upper case are lexer rules, lower case are parse rules

grammars can import other grammars


Here is an antlr4 grammar of sexp

```antlr4
/*
The MIT License

Copyright (c) 2008 Robert Stehwien

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.

*/

/*
Port to Antlr4 by Tom Everett
*/
grammar sexpression;

sexpr
   : item* EOF
   ;

item
   : atom
   | list_
   | LPAREN item DOT item RPAREN
   ;

list_
   : LPAREN item* RPAREN
   ;

atom
   : STRING
   | SYMBOL
   | NUMBER
   | DOT
   ;

STRING
   : '"' ('\\' . | ~ ('\\' | '"'))* '"'
   ;

WHITESPACE
   : (' ' | '\n' | '\t' | '\r')+ -> skip
   ;

NUMBER
   : ('+' | '-')? (DIGIT)+ ('.' (DIGIT)+)?
   ;

SYMBOL
   : SYMBOL_START (SYMBOL_START | DIGIT)*
   ;

LPAREN
   : '('
   ;

RPAREN
   : ')'
   ;

DOT
   : '.'
   ;

fragment SYMBOL_START
   : ('a' .. 'z')
   | ('A' .. 'Z')
   | '+'
   | '-'
   | '*'
   | '/'
   | '.'
   ;

fragment DIGIT
   : ('0' .. '9')
   ;
```
