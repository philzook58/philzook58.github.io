---
layout: post
title: Parsing and Lexing
---

# Lexing

## Regular Expressions
See regex notes


# Parsing
I personally do not enjoy front end issues as much as back end. And yet a front to back compiler course starts there. Kind of off putting.

BNF
Context Free Grammars
[Parsing Expression Grammar](https://en.wikipedia.org/wiki/Parsing_expression_grammar)
LL
LALR

[How do you get good error messages](https://twitter.com/SandMouth/status/1513173009976147975?s=20&t=5y91-I1SPrIGomAWSqs69w)

[sy brand paper on how compilter diagnostics could be imporved](https://twitter.com/TartanLlama/status/1527327581464567809?s=20&t=C_oktCkKA7nprGoHnJpglQ)

[Top-down LR parsing - panchekha](https://pavpanchekha.com/blog/top-down-lr.html)
[Why We Need to Know LR and Recursive Descent Parsing Techniques - tratt](https://tratt.net/laurie/blog/2023/why_we_need_to_know_lr_and_recursive_descent_parsing_techniques.html) https://twitter.com/laurencetratt/status/1615281727538188289?s=20
[Just write the parser - rompf](https://tiarkrompf.github.io/notes/?/just-write-the-parser/aside1)
[Parser generators vs. handwritten parsers: surveying major language implementations in 2021](https://notes.eatonphil.com/parser-generators-vs-handwritten-parsers-survey-2021.html)

https://langcc.io/ [paraticval lr parser generation](https://arxiv.org/abs/2209.08383)

## Grammars
https://en.wikipedia.org/wiki/Formal_grammar
String rewrite rules. Distinguishes between terminal and non terminal

Context free means the rules only have raw non terminals on left hand side

https://en.wikipedia.org/wiki/Linear_grammar

Context Sensitive Grammars
Gneral 

Lambek Grammars



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

[Hammer](https://github.com/abiggerhammer/hammer) binary format parser combinators in C

## Parsing as Deduction


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

Parser generators as "compiler-compilers". It's easier for me to see them as intepreter generators.

Parser generator as 
```python
import logging
from lark import Lark, logger, Transformer

logger.setLevel(logging.WARN)
grammar = '''
expr : 
      | "0" "+" expr -> zero_left
      | NUMBER -> number
      | expr "+" expr -> add
      | "("  expr ")"

%import common.WS
%ignore WS
%import common.NUMBER
'''
grammar = '''
expr : 
      | "0" expr "+" -> zero_left
      | NUMBER -> number
      | expr expr "+" -> add

%import common.WS
%ignore WS
%import common.NUMBER
'''

class Simple(Transformer):
   def number(self,n):
      (n,) = n
      return n
   def add(self,args):
      (x,y) = args
      return f"{x}+{y}"
   def zero_left(self,x):
      (x,) = x
      return x

parser = Lark(grammar, start="expr", parser="lalr", transformer=Simple())
#print(parser.parse("1 + 0 + 2 + 0 + 3 + 4 + 2 + 0 + 1"))
print(parser.parse("0 1 + 2 + 0 + 3 + 4 + 0 + 1 +"))
#parser = Lark(grammar, start="expr")
#print(Simple().transform(parser.parse("1 + 0 + 2 + 0 + 3 + 4 + 0 + 1 + 0")))



```
## Shift Reduce Parsing
See Appell's book
<https://en.wikipedia.org/wiki/Shift-reduce_parser>

shift takes token off stream and puts onto stack
reduce takes top of atxckc

Shift reduce conflicts

# Hand Rolled Parsers
So the story goes, really good parsers with good error messaging are hand rolled.
What is the structure. What are the good techniques

# Recursive Descent

# Recusrive Ascent
https://en.wikipedia.org/wiki/Recursive_ascent_parser

[recursive acent parsing](https://en.wikipedia.org/wiki/Recursive_ascent_parser)



[Treesitter](https://www.youtube.com/watch?v=Jes3bD6P0To&t=963s&ab_channel=StrangeLoopConference)
graph tee sitter
souffle tree-sitter

## ASM
https://austinhenley.com/blog/parsingriscv.html
Kind of a fun macro assembler design. Instead of using a built in macro language or a we can add new parsing forms to the language.

```python
from lark import Lark

grammar = '''


prog : NL* (com NL+)*
com : label | directive | insn
label : NAME ":"
directive : "." NAME
insn : NAME (operand ("," operand)*)?
operand : reg | NAME
reg : "r" INT 



%import common.CNAME -> NAME
%import common.INT -> INT
%import common.ESCAPED_STRING   -> STRING
%import common.NUMBER
%import common.NEWLINE -> NL
%import common.WS_INLINE
%import common.SH_COMMENT
%ignore WS_INLINE
%ignore SH_COMMENT
'''

parser = Lark(grammar, start="prog")
print(parser.parse(''' foo:
mov r1,r2
''').pretty())
```
### Hack

```python
from lark import Lark

grammar = '''
prog : NL* (com NL+)*
com : label | directive | insn
label : NAME ":"
ainsn : "@"
cinsn : ";"
jmp : "J" | "JNE" | JEQ"
insn : NAME (operand ("," operand)*)?
operand : reg | NAME
reg : "r" INT 



%import common.CNAME -> NAME
%import common.INT -> INT
%import common.ESCAPED_STRING   -> STRING
%import common.NUMBER
%import common.NEWLINE -> NL
%import common.WS_INLINE
%import common.SH_COMMENT
%ignore WS_INLINE
%ignore SH_COMMENT
'''

parser = Lark(grammar, start="prog")
print(parser.parse(''' foo:
mov r1,r2
''').pretty())
```

## Datalog
a datalog grammar:
egglite
chr


```python
from lark import Lark

grammar = """
prog : rule*
rule : fact "."
   | head ":-" body  "."

body: fact ("," fact)*
head : fact
fact :  NAME "("  [ term ("," term)* ]  ")"

term : NUMBER -> number
     | STRING -> string
     | NAME -> var

%import common.CNAME -> NAME
%import common.ESCAPED_STRING   -> STRING
%import common.NUMBER
%import common.WS
%ignore WS
"""

parser = Lark(grammar, start="prog")
print(parser.parse("foo(3,4).  edge(1,2). edge(\"a\"). path(x,z) :- edge(x,y), path(y,z).").pretty())
```

## CHR
```python
from lark import Lark

grammar = """
prog : rule*
rule : fact "."
   | label? prop "." 
   | label? simp "."

prop : body "==>" head
simp :  body ("/" body )?  "<=>" head
body: fact ("," fact)*

label : NAME "@"
head : ( guards "|" )? body?
guards : guard ("," guards)*
guard : NAME "=" NAME 

//op : "=|<=|"
fact :  NAME ("("  [ term ("," term)* ]  ")")?

term : NUMBER -> number
     | STRING -> string
     | NAME -> var

%import common.CNAME -> NAME
%import common.ESCAPED_STRING   -> STRING
%import common.NUMBER
%import common.WS
%ignore WS
"""

parser = Lark(grammar, start="prog")
print(parser.parse("""
foo(3,4).  edge(1,2). edge(\"a\"). 
edge(x,y) / edge(x,y) <=> true.
edge(x,y), path(y,z) ==> path(x,z).
edge(x,y) <=> a = y, c = d | path(x,y).
""").pretty())
```


## Sexp

S-expressions are a good example. They are kind of the core simple parse, easy enough to do basic ones by hand.

[Sweet expressions](https://readable.sourceforge.io/)

 https://lark-parser.readthedocs.io/en/latest/json_tutorial.html
 https://github.com/lark-parser/lark/blob/master/lark/grammars/common.lark the common symbols available in lark
```python
from lark import Lark, Transformer
grammar = 
   """
    exp:  "(" "+" exp*  ")" -> add
         | SIGNED_NUMBER    -> lit

    %import common.ESCAPED_STRING
    %import common.SIGNED_NUMBER
    %import common.WS
    %ignore WS
   """

exp_parser = Lark(grammar, start='exp')
e = exp_parser.parse("(+ (+ 1 2) 3)")
print(e.pretty())


class Calc(Transformer):
   def add(self,args):
      print(args)
      return sum(args)
   def lit(self,n):
      (n,) = n
      return float(n)

print(Calc().transform(e))
print(e)
# immediate transformation with no tree
exp_parser = Lark(grammar, start='exp', parser='lalr', transformer=Calc())
print(exp_parser.parse("(+ 2 3)"))
```




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


## Flex Bison
https://begriffs.com/posts/2021-11-28-practical-parsing.html
Crazy stuff.

lex creates yylex which lexes from a file handler
Options can be made to not use globals

the parser calls yylex, which returns if it wants t give bakc a token
The tokens correspond to `define` integers

global variables in the prelude.


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

# Misc
[   flap: A Deterministic Parser with Fused Lexing](https://github.com/yallop/ocaml-flap) use metaocaml staged programming techniques to fuse lexer and parser

[grammar zoo](http://slebok.github.io/zoo/index.html)


[awesome binary parsing](https://github.com/dloss/binary-parsing)

[permutation parsing](https://recursion.ninja/blog/perm-parser) https://www.cambridge.org/core/journals/journal-of-functional-programming/article/functional-pearl-parsing-permutation-phrases/DB7B6AFE506CF84BBDBBF54306F28D38