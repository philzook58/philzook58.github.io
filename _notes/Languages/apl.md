---
layout: post
title: APL
---

<https://aplwiki.com/wiki/Running_APL>
<https://aplwiki.com/wiki/Blogs>

<https://www.youtube.com/watch?v=8ynsN4nJxzU&ab_channel=code_report> code_report conor hoekstra

BQN <https://mlochbaum.github.io/BQN/> <https://github.com/dzaima/CBQN>

K
Q
J

α

```bash
# pretty print result
bqn -p "2 + 3 "
```

<https://aplwiki.com/wiki/Uiua>

<https://xpqz.github.io/learnapl/intro.html>

dyalog

quad

```
¯ × ÷ ∘ ∣ ∼
≠ ≤ ≥
≬ ⌶
⋆ ⌾ ⍟
⌽ ⍉ ⍝ ⍦ ⍧ ⍪ ⍫ ⍬ ⍭
← → , ↑ ↓
∆ ∇ , ∧ ∨ , ∩ ∪ , ⌈ ⌊ , ⊤ ⊥ , ⊂ ⊃
⍅ ⍆ , ⍏ ⍖
⌿ ⍀ , ⍋ ⍒ , ⍱ ⍲
○
⍳ ⍴ ⍵ ⍺
⍶ ⍷ ⍸ ⍹ ⍘ ⍙ ⍚ ⍛ ⍜ ⍮
¨ ⍡ ⍢ ⍣ ⍤ ⍥ ⍨ ⍩
⍊ ⍑ , ⍎ ⍕
⍐ ⍗ , ⍓ ⍌ , ⍍ ⍔ , ⍁ ⍂ , ⍃ ⍄ , ⍇ ⍈
⌸ ⍯
⎕ ⍞ ⍠ ⍰ ⌷ ⌹ ⌺ ⌻ ⌼

```

```bash
echo "⎕← 1 + 1 ÷ 2 × 2" > /tmp/test.apl
dyalogscript /tmp/test.apl


```

co-dfns - gpu compiler

Could apl be useful as a formal language?

Mcchuravy
Aaron hsu <https://www.sacrideo.us/tag/apl/>
vanessa mchale <http://vmchale.com/>
iverson

numpy
combinators - shonfield curry

<http://nsl.com/> no stinking loops. some cool logic programs and other bits. parser combinator

<https://vector.org.uk/>

<https://works.swarthmore.edu/cgi/viewcontent.cgi?article=1350&context=fac-physics> APL And The Numerical Solution Of High-Order Linear Differential Equations  1983
<https://dl.acm.org/doi/abs/10.1145/384283.801095> an apl approach t differential equations

# J

<https://www.jsoftware.com/#/README>
<https://code.jsoftware.com/wiki/Guides/Getting_Started>

<https://code.jsoftware.com/wiki/At_Play_With_J>

<https://www.jsoftware.com/books/pdf/> books. Calculus <https://www.jsoftware.com/books/pdf/calculus.pdf> . Concrete mathemtica companion.

```bash
echo "  NB. re
2 20 $ 'hello world ' NB. string enclosed in single quotes
a=. i.3 4             NB. table of integers
a                     NB. display the table   
+/a                   NB. sum over columns
+/\"1 a                NB. sum over rows
NB. try your own lines here
_3  NB. negative numbers
% 2 NB. recip monad
1 +. 1 NB. or / gcd
foo=. +
35 foo 3
  ;: 'a =. 1 2 3' NB. parsing visalization helper
CR NB. carriage return 
NB.  =: is global definition
foot=. 4 : 0
  x + y
)
1 foot 2

*/ 1 2 3 4 NB. / adverbs modify verbs. reduce / fold
myfact=. +/ 1 + i. NB. no not right
myfact 5

2 2 $ 10 NB. reshape
? 10 100 1000 NB. random numbers

exit 0" |  jconsole

```
