---
layout: post
title: APL
---

<https://www.arraycast.com/>

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

<https://www.youtube.com/@davidzwitser156> bqn vids. ray bqn games

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

<https://github.com/briangu/klongpy> <https://aplwiki.com/wiki/Klong>

# J

<https://github.com/jsoftware/jsource> source

<https://www.jsoftware.com/books/pdf/aioj.pdf> iinterpeter of J. Appendix incabulum: one page interpreter in C?
<https://news.ycombinator.com/item?id=38866622> <https://github.com/kelas/ooj> origins of j

```bash
echo '
typedef char C;typedef long I;
typedef struct a{I t,r,d[3],p[2];}*A;
#define P printf
#define R return
#define V1(f) A f(w)A w;   // one arg frunction
#define V2(f) A f(a,w)A a,w;  // two arg function
#define DO(n,x) {I i=0,_n=(n);for(;i<_n;++i){x;}}   // macro to do stmt x with bound var i
I *ma(n){R(I*)malloc(n*4);}mv(d,s,n)I *d,*s;{DO(n,d[i]=s[i]);}
tr(r,d)I *d;{I z=1;DO(r,z=z*d[i]);R z;}
A ga(t,r,d)I *d;{A z=(A)ma(5+tr(r,d));z->t=t,z->r=r,mv(z->d,d,r);R z;}
V1(iota){I n=*w->p;A z=ga(0,1,&n);DO(n,z->p[i]=i);R z;}
V2(plus){I r=w->r,*d=w->d,n=tr(r,d);A z=ga(0,r,d);
 DO(n,z->p[i]=a->p[i]+w->p[i]);R z;}
V2(from){I r=w->r-1,*d=w->d+1,n=tr(r,d);
 A z=ga(w->t,r,d);mv(z->p,w->p+(n**a->p),n);R z;}
V1(box){A z=ga(1,0,0);*z->p=(I)w;R z;}
V2(cat){I an=tr(a->r,a->d),wn=tr(w->r,w->d),n=an+wn;
 A z=ga(w->t,1,&n);mv(z->p,a->p,an);mv(z->p+an,w->p,wn);R z;}
V2(find){}
V2(rsh){I r=a->r?*a->d:1,n=tr(r,a->p),wn=tr(w->r,w->d);
 A z=ga(w->t,r,a->p);mv(z->p,w->p,wn=n>wn?wn:n);
 if(n-=wn)mv(z->p+wn,z->p,n);R z;}
V1(sha){A z=ga(0,1,&w->r);mv(z->p,w->d,w->r);R z;}
V1(id){R w;}V1(size){A z=ga(0,0,0);*z->p=w->r?*w->d:1;R z;}
pi(i){P("%d ",i);}nl(){P("\n");}
pr(w)A w;{I r=w->r,*d=w->d,n=tr(r,d);DO(r,pi(d[i]));nl();
 if(w->t)DO(n,P("< ");pr(w->p[i]))else DO(n,pi(w->p[i]));nl();}

C vt[]="+{~<#,";
A(*vd[])()={0,plus,from,find,0,rsh,cat},
 (*vm[])()={0,id,size,iota,box,sha,0};
I st[26]; qp(a){R a>='a'&&a<='z';}qv(a){R a<'a';}
A ex(e)I *e;{I a=*e;
 if(qp(a)){if(e[1]=='=')R st[a-'a']=ex(e+2);a= st[ a-'a'];}
 R qv(a)?(*vm[a])(ex(e+1)):e[1]?(*vd[e[1]])(a,ex(e+2)):(A)a;}
noun(c){A z;if(c<'0'||c>'9')R 0;z=ga(0,0,0);*z->p=c-'0';R z;}
verb(c){I i=0;for(;vt[i];)if(vt[i++]==c)R i;R 0;}
I *wd(s)C *s;{I a,n=strlen(s),*e=ma(n+1);C c;
 DO(n,e[i]=(a=noun(c=s[i]))?a:(a=verb(c))?a:c);e[n]=0;R e;}

main(){C s[99];while(gets(s))pr(ex(wd(s)));}
' > /tmp/j.c
# nah it is not compiling
gcc --std gnu89 -o /tmp/j /tmp/j.c

```
<https://news.ycombinator.com/item?id=19421524> more expanded explanation. V1 and V2 are one arg two arg functions.

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
