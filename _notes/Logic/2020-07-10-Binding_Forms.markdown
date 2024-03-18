---
author: philzook58
comments: true
date: 2020-07-10 13:57:58+00:00
layout: post
link: https://www.philipzucker.com/?p=2837
published: True
slug: Binding Forms
title: Binding Forms

---
- [de Bruijn](#de-bruijn)
- [Locally Nameless](#locally-nameless)
- [Abstract Binding Trees](#abstract-binding-trees)
- [Named](#named)
- [Hoas](#hoas)
- [PointFree/ Combinator](#pointfree-combinator)
- [Nominal](#nominal)
- [Scope Graphs](#scope-graphs)
- [Co-debruijn](#co-debruijn)
- [Resources](#resources)

# de Bruijn

de bruijn as summarization of eval/zipper context

Weirdo maude mixed de bruijn and named. Structured identifiers `'x', 1` or both a name and de bruijn. You only need to lift when you cross a name clash.

de bruin has some tricky points

# Locally Nameless

Probably the canonical technique.

# Abstract Binding Trees

<https://semantic-domain.blogspot.com/2015/03/abstract-binding-trees.html?m=1> <https://gist.github.com/neel-krishnaswami/834b892327271e348f79> Neel krishnwaswami

ABT are first order theory?

Induction

Practical Foundationso f programming languages

# Named

barendregt convention - bound variables are uniquely named. The rapier.

The rapier <https://www.microsoft.com/en-us/research/wp-content/uploads/2002/07/inline.pdf>
[The Foil: Capture-Avoiding Substitution With No Sharp Edges](https://arxiv.org/abs/2210.04729)

Named rep. Maintain overapproximation of possible variables in scope, can be aware of possible clashes. YOu traverse introductions as you go into terms.

[https://www.cs.cornell.edu/courses/cs3110/2019sp/textbook/interp/subst_lambda.html](https://www.cs.cornell.edu/courses/cs3110/2019sp/textbook/interp/subst_lambda.html) ordinary stringy substituion done right possibly

# Hoas

HOAS. Weak HOAS, PHOAS.

# PointFree/ Combinator

kiselyov lambda to SKI semantically <http://okmij.org/ftp/tagless-final/ski.pdf>

# Nominal

Explicit fresh and swap things.

alphaprolog - see also note on prolog
alphakanren
mlts
freshml

<https://www.cl.cam.ac.uk/~amp12/agda/choudhury/choudhury-dissertation.pdf> constructive representation of nominal sets in agda

<https://www.youtube.com/watch?v=3Zreblm0Ux0&t=8374s&ab_channel=EdwardKmett> ed kmett. permutations as trees a trie of permuations.

<http://ozark.hendrix.edu/~yorgey/pub/GCBP-author-version.pdf> yorgey foner  What’s the Difference? A Functional Pearl on Subtracting Bijections

See also note on automata for nominal automata.

[Nominal logic, a first order theory of names and binding - pitts 2003](https://www.sciencedirect.com/science/article/pii/S089054010300138X)

# Scope Graphs

# Co-debruijn

Map -style. This one is new to me. Conor Mcbride's Everybody's got the be somewhere mentions this. At every lambda, you hold a map of where those variables end up going. This leads to a lot of duplication of structure, but it makes sense. Even de Bruijn indices are a peculiar indirection. [https://arxiv.org/pdf/1807.04085.pdf](https://arxiv.org/pdf/1807.04085.pdf)

Hash cons modulo alpha

# Resources

<https://github.com/rlepigre/ocaml-bindlib>

<https://github.com/sweirich/lambda-n-ways>
[Stephanie Weirich - How to Implement the Lambda Calculus, Quickly](https://www.youtube.com/watch?v=uhGqJ1A_PRE&ab_channel=Konfy)

See macros: set of scopes.

[nbe in java 19](https://github.com/ekmett/nbe-in-java-19)

<https://jesper.sikanda.be/posts/1001-syntax-representations.html> A better blog post on bindings forms in agda than i could write. Jesper Cockx

2021-03

<http://math.andrej.com/2012/11/29/how-to-implement-dependent-type-theory-iii/#:~:text=de%20Bruijn%20levels%20are%20positions,the%20top%20of%20the%20stack>.

<https://cs.stackexchange.com/questions/119861/semantics-for-de-bruijn-levels>

Yes so, Semantic of de bruijn
z really is a projection function from a tuple
s is a reduction function ignoring
They really use polymorphism to achieve what they need here.
i + l = n levels plus indices = number of binders.
I can be wokring in Fock space for homogenous operators.
Simon here shows a homogenous list based semantics.

2020-07

What do we do with binders?

[https://www.schoolofhaskell.com/user/edwardk/bound](https://www.schoolofhaskell.com/user/edwardk/bound)

Do Just dumbass names

    <code>data Lambo = Var String | Lam String Lambo | App lambo Lambo
    
    -- nope i fucked this up. lordy
    -- You need to alpha rename if x contains s' as a free var
    subst (Lam s' b) s x | s == s' = (Lam s' b)
                         | otherwise = Lam s' (subst b s x)
    subst (Var s') s x | s == s' = x
                       | otherwise = Var s'
    subst (App f x) s x = App (subst f s x) (subst f s x) 
    
    but then we want to be lazy about substituions.
    
    
    eval :: Lambo -> Lambo
    eval (App f x) = let x' = eval x in 
    eval (App (Lam s b) x) = eval (subst b s x)
    eval (App f x) | reducible f = let f' = eval f in eval f' x -- if we also let x' = eval x  it is cbv
                   | otherwise = (App f x) 
    eval x = x</code>

Direct Substitution

Environment passing

Well typed de bruijn. [http://docs.idris-lang.org/en/latest/tutorial/interp.html](http://docs.idris-lang.org/en/latest/tutorial/interp.html)

Bird and Patterson, Altenkirch and Reus. Look at Eisenberg's Stitch. and Idris tutorial.

[https://plfa.github.io/DeBruijn/](https://plfa.github.io/DeBruijn/)

[http://www.cs.ox.ac.uk/people/richard.bird/online/BirdPaterson99DeBruijn.pdf](http://www.cs.ox.ac.uk/people/richard.bird/online/BirdPaterson99DeBruijn.pdf)

Chris mentioned [https://nms.kcl.ac.uk/christian.urban/Publications/nom-tech.pdf](https://nms.kcl.ac.uk/christian.urban/Publications/nom-tech.pdf) nominal forms in isabelle. I don't know what this is

Locally nameless. Separate free and bound variables. Conor Mcbride and Charuand paper

Point-free style. Does my point-free guide hold some stuff about binding forms?

I had some notes I was doing for indexful differentiation. Tensor expressions. It was an interesting exercise

Differentiation is syntactic, not semantic. That's why is sucks so hard in thermo

Differential is a binding form itself. See a comment in Functional Differential geometry and in Plotkin's talk.

weirich [https://www.youtube.com/watch?v=j2xYSxMkXeQ](https://www.youtube.com/watch?v=j2xYSxMkXeQ)

[https://github.com/sweirich/challenge/blob/canon/debruijn/debruijn1.md](https://github.com/sweirich/challenge/blob/canon/debruijn/debruijn1.md)

In locally nameless we don't have to shift on the term we're substituting in since the free variables in the term have names.
