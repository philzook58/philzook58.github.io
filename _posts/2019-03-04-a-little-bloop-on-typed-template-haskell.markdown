---
author: philzook58
comments: true
date: 2019-03-04 00:05:55+00:00
layout: post
link: https://www.philipzucker.com/a-little-bloop-on-typed-template-haskell/
slug: a-little-bloop-on-typed-template-haskell
title: A Little Bloop on Typed Template Haskell
wordpress_id: 1854
categories:
- Haskell
tags:
- haskell
- metaprogramming
---




I've found looking at my statistics that short, to the point, no bull crap posts are the most read and probably most useful.







I've been tinkering around with typed template Haskell, which a cursory internet search doesn't make obvious even exists. The first thing to come up is a GHC implementation wiki that seems like it might be stalled in some development branch. No. Typed template Haskell is already in GHC since GHC 7.8. And the first thing that comes up on a template haskell google search is the style of Template Haskell where you get deep into the guts of the syntax tree, which is much less fun.







Here's a basic addition interpreter example.






    
    <code>{-# LANGUAGE TemplateHaskell -#}
    import Language.Haskell.TH
    import Language.Haskell.TH.Syntax
    
    data Expr = Val Int | Add Expr Expr
    
    eval' :: Expr -> Int
    eval' (Val n) = n
    eval' (Add e1 e2) = (eval' e1) + (eval' e2)
    
    eval :: Expr -> TExpQ Int
    eval (Val n) = [|| n ||]
    eval (Add e1 e2) = [|| $$(eval e1) + $$(eval e2) ||]
    
    </code>







The typed splice `$$` takes `a` out of `TExpQ a`. The typed quote `[|| ||]` puts it in. I find that you tend to be able to follow the types to figure out what goes where. If you're returning a TExpQ, you probably need to start a quote. If you need to recurse, you often need to splice. Etc.







You tend to have to put the actual use of the splice in a different file. GHC will complain otherwise.






    
    <code>ex1 :: Int
    ex1 = $$(eval (Add (Val 1) (Val 1)))</code>







At the top of your file put this to have the template haskell splices dumped into a file 






    
    <code>{-# OPTIONS_GHC -ddump-splices -ddump-to-file #-}</code>







Or have your package.yaml look something like this






    
    <code>executables:
      staged-exe:
        main:                Main.hs
        source-dirs:         app
        ghc-options:
        - -threaded
        - -rtsopts
        - -with-rtsopts=-N
        - -ddump-splices
        - -ddump-to-file
        dependencies:
        - staged</code>







If you're using stack, you need to dive into .stack/dist/x86/Cabal/build and then /src or into the executable folder something-exe-tmp/app to find .dump-splices files.






    
    <code>app/Main.hs:11:10-35: Splicing expression
        eval (Add (Val 1) (Val 1)) ======> (1 + 1)</code>







Nice. I don't know whether GHC might have optimized this thing down anyhow or not, but we have helped the process along. 







Some more examples: unrolling the recursion on a power function (a classic)






    
    <code>-- ordinary version
    power 0 x = 1
    power n x = x * (power (n-1) x)
    
    -- templated up
    power' :: Int -> TExpQ (Int -> Int)
    power' 0 = [|| const 1 ||]
    power' n = [|| \x -> x * $$(power' (n-1)) x ||] </code>







You can unroll a fibonacci calculation






    
    <code>-- unrolled fib woth sharing
    fib 0 = 1
    fib 1 = 1
    fib n = (fib (n-1)) + (fib (n-2))
    
    -- we always need [||  ||] wheneve there is a Code
    fib' :: Int -> TExpQ Int
    fib' 0 = [|| 1 ||]
    fib' 1 = [|| 1 ||] 
    fib' n = [|| $$(fib' (n-1)) + $$(fib' (n-2)) ||]</code>







This is blowing up in calculation though (no memoization, you silly head).  We can implement sharing in the code using let expression (adapted from [https://wiki.haskell.org/The_Fibonacci_sequence](https://wiki.haskell.org/The_Fibonacci_sequence)). Something to think about.






    
    <code>fib4 :: Int -> TExpQ Int
    fib4 n = go n [|| ( 0, 1 ) ||]
                    where
                      go :: Int -> TExpQ (Int, Int) -> TExpQ Int
                      go n z | n==0      = [|| let (a,b) = $$(z) in a ||]
                             | otherwise = go (n-1) [|| let (a,b) = $$(z) in (b, a + b) ||]</code>







Tinkering around, you'll occasionally find GHC can't splice and quote certain things. This is related to cross stage persistence and lifting, which are confusing to me. You should look in the links below for more info.  I hope I'll eventually get a feel for it.







If you want to see more of my fiddling in context to figure out how to get stuff to compile here's my github that I'm playing around in  [https://github.com/philzook58/staged-fun](https://github.com/philzook58/staged-fun)







Useful Link Dump:







Simon Peyton Jones has a very useful talk slides. Extremely useful  [https://www.cl.cam.ac.uk/events/metaprog2016/Template-Haskell-Aug16.pptx](https://www.cl.cam.ac.uk/events/metaprog2016/Template-Haskell-Aug16.pptx)







Matthew Pickering's post keyed me into that Typed Template Haskell is even there.







[ http://mpickering.github.io/posts/2019-02-14-stage-3.html](http://mpickering.github.io/posts/2019-02-14-stage-3.html)







[MuniHac 2018: Keynote: Beautiful Template Haskell](https://www.youtube.com/watch?v=AzJVFkm42zM)







[https://markkarpov.com/tutorial/th.html](https://markkarpov.com/tutorial/th.html) Mark Karpov has a useful Template Haskell tutorial







Oleg Kiselyov: I'm still trying to unpack the many things that are going on here. Oleg's site and papers are a very rich resource.







I don't think that staged metaprogramming requires finally tagless style, as I first thought upon reading some of his articles. It is just very useful.







[http://okmij.org/ftp/meta-programming/](http://okmij.org/ftp/meta-programming/)







[http://okmij.org/ftp/meta-programming/tutorial/](http://okmij.org/ftp/meta-programming/tutorial/)







Typed Template Haskell is still unsound (at least with the full power of the Q templating monad) [http://okmij.org/ftp/meta-programming/#TExp-problem](http://okmij.org/ftp/meta-programming/#TExp-problem)







You can write things in a finally tagless style such that you can write it once and have it interpreted as staged or in other ways. There is a way to also have a subclass of effects (Applicatives basically?) less powerful than Q that is sound. 









