---
author: philzook58
comments: true
date: 2016-02-10 16:57:11+00:00
layout: post
link: https://www.philipzucker.com/quantum-harmonic-oscillator-algebra-in-sympy/
slug: quantum-harmonic-oscillator-algebra-in-sympy
title: Quantum Harmonic Oscillator Algebra in Sympy
wordpress_id: 389
---

This is kind of garbage, but it does work.

    
    from sympy import *
    a = Symbol('a', commutative=False)
    adag = Symbol('adag', commutative=False)
    ket = Symbol('|0>', commutative=False)
    bra = Symbol('<0|', commutative=False)
    
    expr = bra * a * a * a * adag  * adag * adag * ket
    print expr
    rules = [(a * adag, adag * a + 1), (a * ket, 0), (bra*adag, 0), (bra * ket, 1)]
    expr22 =  expr.subs(rules).expand()
    
    for i in range(10):
        expr22 = expr22.expand()
        expr22 = expr22.subs(rules)
    print expr22


Need to loop over it because the substitution rules aren't smart enough to distribute the commutators themselves.

Still, seems to work. Kind of a hack, but seems to work.



Here's the same thing built out of not much. Not elegantly done particularly

    
    def evalexpr(expr):
        if expr == []:
            return 1
        if expr[-1]=='a':
            return 0
        elif expr[0]=='adag':
            return 0
        else:
            for i in range(len(expr)-1):
                if expr[i]=='a' and expr[i+1]=='adag':
                    head = expr[0:i]
                    if i+2 < len(expr):
                        tail = expr[i+2:]
                    else:
                        tail = []
                    return evalexpr(head+tail) + evalexpr(head+['adag','a']+tail)
                    break
    
    print evalexpr(['a','a','a', 'adag', 'adag','adag'])







