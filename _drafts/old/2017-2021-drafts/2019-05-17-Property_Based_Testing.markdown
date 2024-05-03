---
author: philzook58
comments: true
date: 2019-05-17 22:03:47+00:00
layout: post
link: https://www.philipzucker.com/?p=2021
published: false
slug: Property Based Testing
title: Property Based Testing
wordpress_id: 2021
---




Hedgehog, QuickTest, Hypothesis.







install pytest







pytest filename.py







Quickcheck ~ contracts. Sort of a loose ish runtimy thing. Very expressive though. And easy to use relatively. Mike Stay  Contracts = catgoeries. So QuickCheck Generators could be considered a category? Functors from generators of a to generators of [a]. 







Fuzzing is very similar to property testing. They also want example reduction







use pdb to step thorugh excution of python program and turn it into a SMT execution?






    
    <code>from hypothesis import given
    from hypothesis.strategies import text
    import numpy as np
    #import hypothesis
    import hypothesis.strategies as st
    
    @given(st.integers(), st.integers())
    def test_ints_are_commutative(x, y):
        assert x + y == y + x
    
    @given(x=st.integers(), y=st.integers())
    def test_ints_cancel(x, y):
        assert (x + y) - y == x
    
    #this fails. SWEEET
    @given(x=st.floats(0,10), y=st.floats(0,10))
    def test_floats_cancel(x, y):
        assert abs((x + y) - y - x) <= 1e-14 # 15 fails
    '''
    @given(x=st.integers(), y=st.integers())
    def test_ints_false(x, y):
        assert (x + y) == x - y
    '''
    
    
    #pytest</code>



