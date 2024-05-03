---
author: philzook58
comments: true
date: 2020-08-11 21:40:42+00:00
layout: post
link: https://www.philipzucker.com/?p=2926
published: false
slug: Those God Awful 8th Grade Geometry proofs done in Coq
title: Those God Awful 8th Grade Geometry proofs done in Coq
wordpress_id: 2926
---




Syntax and Semantics. The diagrams are supposed to be conceptual aids.







It is not at all clear to me looking at some of these notes what they consider to be axioms, what is self evident and what must be shown. And yet they are very firm on the point on writing out all the steps. Incredibly puzzling.







One possible interpretation of what we are doing is that we have numerical measures associated with each angle. Perhaps we are identifying the theory of angles with some axioms in the theory of reals or perhaps the rationals.  I'm only suggesting this to point out how ridiculous complex the machinery that would be brought to bear on a simple problem.






    
    <code>Require Import Reals.
    
    Definition right_angle := 90%R.
    Definition line := 180.
    Definition supplementary = 180
    </code>







Vertical Angles and the cone counterexample. Not very compelling



