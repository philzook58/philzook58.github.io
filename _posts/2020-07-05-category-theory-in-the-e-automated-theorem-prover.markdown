---
author: philzook58
comments: true
date: 2020-07-05 17:08:52+00:00
layout: post
link: https://www.philipzucker.com/category-theory-in-the-e-automated-theorem-prover/
slug: category-theory-in-the-e-automated-theorem-prover
title: Category Theory in the E Automated Theorem Prover
wordpress_id: 2853
categories:
- Formal Methods
tags:
- atp
- categorytheory
- logic
---




At least in the circles I travel in, interactive theorem provers like Agda, Coq, Lean, Isabelle have more mindspace than automatic theorem provers. I haven't seen much effort to explore category theory in the automatic provers so I thought I'd try it.







### Interactive Systems







There are a number of projects formalizing category theory in these systems







  * [https://github.com/agda/agda-categories](https://github.com/agda/agda-categories)
  * [https://github.com/statebox/idris-ct](https://github.com/statebox/idris-ct)
  * [https://github.com/jwiegley/category-theory](https://github.com/jwiegley/category-theory)
  * [https://arxiv.org/pdf/1401.7694.pdf](https://arxiv.org/pdf/1401.7694.pdf)
  * [https://www.isa-afp.org/](https://www.isa-afp.org/) search for category. There are a couple.
  * [https://mathoverflow.net/questions/152497/formalizations-of-category-theory-in-proof-assistants](https://mathoverflow.net/questions/152497/formalizations-of-category-theory-in-proof-assistants) - Thanks to Eduardo Ochs for pointing this out
  * Many more






All of these systems are using some variant of higher order logic where you can quantify over propositions. This is very expressive, but also are more difficult to automate (They _do_ have significant automation in them though, but this tends to be for filling in the relatively obvious intermediate details of a proof, not complete automation). Perhaps this has some relation to [Godel's incompleteness theorem](https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems)







### Automated Theorem Provers







There are other classes of theorem proving systems: automatic theorem provers and SMT solvers. Can we do category theory in them? Doesn't Automatic sound real nice in principle?







ATP and SMT are similar in some respects but are architected differently and have slightly different use cases and strengths:







  * SMT solvers are based around SAT solvers and tractable sub problems (theories). They have subsystems that deeply understand linear equations, linear inequalities, systems of polynomials, theory of uninterpreted functions, bit-blasting, others. They combine these facilities via the Nelson-Oppen procedure. They are fairly weak at quantifier reasoning. They are good at problems that require lots of domain specific understanding. Examples of SMT solvers include Z3, CVC4, Alt Ergo, Boolector. You can find more and comparisons at the [SMT competition](https://smt-comp.github.io/2020/news/2020-07-05)
  * While the term Automatic Theorem Prover (ATP) could mean anything, it has a tendency to denote a class of first order logic solvers based around [resolution](https://en.wikipedia.org/wiki/Resolution_(logic)). Examples of such provers include Vampire, E, and Prover9. You can find more at the [CADE competition](http://www.tptp.org/CASC/27/WWWFiles/DivisionSummary1.html). They are more oriented to abstract first order logic structures and quantifier reasoning.






A big downside of automatic methods is that once they start to fail, you're more hosed than the interactive provers. Until then, it's great though.







### Categories in ATP







Category theory proofs have a feeling of being close to trivial (at least the ones I've seen, but I've mostly seen the trivial ones so...? ), amounting to laboriously expanding definitions and rewrite equations corresponding to commutation conditions. An automatic system to verify these seems useful.







What are the kinds of questions one wants to ask these provers?







  * Confirmation that a concrete mathematical structure (integers, reals, bools, abstract/concrete preorder, group, lattice) obeys the required categorical axioms/interface. The axioms of category structures are the _conjectures_ here
  * Confirmation that abstract categorical constructions do what they're supposed to. One presupposes categorical axioms and structures and asks conjecture conclusions. For example, given this square, does this other diagram commute? Is this "[diagram chasing](https://en.wikipedia.org/wiki/Commutative_diagram)"?






These are yes/no questions. Although in the case of no, often a counterexample is emitted which can help show where you went awry. A third task that is more exciting to me, but harder and not an obvious stock capability of these provers is







  * Calculate/construct something categorical. For example, we might want to construct a condensed or efficient version of some program given by a categorical spec, or emit a categorical construction that has certain properties. There are clear analogies with program verification vs. program synthesis.






Now it appears that to some degree this is possible. I have noted that in the proof output, one can sometimes find terms that may correspond to the thing you desire, especially if you ask an existential conjecture, "does there exists a morphism with such and such a property".







### Formulating Category Theory in First Order Logic







[TPTP](http://www.tptp.org/) is both a problem library and specification language for first order problems for the purposes of computer provers. There is a nice overview [video here](https://www.youtube.com/watch?v=MzN-pR8n9wI&t=2s). There is a nice web interface to explore different provers [here](http://www.tptp.org/cgi-bin/SystemOnTPTP). The TPTP library contains four different axiomatizations for categories, and a number of problems







  * [http://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=CAT001-0.ax](http://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=CAT001-0.ax)
  * [http://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=CAT002-0.ax](http://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=CAT002-0.ax)
  * [http://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=CAT003-0.ax](http://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=CAT003-0.ax)
  * [http://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=CAT004-0.ax](http://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=CAT004-0.ax)






There is a good set of videos explaining how to formalize category axioms in a first order setting. [https://www.youtube.com/watch?v=NjDZMWdDJKM&list=PL4FD0wu2mjWOtmhJsiVrCpzOAk42uhdz8&index=6&t=0s](https://www.youtube.com/watch?v=NjDZMWdDJKM&list=PL4FD0wu2mjWOtmhJsiVrCpzOAk42uhdz8&index=6&t=0s) he has a couple different formulation actually. It's interesting.  Here's a stack overflow [https://math.stackexchange.com/questions/2383503/category-theory-from-the-first-order-logic-point-of-view](https://math.stackexchange.com/questions/2383503/category-theory-from-the-first-order-logic-point-of-view) along with a small discussion of why it's wrong headed to even do such a thing. I'm not sure I agree with the second part.







Here is my encoding. I am not 100% confident anything I've done here is right. Note that composition is expressed as a ternary relation. This is one way of handling the fact that without stronger typing discipline, composition is a_ partial_ binary function. In order to compose, morphisms need to meet on an intermediate object. Categorical "typing" is expressed via logical constraint on the relation.







A trick one can use is to identify the identity arrows and the objects at which they are based. Since every object is required to have an identity arrow and every identity arrow points from and to a single object, they are in isomorphism. There is some conceptual disclarity that occurs from this trick though. I'm not totally sold.







TPTP syntax is mostly straightforward but note that  ! [X] is forall X, ? [X] is exists X, capital names are variables, lowercase names are constants. Quantifiers bind tighter than I personally expected, hence my parenthesis explosion.






    
    
```

% axioms of a category
% we would resupply this for every category involved?
% ! [X] is forall X, ? [X] is exists X. Capital names are variables
% lowercase names are constants.
fof( dom_cod, axiom, ![X] : dom(cod(X)) = cod(X)).
fof( cod_dom, axiom, ![X] : cod(dom(X)) = dom(X)).
fof( comp_is_unique, axiom, ![F, G, FG1, FG2] : ((comp(F,G,FG1) & comp(F,G,FG2)) => FG1 = FG2)   ).
fof( comp_objects_middle, axiom, ![F, G] : ((? [FG] : comp(F,G,FG)) <=> dom(F) = cod(G))).
fof( comp_dom, axiom, ![F, G, FG] : (comp(F,G,FG) => dom(G) = dom(FG))).
fof( comp_cod, axiom, ![F, G, FG] : (comp(F,G,FG) => cod(F) = cod(FG))).
fof( left_id, axiom, ![F] : comp(cod(F),F,F) ).
fof( right_id, axiom, ![F] : comp(F,dom(F),F) ).
% I've heard that composition axioms cause churn?
fof( comp_assoc, axiom, ![F, G, H, FG, GH, FGH1, FGH2] : ((comp(F,G,FG) & comp(FG,H,FGH1) & comp(F,GH,FGH2) & comp(G,H,GH)) => FGH1 = FGH2  )).
```








Here are some definitions. One could also just inline these definitions with a macro system. [Uniqueness quantification](https://en.wikipedia.org/wiki/Uniqueness_quantification) occurs in universal properties. It's sort of a subtle idea to encode into ordinary first order logic without uniqueness quantification. Are some encoding better than others? Another place where macros to generate TPTP files would be useful. Uniqueness quantification is naturally expressible as a higher order predicate.






    
    
```

fof(monic_def, axiom,  
    ![M] : (monic(M) <=> (! [F,G] : (( ? [H] : (comp(M, F, H) & comp(M,G,H))) => F = G)))).

fof(commute_square_def, axiom, 
    ![F,G,H,K] : (commute_square(F,G,H,K) <=> (? [M] : (comp(F,G,M) & comp(H,K,M))))).

fof(pullback_def, axiom,
   ![F,G,P1,P2] : (pullback(F,G,P1,P2) <=>
        (commute_square(F,P1,G,P2) &
        (![Q1,Q2] : (commute_square(F,Q1,G,Q2) => 
            (?[U] : (! [U1] : ((comp(P1,U1,Q1) & comp(P2,U1,Q2)) <=> (U1 = U))))
        ))))).

```








Here are some pretty simple problems:






    
    
```

% should be a trivial statement, but isn't literally an axiom.
fof( codcod, conjecture, ![F] : cod(cod(F)) = cod(F) ).


% paste two commuting squares together gives another commuting square
fof( pasting_square,conjecture,   ![A,B,C,D, I,J,K, BI, CJ] : ((commute_square(B,A,D,C) & commute_square(I,D,K,J) & comp(I,B, IB) & comp( J, C,JC)) 
                                                        =>  commute_square( IB,A, K,JC ) )).
```








One theorem that is not quite so trivial is the pullback of a monic is monic [https://math.stackexchange.com/questions/2957202/proving-the-pullback-of-monics-is-monic](https://math.stackexchange.com/questions/2957202/proving-the-pullback-of-monics-is-monic). It's ultimately not that complicated and yet difficult enough that it takes me a lot of head scratching. It crucially uses the uniqueness property of the pullback. Here's an encoding of the conjecture.






    
    
```

include('cat.tptp').
include('constructions.tptp').

% warmup?
%fof(pullback_monic, conjecture, ![M, P1,P2] : ((monic(M) & pullback(cod(M),M,P1,P2)) => %monic(P2))).

% pullback of monic is monic
fof(pullback_monic, conjecture, ![M, F, P1,P2] : ((monic(M) & pullback(F,M,P1,P2)) => monic(P1))).
```








Invoking the prover.






    
    
```

eprover --auto-schedule --cpu-limit=60 --proof-object monic_pullback.tptp
```








Vampire appears to do it faster. Again the easiest way to try it yourself or compare other solvers is the web interface System on TPTP [http://www.tptp.org/cgi-bin/SystemOnTPTP](http://www.tptp.org/cgi-bin/SystemOnTPTP). Caveat: given how many times I've screwed up writing this post, I'd give a 40% chance that that final theorem is actually expressing what I intended it to.







### Bits and Bobbles







Encoding our questions into first order logic, which is powerful but not fully expressive, requires a lot of "macro" like repetitiveness when possible at all. I have found through experience that the extra macro capabilities given by python for emitting Z3 problems to be extremely powerful. For this reason, we should use a real programming language to emit these problems. I think the logical candidate is Julia and the Catlab library.  One unknown question, will this repetitiveness choke the theorem prover? 







Categorical Constructions that one might want to encode:







  * Monic
  * Epic
  * Commuting Squares
  * Pullbacks
  * Pushouts
  * products
  * coproducts
  * exponential objects
  * Subobject classifiers
  * Finite categories
  * Functors
  * Natural transformations
  * Adjunctions
  * Kan Extensions
  * PreSheaves






Theorems that seem possible. (Surely there are many more.







  * The pullback of a monic is monic
  *  [five lemma](https://en.wikipedia.org/wiki/Five_lemma), 
  * the [snake lemma](https://en.wikipedia.org/wiki/Snake_lemma), 
  * the [zig-zag lemma](https://en.wikipedia.org/wiki/Zig-zag_lemma), 
  * and the [nine lemma](https://en.wikipedia.org/wiki/Nine_lemma).
  * [https://www.cs.le.ac.uk/people/rlc3/research/papers/mgs2015-categoryTheory-exercises.pdf](https://www.cs.le.ac.uk/people/rlc3/research/papers/mgs2015-categoryTheory-exercises.pdf)
  * [https://math.stackexchange.com/questions/54583/looking-for-students-guide-to-diagram-chasing](https://math.stackexchange.com/questions/54583/looking-for-students-guide-to-diagram-chasing)












Some observations on actually using these provers: Just because it says proved is not very convincing. It is very easy to have your axioms and/or conjecture stated incorrectly. Forall ! and Exists ? bind tighter than I naively expect them to in the syntax. I ended up putting parenthesis nearly everywhere. I had a lot of very difficult to debug problems due to bad binding assumptions. Typos are also a disaster. These things are hard to debug. It is helpful to alternatively ask for satisfiability (disproving the conjecture). One should also at least look at which axioms it's using. If it is using less axioms than makes sense, something is up. These are all good reasons that it might be better to automatically generate these problem files. Ultimately I feel like that is the way to go, because encoding what you're interested in into first order logic can require some repetitiveness.







Sanity checking my files with [http://www.tptp.org/cgi-bin/SystemB4TPTP](http://www.tptp.org/cgi-bin/SystemB4TPTP) proved to be helpful. Also looking at the parenthesis structure in the output.







I think using the typed tff format could also help sanity significantly. It really sucks that a typo on one of your predicates or variables can fail silently.







Even ignoring syntax screwups, the scoping of quantifiers is tough to think about.







I suspect that these systems will be very good for proofs that amount to unrolling definitions.







What is the best formulation for category theory properties?







An interesting property is that these provers seem to want a time limit given to them. And they schedule themselves in such a way to use the full time limit, even if they shouldn't need it.







Categorical "type checking" as an external predicate. In order to compose, morphisms need to meet on an intermediate object. 







The proof output is rather difficult to read. It is the equivalent of trying to read assembly code. The high level structure has been transformed into something more amenable to the machine and many names have been mangled. This proof is short enough that I think a person could stare at it for a while an eventually kind of understand it.







Perhaps we want to directly input our constructions in cnf form with skolemization manually applied. This might make the output more readable?







In terms of automated category theory proving, I'm not aware of that much work, but there must be more that I don't know how to find.







  * [https://www.cs.cornell.edu/~kozen/Papers/06ijcar-categories.pdf](https://www.cs.cornell.edu/~kozen/Papers/06ijcar-categories.pdf)
  * [https://www.cambridge.org/core/books/categories-and-computer-science/203EBBEE29BEADB035C9DD80191E67B1](https://www.cambridge.org/core/books/categories-and-computer-science/203EBBEE29BEADB035C9DD80191E67B1)
  * [http://www.cs.man.ac.uk/~david/categories/book/book.pdf](http://www.cs.man.ac.uk/~david/categories/book/book.pdf)






Example proof term: Is this even right? Hard to know.






    
    
```

# Proof found!
# SZS status Theorem
# SZS output start CNFRefutation
fof(pullback_monic, conjecture, ![X11, X13, X14]:((monic(X11)&pullback(cod(X11),X11,X13,X14))=>monic(X14)), file('properties.tptp', pullback_monic)).
fof(pullback_def, axiom, ![X2, X3, X13, X14]:(pullback(X2,X3,X13,X14)<=>(commute_square(X2,X13,X3,X14)&![X15, X16]:(commute_square(X2,X15,X3,X16)=>?[X17]:![X18]:((comp(X13,X18,X15)&comp(X14,X18,X16))<=>X18=X17)))), file('properties.tptp', pullback_def)).
fof(commute_square_def, axiom, ![X2, X3, X7, X12]:(commute_square(X2,X3,X7,X12)<=>?[X11]:(comp(X2,X3,X11)&comp(X7,X12,X11))), file('properties.tptp', commute_square_def)).
fof(comp_objects_middle, axiom, ![X2, X3]:(?[X6]:comp(X2,X3,X6)<=>dom(X2)=cod(X3)), file('cat.tptp', comp_objects_middle)).
fof(dom_cod, axiom, ![X1]:dom(cod(X1))=cod(X1), file('cat.tptp', dom_cod)).
fof(left_id, axiom, ![X2]:comp(cod(X2),X2,X2), file('cat.tptp', left_id)).
fof(comp_is_unique, axiom, ![X2, X3, X4, X5]:((comp(X2,X3,X4)&comp(X2,X3,X5))=>X4=X5), file('cat.tptp', comp_is_unique)).
fof(monic_def, axiom, ![X11]:(monic(X11)<=>![X2, X3]:(?[X7]:(comp(X11,X2,X7)&comp(X11,X3,X7))=>X2=X3)), file('properties.tptp', monic_def)).
fof(comp_cod, axiom, ![X2, X3, X6]:(comp(X2,X3,X6)=>cod(X2)=cod(X6)), file('cat.tptp', comp_cod)).
fof(comp_dom, axiom, ![X2, X3, X6]:(comp(X2,X3,X6)=>dom(X3)=dom(X6)), file('cat.tptp', comp_dom)).
fof(comp_assoc, axiom, ![X2, X3, X7, X6, X8, X9, X10]:((((comp(X2,X3,X6)&comp(X6,X7,X9))&comp(X2,X8,X10))&comp(X3,X7,X8))=>X9=X10), file('cat.tptp', comp_assoc)).
fof(c_0_11, negated_conjecture, ~(![X11, X13, X14]:((monic(X11)&pullback(cod(X11),X11,X13,X14))=>monic(X14))), inference(assume_negation,[status(cth)],[pullback_monic])).
fof(c_0_12, plain, ![X68, X69, X70, X71, X72, X73, X75, X76, X77, X78, X79, X80, X83]:(((commute_square(X68,X70,X69,X71)|~pullback(X68,X69,X70,X71))&((~comp(X70,X75,X72)|~comp(X71,X75,X73)|X75=esk7_6(X68,X69,X70,X71,X72,X73)|~commute_square(X68,X72,X69,X73)|~pullback(X68,X69,X70,X71))&((comp(X70,X76,X72)|X76!=esk7_6(X68,X69,X70,X71,X72,X73)|~commute_square(X68,X72,X69,X73)|~pullback(X68,X69,X70,X71))&(comp(X71,X76,X73)|X76!=esk7_6(X68,X69,X70,X71,X72,X73)|~commute_square(X68,X72,X69,X73)|~pullback(X68,X69,X70,X71)))))&((commute_square(X77,esk8_4(X77,X78,X79,X80),X78,esk9_4(X77,X78,X79,X80))|~commute_square(X77,X79,X78,X80)|pullback(X77,X78,X79,X80))&((~comp(X79,esk10_5(X77,X78,X79,X80,X83),esk8_4(X77,X78,X79,X80))|~comp(X80,esk10_5(X77,X78,X79,X80,X83),esk9_4(X77,X78,X79,X80))|esk10_5(X77,X78,X79,X80,X83)!=X83|~commute_square(X77,X79,X78,X80)|pullback(X77,X78,X79,X80))&((comp(X79,esk10_5(X77,X78,X79,X80,X83),esk8_4(X77,X78,X79,X80))|esk10_5(X77,X78,X79,X80,X83)=X83|~commute_square(X77,X79,X78,X80)|pullback(X77,X78,X79,X80))&(comp(X80,esk10_5(X77,X78,X79,X80,X83),esk9_4(X77,X78,X79,X80))|esk10_5(X77,X78,X79,X80,X83)=X83|~commute_square(X77,X79,X78,X80)|pullback(X77,X78,X79,X80)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[pullback_def])])])])])])).
fof(c_0_13, negated_conjecture, ((monic(esk11_0)&pullback(cod(esk11_0),esk11_0,esk12_0,esk13_0))&~monic(esk13_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
fof(c_0_14, plain, ![X58, X59, X60, X61, X63, X64, X65, X66, X67]:(((comp(X58,X59,esk6_4(X58,X59,X60,X61))|~commute_square(X58,X59,X60,X61))&(comp(X60,X61,esk6_4(X58,X59,X60,X61))|~commute_square(X58,X59,X60,X61)))&(~comp(X63,X64,X67)|~comp(X65,X66,X67)|commute_square(X63,X64,X65,X66))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[commute_square_def])])])])])])).
cnf(c_0_15, plain, (commute_square(X1,X2,X3,X4)|~pullback(X1,X3,X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
cnf(c_0_16, negated_conjecture, (pullback(cod(esk11_0),esk11_0,esk12_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
fof(c_0_17, plain, ![X25, X26, X27, X28, X29]:((~comp(X25,X26,X27)|dom(X25)=cod(X26))&(dom(X28)!=cod(X29)|comp(X28,X29,esk1_2(X28,X29)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[comp_objects_middle])])])])])).
cnf(c_0_18, plain, (comp(X1,X2,esk6_4(X1,X2,X3,X4))|~commute_square(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
cnf(c_0_19, negated_conjecture, (commute_square(cod(esk11_0),esk12_0,esk11_0,esk13_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
fof(c_0_20, plain, ![X19]:dom(cod(X19))=cod(X19), inference(variable_rename,[status(thm)],[dom_cod])).
fof(c_0_21, plain, ![X37]:comp(cod(X37),X37,X37), inference(variable_rename,[status(thm)],[left_id])).
cnf(c_0_22, plain, (dom(X1)=cod(X2)|~comp(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
cnf(c_0_23, negated_conjecture, (comp(cod(esk11_0),esk12_0,esk6_4(cod(esk11_0),esk12_0,esk11_0,esk13_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
cnf(c_0_24, plain, (dom(cod(X1))=cod(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
fof(c_0_25, plain, ![X21, X22, X23, X24]:(~comp(X21,X22,X23)|~comp(X21,X22,X24)|X23=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[comp_is_unique])])).
cnf(c_0_26, plain, (comp(cod(X1),X1,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
cnf(c_0_27, negated_conjecture, (cod(esk12_0)=cod(esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
fof(c_0_28, plain, ![X46, X47, X48, X49, X50]:((~monic(X46)|(~comp(X46,X47,X49)|~comp(X46,X48,X49)|X47=X48))&(((comp(X50,esk2_1(X50),esk4_1(X50))|monic(X50))&(comp(X50,esk3_1(X50),esk4_1(X50))|monic(X50)))&(esk2_1(X50)!=esk3_1(X50)|monic(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[monic_def])])])])])])).
cnf(c_0_29, plain, (X3=X4|~comp(X1,X2,X3)|~comp(X1,X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
cnf(c_0_30, negated_conjecture, (comp(cod(esk11_0),esk12_0,esk12_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
fof(c_0_31, plain, ![X34, X35, X36]:(~comp(X34,X35,X36)|cod(X34)=cod(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[comp_cod])])).
cnf(c_0_32, negated_conjecture, (~monic(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
cnf(c_0_33, plain, (comp(X1,esk2_1(X1),esk4_1(X1))|monic(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
cnf(c_0_34, plain, (comp(X1,X2,esk6_4(X3,X4,X1,X2))|~commute_square(X3,X4,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
cnf(c_0_35, plain, (comp(X1,esk3_1(X1),esk4_1(X1))|monic(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
cnf(c_0_36, negated_conjecture, (X1=esk12_0|~comp(cod(esk11_0),esk12_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
cnf(c_0_37, plain, (cod(X1)=cod(X3)|~comp(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
cnf(c_0_38, negated_conjecture, (comp(esk13_0,esk2_1(esk13_0),esk4_1(esk13_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
cnf(c_0_39, negated_conjecture, (comp(esk11_0,esk13_0,esk6_4(cod(esk11_0),esk12_0,esk11_0,esk13_0))), inference(spm,[status(thm)],[c_0_34, c_0_19])).
cnf(c_0_40, negated_conjecture, (comp(esk13_0,esk3_1(esk13_0),esk4_1(esk13_0))), inference(spm,[status(thm)],[c_0_32, c_0_35])).
fof(c_0_41, plain, ![X31, X32, X33]:(~comp(X31,X32,X33)|dom(X32)=dom(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[comp_dom])])).
cnf(c_0_42, negated_conjecture, (esk6_4(cod(esk11_0),esk12_0,esk11_0,esk13_0)=esk12_0), inference(spm,[status(thm)],[c_0_36, c_0_23])).
cnf(c_0_43, negated_conjecture, (cod(esk4_1(esk13_0))=cod(esk13_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
cnf(c_0_44, negated_conjecture, (cod(esk13_0)=dom(esk11_0)), inference(spm,[status(thm)],[c_0_22, c_0_39])).
cnf(c_0_45, plain, (comp(X1,X2,esk1_2(X1,X2))|dom(X1)!=cod(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
cnf(c_0_46, negated_conjecture, (cod(esk3_1(esk13_0))=dom(esk13_0)), inference(spm,[status(thm)],[c_0_22, c_0_40])).
cnf(c_0_47, plain, (dom(X2)=dom(X3)|~comp(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
cnf(c_0_48, negated_conjecture, (comp(esk11_0,esk13_0,esk12_0)), inference(rw,[status(thm)],[c_0_39, c_0_42])).
cnf(c_0_49, negated_conjecture, (cod(esk4_1(esk13_0))=dom(esk11_0)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
fof(c_0_50, plain, ![X39, X40, X41, X42, X43, X44, X45]:(~comp(X39,X40,X42)|~comp(X42,X41,X44)|~comp(X39,X43,X45)|~comp(X40,X41,X43)|X44=X45), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[comp_assoc])])).
cnf(c_0_51, negated_conjecture, (comp(X1,esk3_1(esk13_0),esk1_2(X1,esk3_1(esk13_0)))|dom(X1)!=dom(esk13_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
cnf(c_0_52, negated_conjecture, (dom(esk12_0)=dom(esk13_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
cnf(c_0_53, negated_conjecture, (comp(X1,esk4_1(esk13_0),esk1_2(X1,esk4_1(esk13_0)))|dom(X1)!=dom(esk11_0)), inference(spm,[status(thm)],[c_0_45, c_0_49])).
cnf(c_0_54, plain, (X5=X7|~comp(X1,X2,X3)|~comp(X3,X4,X5)|~comp(X1,X6,X7)|~comp(X2,X4,X6)), inference(split_conjunct,[status(thm)],[c_0_50])).
cnf(c_0_55, negated_conjecture, (comp(esk12_0,esk3_1(esk13_0),esk1_2(esk12_0,esk3_1(esk13_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
cnf(c_0_56, negated_conjecture, (cod(esk2_1(esk13_0))=dom(esk13_0)), inference(spm,[status(thm)],[c_0_22, c_0_38])).
cnf(c_0_57, plain, (commute_square(X1,X2,X4,X5)|~comp(X1,X2,X3)|~comp(X4,X5,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
cnf(c_0_58, negated_conjecture, (comp(esk11_0,esk4_1(esk13_0),esk1_2(esk11_0,esk4_1(esk13_0)))), inference(er,[status(thm)],[c_0_53])).
cnf(c_0_59, negated_conjecture, (esk1_2(esk12_0,esk3_1(esk13_0))=X1|~comp(X2,esk3_1(esk13_0),X3)|~comp(X4,X2,esk12_0)|~comp(X4,X3,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
cnf(c_0_60, negated_conjecture, (comp(X1,esk2_1(esk13_0),esk1_2(X1,esk2_1(esk13_0)))|dom(X1)!=dom(esk13_0)), inference(spm,[status(thm)],[c_0_45, c_0_56])).
cnf(c_0_61, plain, (X2=esk7_6(X6,X7,X1,X4,X3,X5)|~comp(X1,X2,X3)|~comp(X4,X2,X5)|~commute_square(X6,X3,X7,X5)|~pullback(X6,X7,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
cnf(c_0_62, negated_conjecture, (commute_square(X1,X2,esk11_0,esk4_1(esk13_0))|~comp(X1,X2,esk1_2(esk11_0,esk4_1(esk13_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
cnf(c_0_63, negated_conjecture, (cod(esk1_2(esk11_0,esk4_1(esk13_0)))=cod(esk11_0)), inference(spm,[status(thm)],[c_0_37, c_0_58])).
cnf(c_0_64, negated_conjecture, (esk1_2(esk12_0,esk3_1(esk13_0))=esk1_2(esk11_0,esk4_1(esk13_0))|~comp(X1,esk3_1(esk13_0),esk4_1(esk13_0))|~comp(esk11_0,X1,esk12_0)), inference(spm,[status(thm)],[c_0_59, c_0_58])).
cnf(c_0_65, negated_conjecture, (comp(esk12_0,esk2_1(esk13_0),esk1_2(esk12_0,esk2_1(esk13_0)))), inference(spm,[status(thm)],[c_0_60, c_0_52])).
cnf(c_0_66, negated_conjecture, (X1=esk7_6(cod(esk11_0),esk11_0,esk12_0,esk13_0,X2,X3)|~commute_square(cod(esk11_0),X2,esk11_0,X3)|~comp(esk13_0,X1,X3)|~comp(esk12_0,X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_16])).
cnf(c_0_67, negated_conjecture, (commute_square(cod(esk11_0),esk1_2(esk11_0,esk4_1(esk13_0)),esk11_0,esk4_1(esk13_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_26]), c_0_63])).
cnf(c_0_68, negated_conjecture, (esk1_2(esk12_0,esk3_1(esk13_0))=esk1_2(esk11_0,esk4_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_48]), c_0_40])])).
cnf(c_0_69, negated_conjecture, (esk1_2(esk12_0,esk2_1(esk13_0))=X1|~comp(X2,esk2_1(esk13_0),X3)|~comp(X4,X2,esk12_0)|~comp(X4,X3,X1)), inference(spm,[status(thm)],[c_0_54, c_0_65])).
cnf(c_0_70, negated_conjecture, (X1=esk7_6(cod(esk11_0),esk11_0,esk12_0,esk13_0,esk1_2(esk11_0,esk4_1(esk13_0)),esk4_1(esk13_0))|~comp(esk12_0,X1,esk1_2(esk11_0,esk4_1(esk13_0)))|~comp(esk13_0,X1,esk4_1(esk13_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
cnf(c_0_71, negated_conjecture, (comp(esk12_0,esk3_1(esk13_0),esk1_2(esk11_0,esk4_1(esk13_0)))), inference(rw,[status(thm)],[c_0_55, c_0_68])).
cnf(c_0_72, negated_conjecture, (esk1_2(esk12_0,esk2_1(esk13_0))=esk1_2(esk11_0,esk4_1(esk13_0))|~comp(X1,esk2_1(esk13_0),esk4_1(esk13_0))|~comp(esk11_0,X1,esk12_0)), inference(spm,[status(thm)],[c_0_69, c_0_58])).
cnf(c_0_73, negated_conjecture, (esk7_6(cod(esk11_0),esk11_0,esk12_0,esk13_0,esk1_2(esk11_0,esk4_1(esk13_0)),esk4_1(esk13_0))=esk3_1(esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_40]), c_0_71])])).
cnf(c_0_74, negated_conjecture, (esk1_2(esk12_0,esk2_1(esk13_0))=esk1_2(esk11_0,esk4_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_48]), c_0_38])])).
cnf(c_0_75, negated_conjecture, (X1=esk3_1(esk13_0)|~comp(esk12_0,X1,esk1_2(esk11_0,esk4_1(esk13_0)))|~comp(esk13_0,X1,esk4_1(esk13_0))), inference(rw,[status(thm)],[c_0_70, c_0_73])).
cnf(c_0_76, negated_conjecture, (comp(esk12_0,esk2_1(esk13_0),esk1_2(esk11_0,esk4_1(esk13_0)))), inference(rw,[status(thm)],[c_0_65, c_0_74])).
cnf(c_0_77, plain, (monic(X1)|esk2_1(X1)!=esk3_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
cnf(c_0_78, negated_conjecture, (esk3_1(esk13_0)=esk2_1(esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_38]), c_0_76])])).
cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_32]), ['proof']).
# SZS output end CNFRefutation
# Proof object total steps             : 80
# Proof object clause steps            : 57
# Proof object formula steps           : 23
# Proof object conjectures             : 44
# Proof object clause conjectures      : 41
# Proof object formula conjectures     : 3
# Proof object initial clauses used    : 18
# Proof object initial formulas used   : 11
# Proof object generating inferences   : 34
# Proof object simplifying inferences  : 16
# Training examples: 0 positive, 0 negative
# Parsed axioms                        : 14
# Removed by relevancy pruning/SinE    : 0
# Initial clauses                      : 31
# Removed in clause preprocessing      : 0
# Initial clauses in saturation        : 31
# Processed clauses                    : 4871
# ...of these trivial                  : 248
# ...subsumed                          : 2833
# ...remaining for further processing  : 1790
# Other redundant clauses eliminated   : 2
# Clauses deleted for lack of memory   : 0
# Backward-subsumed                    : 68
# Backward-rewritten                   : 917
# Generated clauses                    : 12894
# ...of the previous two non-trivial   : 12112
# Contextual simplify-reflections      : 0
# Paramodulations                      : 12870
# Factorizations                       : 0
# Equation resolutions                 : 24
# Propositional unsat checks           : 0
#    Propositional check models        : 0
#    Propositional check unsatisfiable : 0
#    Propositional clauses             : 0
#    Propositional clauses after purity: 0
#    Propositional unsat core size     : 0
#    Propositional preprocessing time  : 0.000
#    Propositional encoding time       : 0.000
#    Propositional solver time         : 0.000
#    Success case prop preproc time    : 0.000
#    Success case prop encoding time   : 0.000
#    Success case prop solver time     : 0.000
# Current number of processed clauses  : 772
#    Positive orientable unit clauses  : 155
#    Positive unorientable unit clauses: 0
#    Negative unit clauses             : 1
#    Non-unit-clauses                  : 616
# Current number of unprocessed clauses: 5468
# ...number of literals in the above   : 16715
# Current number of archived formulas  : 0
# Current number of archived clauses   : 1016
# Clause-clause subsumption calls (NU) : 303883
# Rec. Clause-clause subsumption calls : 253866
# Non-unit clause-clause subsumptions  : 2890
# Unit Clause-clause subsumption calls : 1530
# Rewrite failures with RHS unbound    : 0
# BW rewrite match attempts            : 1110
# BW rewrite match successes           : 80
# Condensation attempts                : 0
# Condensation successes               : 0
# Termbank termtop insertions          : 267453
```




