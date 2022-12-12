---
date: 2022-12-11
layout: post
title: "Datalog as a Theorem Prover: Harrop Clauses-lite"
description: 
tags: datalog rust
---

[Datalog](https://www.philipzucker.com/datalog-book/) is a really cool technology because it is both declarative, intuitive and high performance. The core algorithms can be accomplished using database technology, which has become very refined over the years.

Datalog is a relative of [prolog](https://www.metalevel.at/prolog). Prolog and Datalog programs are roughly described as being made of [Horn clauses](https://en.wikipedia.org/wiki/Horn_clause), which can be considered a subset of first order logic.

Datalog as a theorem prover is discussed even less than prolog's character as a theorem prover.
The Nadathur and Miller book [Programming with Higher Order Logic](https://www.google.com/books/edition/Programming_with_Higher_Order_Logic/xKsgAwAAQBAJ?hl=en&gbpv=1&printsec=frontcover) has an excellent discussion of the logical semantics of prolog. This book is a classic. It is so rich with insight, I'm hard pressed to think of another book that is its equal.

This blog post is trying to illuminate the class of formulas that Datalog or Datalog with light preprocessing is a prover for.

# Prolog
Prolog works via what can be described as top-down, backwards, or goal-directed inference, trying to construct a proof tree backwards from a given goal formula. 

Prolog has a few pieces.
- Clauses or rules which consist of a head and body.
- A notion of query which you enter in at the repl. It's easy to forget about this part, but it is kind of crucial for what follows.
- Unification variables, which are denoted by constants that start with a capitalized letter.

Prolog works by maintaining a goal list state which is initialized by the user given query. It matches (unifies) these goals against the heads of rules, and if successful replaces that goal with the body of the rule in the state. It can choose a rule that leads down a blind alley, so it maintains the ability to backtrack these choices and try another rule.

Prolog as described above can be seen as logical. `:-` is like implication. Unification variables are implicitly forall quantified in the program clauses and implicitly existentially quantified in the goal formula. But there is a slightly richer logical formula representation.

## Horn Clauses

One presentation of Horn clauses is (Section 2.3 of Nadathur and Miller)

```
G ::= True | A | G ∧ G | G ∨ G | ∃τ x G
D ::= A | G ⊃ D | D ∧ D | ∀x, D
```

When you give prolog a program clause file P, and state a query G in the repl it can be thought of as setting up a sequent  `P |- G` for which you want prolog to find a proof tree.

An operational interpretation can be given to breaking down the goal formula in this sequents in prolog. Breaking down a compound goal is automatic and does not represent a backtracking step. These rules are [invertible](https://www.cs.cmu.edu/~fp/courses/oregon-m10/04-focusing.pdf), meaning we have not committed to a possibly bad thing by taking them.



- to prove the goal `P |- G1 /\ G1`, prove `P |- G1` and then `P |- G2`

In inference rule form this looks like ths right introduction rule

```
`P |- G1`           P |- G2
----------------------------------- /\ R
        P |- G1 /\ G1`  
```

- to prove the goal `P  |- G1 \/ G1`, try proving `P |- G1` and if that doesn't work try `P |- G2`

- `P |- exists X, G` introduce a fresh unification X. 

These unification variables introduced here are really metavariables, standing for an as yet determined actual term.

There is something a bit weird about not tracking existential metavariables in the sequent. They allow spooky action at a distance in the proof search, which can be disconcerting. Minikanren is more explicit on this point, purely functionally carrying a substitution dictionary.

Prolog for free will prove a stronger theorem than the one asked for. A metavariable in the answer substitution represents a universal quantification when all you asked for as an existential one. This is very cool.

A subtle point. If the answer is ungrounded, this is proving a universal quantification, but a universal only proves an existential if the sort in question is non empty, so actually it is returning a stronger theorem and a proof obligation for non emptiness.  In the unityped setting this is less apparent.

# Harrop Clauses
 
There is an extension of horn clauses called hereditary Harrop clauses which also have an operational character. [Lambda prolog](https://www.lix.polytechnique.fr/~dale/lProlog/) directly supports these. Enriching the set of formula you support is good. 


```
G ::= True | A | G ∧ G | G ∨ G | ∃τ x G | D ⊃ G | ∀x G
D ::= A | G ⊃ D | D ∧ D | ∀x D
```

The additions compared to the above Horn clause structure is implication and forall are allowed in the goal formula. We now add a parameter `S` to the sequent to represent the signature.

- `P ; S |- D -> G` puts a new program clause into the database `(D :: P) ; S |- G`. 

- `P ; S |- forall x, G` introduce a new fresh constant `P ; (x :: S) |- G`

We can see that implication and forall are related. In dependent type theory implication is just a forall where you ignore the argument in the rest of the type `A -> B = forall x : A, B`. Likewise bounded quantifiers $\forall_S x, P$ can be usefully expanded as $\forall x, S \rightarrow P$ when you are modeling this construct in a first order theorem prover.

The forall rule also gives us a principled way to generate well scoped fresh names. This interplays with lambda prolog's ability to talk about lambda terms.

What's really beautiful and powerful seeming is that the program and goal formulas are mutually recursively defined.

# Backchaining
The above rules break down the goal formula, but eventually it becomes atomic. What then?
Then comes the backchaining phase where the logic program selects a program clause to resolve against the goal.

This has something to do with [focusing](https://www.cs.cmu.edu/~fp/courses/15816-f16/lectures/18-focusing.pdf) 

Prolog's default depth first search strategy hurts it's character as a theorem prover. There is much to be gained from this convention, as it increases it's predictable character as a operational programming language.

Datalog is superior on this count. It breadth first searches through forward inference and cannot get caught digging down as dusty alley.

# Datalog
Datalog works via bottom up / forward inference.

What Datalog support.
- We can assert facts to go right in the database like`edge(1,2).`. 
- We can assert rules like `path(x,z) :- edge(x,y), path(y,z).`. Operationally speaking, the body is a SQL-like query matched (not unified!) against the database, for which the query result is used to fill out the head. Because of how this works, every variable occurring in the head must be bound in the body. If it isn't, what are you going to fill it out with? Well we can imagine some ideas (to be discussed), but that is not stock Datalog.

# Bounded Horn Clauses
What is the set of formulas that Datalog can prove?

Datalog does not support Horn clauses in the sense described above. "Outrage!" you scream at me, readying to tear me apart limb from limb. 

Datalog does not _really_ support either of Horn or Harrop, but can handle restrictions.

The issue with horn clauses is the universal quantifier in D formula. It isn't a full universal quantifier. It is more like a  [Bounded Quantifiers](https://en.wikipedia.org/wiki/Bounded_quantifier) which is a much weaker notion. What s kind of interesting is that the bound relation for the quantifier is mutually recursively defined, and not necessarily some a priori fixed range.

```
G ::= True | A | G ∧ G | G ∨ G | ∃τ x, G
D ::= A | G ⊃ D | D ∧ D | ∀x y z..:G, D
```

This is all basically non surprising. D formula can be expanded into a normal form expected by a typical datalog engine. Souffle datalog supports the [disjunction operator](https://souffle-lang.github.io/rules#disjunction) in rule bodys as `;` and [multiheaded conjunction](https://souffle-lang.github.io/rules#multiple-heads) rules `,`.

Goals correspond to reasonable queries you can make over a database. Existentials are variables in the query, and the query can be expanded into [disjunctive normal form](https://en.wikipedia.org/wiki/Disjunctive_normal_form).
You can also turn goals into rules via introducing a `proven` predicate. Then a goal G can be expanded into clauses producing thi predicate

```souffle
// exists x, g(x)
proven() :- g(_x).

// G1 /\ G2
proven() :- g1, g2.

// G1 \/ G2
proven() :- g1.
proven() :- g2.
// or identically
proven() :- g1; g2.
```

Likewise the expansion of rules can be written a a set rewriting system

```
D1 /\ D2 :- G    --> {D2 :- G, D2 :- G}
D :- (G1 \/ G2)  --> {D :- G1, D :- G2} 
D :- (exists x, G1) --> {D :- G1} // alpha renaming for any variable clashes
D :- (G1 /\ G2) --> {D :- G1, G2}
```

# Harrop-Lite

Ok, so how much of Harrop clauses can we do? Well, I've been on a wild goose chase on this one, but I think the following is the simple point in the design space.

We stratify goals into two kinds. One is in essence the same as it appears in horn clauses, which I will now call Q for queries and one contains the extra Harrop formula.

```
G ::= True | Q | G ∧ G | G ∨ G | ∃x G | D ⊃ G | ∀x G
D ::= A | | Q ⊃ D | D ∧ D | ∀x..:Q, D
Q ::= True | A | Q ∧ Q | Q ∨ Q | ∃x Q
```


- `D -> G` can be simply inverted by inserting the clause D into the datalog program.
- `∀x G` can be dealt with by creating a fresh constant and instantiating it in the formula.

Perhaps less interesting and more optional are
- `G /\ G` is dealt with by forking the database into two process and waiting for both to come back true.
- `G \/ G` is dealt with by forking the database search into two processes and seeing if one comes back proven


Note that despite the richness of G, this set of formula is _not_ mutually recursive. So it is weaker than Harrop clauses because the quantification.

One way of describing what is happening here is we are permitting 1 pass of goal breakdown as generative metaprogramming of a datalog program.

The D rule `Q -> D` is redundant as it represents a bounded quantifier that does not use it's bound variables. 

# Is that it?
No, but this is essentially the set of formula that can be operationally interpreted in normal stock datalog without too much agony. By agony, I mean with the true bulk search occurring in the datalog engine itself and where the proving process proceeds via generative metaprogramming and not deeper matching on the structure of the program clauses.

Going beyond that requires funky features or weird encodings and it appears thus far that the farther you go afield the harder the going is.

## Existentials
This is a really cool one actually. Can you add existentials to the heads of program clauses? It appears so.
These are rules that are called tuple generating dependencies in the database community and are one of the subjects of the topic known as the chase. Some other topics to search for "Existential Datalog", "datalog +/-"

```
G ::= Q | G ∧ G | G ∨ G | ∃x G | D ⊃ G | ∀x G
D ::= A | D ∧ D | ∀x..:PG, D | ∃x D
Q ::= True | A | Q ∧ Q | Q ∨ Q | ∃x Q
```

This can be encoded using gensym/autoinc counters to create fresh terms for the existentials, or datatypes to create skolem symbols, for which you probably get better performance and termination properties. Datatypes are a bit problematic because the skolem symbols aren't persay not equal to other constants, but datatypes are. A slightly sticky point.

- [Benchmarking the chase](https://www.cs.ox.ac.uk/boris.motik/pubs/bkmmpst17becnhmarking-chase.pdf)
- [The chase revisited](https://dbucsd.github.io/paperpdfs/2008_8.pdf)


## Equality

Equality is arguably part of the formula `A`. This is choice. These are called equality generating dependencies. Equality in the queries Q is unproblematic until you add equality to D. Now the two interplay and you've got some challenges.

This is also the subject of the chase and egglog.

```
G ::= Q | G ∧ G | G ∨ G | ∃x G | D ⊃ G | ∀x G
D ::= A | t1 = t2 | D ∧ D | ∀x..:Q, D
Q ::= True | A | Q ∧ Q | Q ∨ Q | ∃x Q | t1 = t2
```

## Hypotheses / Contexts

Can `Q ⊃ D` becomes `G ⊃ D`? It'd be really nice. That would get use back 

This is one of the extensions that is most tempting and still pretty cloudy how to do it right or even _really_ what it is I even want. I currently have some reason to believe that I don't want set-like contexts but instead something more like evaluation contexts.
Some terms for this are Contextual datalog, hypothetical datalog, or scoped datalog.

- [Blog post on contextual datalog](https://www.philipzucker.com/contextual-datalog/) First class sets and subsumption are useful features for modelling the frontier of weakest assumptions.
- [Implementing Tabled Hypothetical Datalog](http://www.fdi.ucm.es/profesor/fernan/FSP/Sae13c.pdf)

# Negation

Negation is a whole thing and has sent the logic programming into fits since the beginning. There are stories about how to do it right, but it's nuanced.

[Negation as failure](https://en.wikipedia.org/wiki/Negation_as_failure)

Many datalog's support stratified negation. Under some situations, negation can be used to model swap and/or and forall/exists. This is a tricky topic.

# Disjunction

Disjunction in the head of rules (In the D formula) also requires more magumbo than a stock datalog allows. This is something like what [answer set programming](https://en.wikipedia.org/wiki/Answer_set_programming) ([notes](https://www.philipzucker.com/notes/CS/constraint-programming/#answer-set-programming)) supports. ASP is something akin to slamming a datalog ad SAT solver together.
See also [DLV](https://www.dbai.tuwien.ac.at/proj/dlv/tutorial/), disjunctive datalog

# Lambda Terms / Higher Order Logic
Lambda prolog of course has built in stuff for this. But, for datalog, I don't even know, man.
- [Lambda Normalization for Souffle Datalog](https://www.philipzucker.com/lambda-datalog-souffle/)
You can write static analyses _about_ lambda terms/scheme
- [So You Want to Analyze Scheme Programs With Datalog?](https://arxiv.org/abs/2107.12909)
- [A Systematic Approach to Deriving Incremental Type Checkers](https://szabta89.github.io/publications/inca-typechecking.pdf)
But these feel like encodings and don't quite satisfy me. I want the datalog itself to be doing more heavy lifting.

Also how does nominal logic interact with datalog? Good, bad? Dunno. See [alpha prolog](https://homepages.inf.ed.ac.uk/jcheney/programs/aprolog/) and alpha kanren for nominal logic in the prolog like setting.

# Are formulas even the thing to be talking about
I actually kind personally de-emphasize this perspective. Instead I like the think of datalog/prolog rules as corresponding to inference rules (the horizontal line) and datalog/prolog predicates correspond to judgements. See these [Pfenning notes](https://www.cs.cmu.edu/~fp/courses/15317-f17/lectures/18-datalog.pdf).

Datalog is an engine for breadth first exploration of forward inferences. Every piece of knowledge that datalog asserts is _justified_. One can extract a judgemental proof tree for any fact derived by a datalog execution using some lightweight extra tagging. This is in distinction to traditional resolution based theorem provers or SMT solvers which have a much more classical bent. They can make guesses. Datalog has a more constructive feel from this perspective.

From a pragmatic standpoint, every datalog operation has an operational as well as logical character. Only inferring justifiable rules enables the datalog inference process to be more predictable and controllable in my experience than classical solvers. Perhaps as Zach put it "You can play computer".

# Bits and Bobbles


Alternative suggested names: Bounded Harrop formula, Non-recursive Harrop formula

It seems plausible to me that harrop-lite can extended to a hierarchy that is still finite by deeper.

An interplay of a stronger prolog process as a metaprogram or subprogram of the datalog program could be an interesting thing. Souffle's inline relatins can be seen as a weak terminating prolog metaprogram.

Contexts also have a hierarchy that may be useful. 1-contexts, 2-contexts, and so on and then sut them off. This is remininscent of how context is treated in abstract interpretation

Really a list of these, which represent the current leaves of a partially constructed proof tree.

```
G ::= Top | A | G ∧ G | G ∨ G | ∃τ x G
D ::= A | G ⊃ D | D ∧ D | ∀x:bounds, D
```

In a sense, the requirement of needing a G is



The truth values aren't booleans. The two values are unknown and proven, not true and false. They are like Marshall B's sierpinski trth values

`CoInductive Sierp := Unsure Sierp | Proven.`

```python
def goldbach():
    i = 4
    while True:
        i += 2 # even numbers
        for j in range(i):
            if isprime(j) and isprime(j - i):
                return True
        yield None

```


where G is a formula that grounds the variables being introduced.
(Hmm. But is it ok tht G includes \/? The DNF expansion must include the variables being introduced.
So undert more complicated conditions that A can become a 
The bounds can also be a primitive enumerator like `range` or `nats`.
Using A is a bummer because 
`forall x (b(x) \/ c(x)), q(x)` is fine but we have to reformulate it as `forall x: b(x), q(x) /\ forall x: c(x), q(x)`

)

A bottom up technique 

Each one of these additions is hard fought.

The chase
skolemization
egglog

A gensym or autoinc counter can be used to invent new symbols.
Significantly better is to use skolem functions. These essentially record the reason by .
What is weak or subtly undesirable about this is that creating a skolem function as a _datatype_ is that the existential doesn't guarantee a new thing. There may be something that already exists to satisfy the need of the existential.
It also is somewhat implying that there is a unique element that satisfies the existential. This is why we can't use egglog union to "delete" the skolem.
It is not easy to tell when you can soundly assume the outputs of the skolem function are != from other types.


g and equality generating in the database community. They can be used to specify functional dependencies.
a = b :- f(x,a), f(x,b).
f(x,a) != :- a != b. // coinductive rule

Support higher order constructs.
Curried rules can be supported in a different way via defining new predciates.
There's kind f a cute normal form for datalog programs of binary lcayses. Ths presuppose a query ordering, which maye be indesirable since a benefit of the datalog approach is to have big queries that the database has descided how to break up.

Egglog supports an intrinsic notion of equality. It is a presentational choice to decide whether equaliy is part of the logic or not. It is such an important notion it often is.

slog 

# Example Rust Implementation for Egglog
<https://github.com/mwillsey/egg-smol/pull/79>

```rust
use crate::*;
impl EGraph {
    fn calc_helper(
        &mut self,
        idents: Vec<IdentSort>,
        exprs: Vec<Expr>,
        depth: &mut i64,
    ) -> Result<(), Error> {
        self.push();
        *depth += 1;
        // Insert fresh symbols for locally universally quantified reasoning.
        for IdentSort { name, sort } in idents {
            let sort = self.sorts.get(&sort).unwrap().clone();
            self.declare_const(name, &sort)?;
        }
        // Insert each expression pair and run until they match.
        for ab in exprs.windows(2) {
            let a = &ab[0];
            let b = &ab[1];
            self.push();
            *depth += 1;
            self.eval_expr(a, None, true)?;
            self.eval_expr(b, None, true)?;
            let cond = Fact::Eq(vec![a.clone(), b.clone()]);
            self.run_command(
                Command::Run(RunConfig {
                    limit: 100000,
                    until: Some(cond.clone()),
                }),
                true,
            )?;
            self.run_command(Command::Check(cond), true)?;
            self.pop().unwrap();
            *depth -= 1;
        }
        self.pop().unwrap();
        *depth -= 1;
        Ok(())
    }

    // Prove a sequence of equalities universally quantified over idents
    pub fn calc(&mut self, idents: Vec<IdentSort>, exprs: Vec<Expr>) -> Result<(), Error> {
        if exprs.len() < 2 {
            Ok(())
        } else {
            let mut depth = 0;
            let res = self.calc_helper(idents, exprs, &mut depth);
            if res.is_err() {
                // pop egraph back to original state if error
                for _ in 0..depth {
                    self.pop()?;
                }
            } else {
                assert!(depth == 0);
            }
            res
        }
    }

    fn run_query_formula(&mut self, goal: Query) -> Result<(), Error> {
        match goal {
            Query::Atom(fact) => {
                if self.check_fact(&fact, true).is_err() {
                    println!("{}", self.summary());
                    // I should actually have run check until first if it doesn't already
                    self.run_command(
                        Command::Run(RunConfig {
                            limit: 100000,
                            until: Some(fact.clone()),
                        }),
                        true,
                    )?;
                    self.check_fact(&fact, true)
                } else {
                    Ok(())
                }
            }
            Query::And(goals) => {
                for goal in goals {
                    self.run_query_formula(goal)?;
                }
                Ok(())
            }
        }
    }
    fn body_from_query(body: &mut Vec<Fact>, sig: &HashSet<Symbol>, g: Query) {
        match g {
            Query::Atom(f) => {
                // TODO: check all pattern variables in f are in sig.
                body.push(f)
            }
            Query::And(goals) => {
                for goal in goals {
                    EGraph::body_from_query(body, sig, goal);
                }
            }
        }
    }
    fn assert_prog_helper(
        &mut self,
        body: &mut Vec<Fact>,
        sig: &mut HashSet<Symbol>,
        prog: Prog,
    ) -> Result<(), Error> {
        match prog {
            Prog::Atom(action) => {
                if body.is_empty() {
                    self.eval_actions(&[action])
                } else {
                    let _ = self.add_rule(ast::Rule {
                        body: body.clone(),
                        head: vec![action],
                    })?; // TODO: allow duplicate rule error?
                    Ok(())
                }
            }
            Prog::And(progs) => {
                for prog in progs {
                    self.assert_prog_helper(&mut body.clone(), &mut sig.clone(), prog)?;
                }
                Ok(())
            }
            Prog::ForAll(idents, prog) => {
                for ident in idents {
                    assert!(!self.functions.contains_key(&ident.name));
                    // TODO: This should actually be shadowing.
                    assert!(!sig.contains(&ident.name));
                }
                self.assert_prog_helper(body, sig, *prog)
            }
            Prog::Implies(goal, prog) => {
                EGraph::body_from_query(body, sig, goal);
                self.assert_prog_helper(body, sig, *prog)
            }
        }
    }

    pub fn assert_prog(&mut self, prog: Prog) -> Result<(), Error> {
        self.assert_prog_helper(&mut vec![], &mut Default::default(), prog)
    }
    fn reduce_goal(&mut self, goal: Goal) -> Result<(), Error> {
        match goal {
            Goal::ForAll(idents, goal) => {
                for IdentSort { name, sort } in idents {
                    let sort = self.sorts.get(&sort).unwrap().clone();
                    self.declare_const(name, &sort)?;
                }
                self.reduce_goal(*goal)
            }
            Goal::Query(goal) => self.run_query_formula(goal),
            Goal::Implies(prog, goal) => {
                self.assert_prog(prog)?;
                self.reduce_goal(*goal)
            }
        }
    }
    pub fn prove_goal(&mut self, goal: Goal) -> Result<(), Error> {
        self.push();
        let res = self.reduce_goal(goal);
        self.pop().unwrap();
        res
    }
}
```
