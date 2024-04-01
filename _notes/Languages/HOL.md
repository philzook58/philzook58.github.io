---
layout: post
title: HOL
---

# Axioms

Encoding forall
``\x P(x) = \x true` is saying that the predictae p is always true.

# HOL

- [cakeml](https://cakeml.org/) a verified implementation of an ML in HOL4
- [holpy](https://github.com/bzhan/holpy) <https://arxiv.org/abs/1905.05970>

HOL4
<https://kth-step.github.io/itppv-course/>

# HOL light

- [wikpedia](https://en.wikipedia.org/wiki/HOL_Light)
- [Harrison's page](https://www.cl.cam.ac.uk/~jrh13/hol-light/)
- [tutorial](https://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf) quite good
- [Thomas Hale - Formal Proof article](https://cmartinez.web.wesleyan.edu/documents/FP.pdf) Succinct summary of axioms
- [](https://crypto.stanford.edu/~blynn/compiler/Hol.html)

<https://github.com/jrh13/hol-light/>
[harrison itp school](https://itp-school-2023.github.io/slides/slides_jrh_part1.pdf)
<https://cakeml.org/candle> candle hol light on cakeml

botstrap <https://github.com/jrh13/hol-light/blob/master/hol.ml>

kernel <https://github.com/jrh13/hol-light/blob/master/fusion.ml>

```bash
echo "
;question, can I write re
(declare-const b Bool)
(assert (distinct b b))
(check-sat)" > /tmp/test.smt2
vampire /tmp/test.smt2
```

#

# Isabelle

<https://slawekk.wordpress.com/> isar mathlib <https://isarmathlib.org/index.html>

<https://www.cl.cam.ac.uk/teaching/2122/L21/materials.html> pauleson course

metis <https://www.gilith.com/software/metis/>
metitarski. Resolution + Qepcad

FOLP first order logic with proofs. Interesting idea

ZF

typedecl
judgement
axiomatization

argo smt solver. hmm

HOL
nonstadnard reals

<https://isabelle.in.tum.de/library/>

paulson's blog slaps <https://lawrencecpaulson.github.io/>
<https://github.com/lawrencecpaulson/lawrencecpaulson.github.io/tree/main/Isabelle-Examples>

semantic search <https://behemoth.cl.cam.ac.uk/search/> serapis

isabelle isar reference manual is useful

src/HOL directory
impp mutablle nominal nonstandard-analysis

[from lcf to isabelle](https://dl.acm.org/doi/pdf/10.1007/s00165-019-00492-1)
[sel4](https://sel4.systems/) - verified microkernel

[](https://www.cse.unsw.edu.au/~cs4161/)

Metalevel is a syntax for describing inference rules

- `!! x.`     \Lambda Universal variables at the meta level. enables Schema
- `==>` is inference rule
- `%x.` is meta level lambda?

[typeclasses vs locales](https://twitter.com/LawrPaulson/status/1506603400267505669?s=20&t=y2AWW1GNA8vyxsWqTXmKPQ)

[Sledgehammer: some history, some tips](https://lawrencecpaulson.github.io/2022/04/13/Sledgehammer.html)
[isabelle cookboook: programming in ML](https://web.cs.wpi.edu/~dd/resources_isabelle/isabelle_programming.urban.pdf)
[more isabelle ML programming notes](https://www.lri.fr/~wolff/papers/other/TR_my_commented_isabelle.pdf)

[Baby examples](https://lawrencecpaulson.github.io/2022/05/04/baby-examples.html)

Isabelle => vs --> vs ==>
=> is the function type
--> is implication
==> is meta implication, which is something like a sequent |-

```isabelle
{% include_relative isabelle/play.thy %}
```

Querying

```isabelle
{% include_relative isabelle/isabelleplay.thy %}
```

The isabelle command line <https://stackoverflow.com/questions/48939929/verify-an-isabelle-proof-from-the-command-line>
`isabelle build`
`isabelle process -T`

Isabelle system manual <https://isabelle.in.tum.de/doc/system.pdf>

ROOT files

```
Usage: isabelle process [OPTIONS]

  Options are:
    -T THEORY    load theory
    -d DIR       include session directory
    -e ML_EXPR   evaluate ML expression on startup
    -f ML_FILE   evaluate ML file on startup
    -l NAME      logic session name (default ISABELLE_LOGIC="HOL")
    -m MODE      add print mode for output
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Run the raw Isabelle ML process in batch mode.
```

```bash
#isabelle process -e "1 + 1" # eval ML expr
#isabelle process -e ’Thy_Info.get_theory "Main"’
#isabelle process -T /home/philip/Documents/philzook58.github.io/_notes/Languages/isabelle/play
cat <<'EOF' > /tmp/test.thy
theory test
imports Main
begin
lemma "1 + 1 = 2" by simp
value "3::int"
(* print_commands *)
(* defining a datatype *)
datatype 'a  MyList = MyNil | MyCons 'a "'a MyList"
(* defining a function *)
fun mylength :: "'a MyList \<Rightarrow> nat" where
  "mylength MyNil = 0"
| "mylength (MyCons x xs) = 1 + mylength xs"
end
EOF
isabelle process -T /tmp/test

```

```bash
isabelle console
```

<https://github.com/isabelle-prover/mirror-isabelle>

PURE is the isabelle framework. The core rules are resolution?
<https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Pure/thm.ML>

```
(*Resolution: exactly one resolvent must be produced*)
fun tha RSN (i, thb) =
  (case Seq.chop 2 (biresolution NONE false [(false, tha)] i thb) of
    ([th], _) => solve_constraints th
  | ([], _) => raise THM ("RSN: no unifiers", i, [tha, thb])
  | _ => raise THM ("RSN: multiple unifiers", i, [tha, thb]));

(*Resolution: P \<Longrightarrow> Q, Q \<Longrightarrow> R gives P \<Longrightarrow> R*)
fun tha RS thb = tha RSN (1,thb);
```

Higher order unfication <https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Pure/unify.ML>

simplifier <https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Pure/simplifier.ML>
<https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Pure/raw_simplifier.ML>

Example simple HOL def <https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Pure/Examples/Higher_Order_Logic.thy>

<https://github.com/isabelle-prover/mirror-isabelle/tree/master/src/Provers> provers.
