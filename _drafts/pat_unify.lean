/-

https://www.cs.mcgill.ca/~bpientka/papers/unif-sigma-final.pdf
Higher-Order Dynamic Pattern Unification for Dependent Types and Records


Semantics of pattern unification
https://raw.githubusercontent.com/amblafont/unification/master/draft.pdf

Jason Reed

https://saizan.github.io/papers/pattern-unif.pdf
A Categorical Perspective on Pattern Unification - Vezossi and Abel

Miller mixed prefix
https://hal.science/hal-05600175 https://www.lix.polytechnique.fr/~dale/papers/jsc92.pdf

Krishnaswami question
https://cstheory.stackexchange.com/questions/57126/modern-presentation-of-first-order-unification-under-a-mixed-prefix/57132#57132

Abel says it well
M x y = t  is solved uniquely by M = lambda x y. t

M x y = N y z  must mean only y is used. The slotted trick.

M x y -> U y
N y z ->  U y

https://cstheory.stackexchange.com/questions/57126/modern-presentation-of-first-order-unification-under-a-mixed-prefix/57132#57132

pfenning notes
https://www.cs.cmu.edu/~fp/courses/atp/handouts/atp.pdf
"unification logic"

-- https://dl.acm.org/doi/10.1145/2784731.2784751 a unification algorithm for coq


https://lean-lang.org/doc/api/Lean/MetavarContext.html
-/
import Lean
import Philib
open Lean Meta

#check MetavarContext


#py r#"
from dataclasses import dataclass
type MetaId = int

@dataclass
class App:
  decl : Decl
  args : list["Term"]

type Term = App | MetaId
@dataclass
class Decl:
  sort : Optional[Term] # or further terms?

@dataclass
class MetavarContext:
  depth : int
  decls : dict[MetaId, Decl]
  assigns : dict[MetaId, Term] # optional


"# ()

abbrev MetaId := Nat
structure MyMetavarContex where
  depth : Nat -- depth though?
  decls : Std.HashMap MetaId String
