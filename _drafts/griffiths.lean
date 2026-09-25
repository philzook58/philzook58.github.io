import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finsupp.Basic
/-

What is the somewhat rigorous version of griffiths

Separation of variables.
Must a wavefunction be fourier transformable?
psi^2 must be normalizaable (square integrable)

Scattering to t=-inf and t=inf

distributions vs functions
operators as algebraic entitites

Laplace and Fourier picture
psi = F[psik] is an ansatz as much a seperatin of vairables is

Or apply F to both sides of equation

1/r potentials
1. diverge
2. are slow decaying.


Taylor scattering book chapter 1
isometric operators
operator limits
operators and inverses


Mixed continuous and discrete spectrums

https://pubs.ams.org/ebooks/gsm/099/

lectures on quantum for mathematical - fadeev
https://pubs.ams.org/ebooks/stml/047/

https://link.springer.com/book/10.1007/978-1-4614-7116-5?page=2#toc
qunatum theory for mathematicicans





-/




open scoped BigOperators
/-

Articles
https://www.scottaaronson.com/democritus/lec9.html

https://physicstoday.aip.org/features/heisenberg-and-the-early-days-of-quantum-mechanics - Bloch 1976
https://physicstoday.aip.org/features/is-the-moon-there-when-nobody-looks-reality-and-the-quantum-theory-1760212151991 memrmin 1985

Bohm, Dirac book

probability of wavefunctions.

It has the floppiness / non canonical problem. Hmm.
Like a list vs a set. Too much data
Density matrix is quotient

How I introduce the schorodinger equation
https://arxiv.org/pdf/2010.15589


Inverse problems
Bayesian methods

Why is it ocmplex?
Why is it a scalar?

Integral forms
psi = G psi0
psi = psi0 + int_t H psi


the analytic signal
https://en.wikipedia.org/wiki/Analytic_signal
phasors

Are complex hilbert spaces better than real hilbert spaces?

Plotting wavefunctions
complex spirals
superposed 1d
using colors for phase
-/

namespace contprob

/-
integ p(x) = 1
Expect f p := integ -inf

def dropx t := 1/2 * g * t^2
def veldrpo t := deriv dropx



-/
end contprob



/-
Yeah Q vs R. Q is computable has many nice properties

Finite support.
Even if we consider it to be over the Integers/Nats
An explicit parametrized space of Fin 3 is maybe smart, albeit non obvious

I am beginning to see the wisdom of the frst approach

-/
def observations : Multiset ℤ :=
  {0, 2, 2, 2, 3, 3, 3, 3}

-- example : {0,2,3} = ({3,0,2} : MultiSet ℤ) := by



#check Finsupp
#check finset% Finset.range 2
abbrev Histogram := ℤ →₀ ℚ
#eval Finsupp.onFinset (Finset.range 2) (fun x => x)



namespace Listy
def people : List (ℚ × ℚ) :=
  [(0,1), (2,3), (3,4)]

def total : ℚ := (people.map fun row => row.2).sum
#eval total
example : total = 8 := by
  norm_num [total, people]

end Listy




namespace FinStyle
abbrev Outcome := Fin 3

-- huh vector notation
def value : Outcome → ℚ := ![0, 2, 3]
def count : Outcome → ℚ := ![1, 3, 4]
def total := ∑ i, count i
#check Finset.sum
#check Finset
#eval total
def prob (i : Outcome) : ℚ := (count i) / total

end FinStyle
-- #check ENNReal
/-import Mathlib.Probability
import Mathlib.Reals -- derivative
import Mathlib.Complex
import Mathlib.Sums
/-



-/

def people := [
  (0, 1),
  (2, 3),
  (3, 4),
]

def prob n : R = lookup n / sum people

theorem check_sum : sum_n prob n = 1

def avg prob := sum_n n * prob n
def variance2 prob := sum_n prob n (n - avg prob )^2
def variance prb := sqrt (variance2 prob)

def hbar : Real := 1.05 * 10^-24
def h := hbar / 2 * pi

def schrod psi := I * hbar / 2 ∂_t psi(x) = - hbar ^2 / 2 / m * ∂_x
 ψ(x) + V(x) * ψ(x)

-/
