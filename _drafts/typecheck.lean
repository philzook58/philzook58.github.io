

-- Do Pierce style typecheckers
-- Use lean to get good syntax?

-- Or literally reuse the Lean.Expr type but for different type systems.


/-
Aexpr typechecker.

What if we never go to lambdas but put in all the features we can?
Typeclass inference
Dependent types
subtyping
generics / parametric / system F


go thgrough pfpl


Lambda: The Ultimate pain in the ass

currying: allowed or no?


https://www.cis.upenn.edu/~bcpierce/tapl/

-/


namespace TArith

inductive term where
  | tmtrue
  | tmfalse
  | tmif (t1 t2 t3 : term)
  | tmzero
  | tmsucc (t1 : term)
  | tmpred (t1 : term)
  | tmiszero (t1 : term)

inductive ty where
  | tybool
  | tynat


def eval1 : term -> term
| .tmif .tmtrue t2 t3 => t2
| .tmif .tmfalse t2 t3 => t3
| .tmif t1 t2 t3 => .tmif (eval1 t1) t2 t3
| .tmsucc t1 => .tmsucc (eval1 t1)



end TArith
