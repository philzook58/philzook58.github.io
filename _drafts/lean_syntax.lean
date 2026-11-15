


section preterm
inductive term where
  | x : term
  | f : term -> term
  | bool : term

inductive judgement where
  | has_type : term -> term -> judgement



end preterm


section well_scoped

inductive thin : Nat -> Nat -> Type where



end well_scoped


section algebra

structure monoid





end algebra
