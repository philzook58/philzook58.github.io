-- shallow embdding of logic is a usefuk thing to know about
-- []()

inductive Prop' where
  | Atom : String -> Prop' 
  | Impl : Prop' -> Prop'  -> Prop' 
  | Not : Prop'  -> Prop' 
  | False : Prop'

inductive Provable : List Prop' -> Prop' -> Prop where -- [P] |- Q
  --| Modus : forall a b, Provable h(Impl a b) -> Provable a -> Provable b
  -- | Axiom : forall a, Provable a -> Provable a
  | Refl : forall hyps a, Provable (a :: hyps) a
  | Weaken : forall hyps a b,  Provable hyps b -> Provable (a :: hyps) b
  -- | NotI : forall hyps a, Provable (a :: hyps) Prop'.False -> Provable hyps (Prop'.Not a)
  -- | NotE : forall hyps a, Provable hyps (Prop'.Not a) -> ProaProvable hyps Prop'.False
  | ImplI : forall hyps a b, Provable (a :: hyps) b -> Provable hyps (Prop'.Impl a b)
  | ImplE : forall hyps a b, Provable hyps (Prop'.Impl a b) -> Provable hyps a -> Provable hyps b
  | FalseE : forall hyps a, Provable hyps Prop'.False -> Provable hyps a

-- Using lean typeclasses as automation for our proof datatype
instance Inhabited (Provable )
class BackChain
class Invert

-- cody claims that first order logic using explicit names isn't that bad

inductive Term where
  | Var : String -> Term
  | Const : String -> List Term -> Term

inductive FOL where
  | Atom : Term -> FOL
  | Impl : FOL -> FOL -> FOL

