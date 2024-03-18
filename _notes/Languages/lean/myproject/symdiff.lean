import Matlhb.Data.Real.basic

inductive expr : Type where
  | const : ℕ -> expr
  | var : String -> expr
  | add : expr -> expr -> expr
  | mul : expr -> expr -> expr
  | pow : expr -> ℕ -> expr
  | sin : expr -> expr
  | cos : expr -> expr
  | exp : expr -> expr

def interp (env : String -> ℝ): expr -> ℝ
  | .const n => n
  | .var x => env x
  | .add f g => interp env f + interp env g
  | .mul f g => interp env f * interp env g
  | .pow f n => (interp env f) ^ n
  | .sin f => sin (interp env f)
  | .cos f => cos (interp env f)
  | .exp f => exp (interp env f)

def diff (x : String) : expr -> expr
  | .const _ => .const 0
  | .var y => if x == y then .const 1 else .const 0
  | .add f g => add (diff x f) (diff x g)
  | .mul f g => add (mul f (diff x g)) (mul g (diff x f))
  | .pow f g => mul (mul g (pow f (add g (const (-1))))) (diff x f)
  | .sin f => mul (cos f) (diff x f)
  | .cos f => mul (const (-1)) (mul (sin f) (diff x f))
  | .exp f => mul (exp f) (diff x f)
-- | heaviside x => .dirac x


def const_fold : expr -> expr
  | .add (.const n) (.const m) => .const (n + m)
  | .mul (.const n) (.const m) => .const (n * m)
  | .pow (.const n) m => .const (n ^ m)
  | .sin (.const n) => .const (sin n)
  | .cos (.const n) => .const (cos n)
  | .exp (.const n) => .const (exp n)
  | e => e

def simplify1 : expr -> expr
  | .add (.const 0) f => f
  | .add f (.const 0) => f
  | .mul (.const 0) f => .const 0
  | .mul f (.const 0) => .const 0
  | .mul (.const 1) f =>  f
  | .mul f (.const 1) =>  f
  | .pow f 0 => .const 1
  | .pow f 1 => f
  | .pow (.const 1) f => .const 1
  | .pow f (.const 1) => f
  | .mul (.add x y) z => add (mul x z) (mul y z)
  | .mul x (.add y z) => add (mul x y) (mul x z)
  | .sin (.const 0) => .const 0
  | .cos (.const 0) => .const 1
  | .exp (.const 0) => .const 1
  | e => e




-- def fourier : funexpr -> funexpr
