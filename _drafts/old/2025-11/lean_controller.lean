import Init.Data.Array.Zip
import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
#eval "hellow"


--def Controller := (State, Obs) -> Action

namespace Foolin

def add_float x y := (x + y : Float)
#eval add_float 1.0 2.0
#eval Float.cos 4.0

-- Vectors? Scilean, sure.
-- Something less invasive?
structure State where
  x : Float
  v : Float



def free_part (s : State) (dt : Float) : State :=
  { x := s.x + s.v * dt , v := s.v }

def state0 : State := { x := 0.0, v := 1.0 }

#eval free_part state0 3.0

/-
Cody brings up two good ideas:
- prove stability at balancing point
- polymorphic over float and reals instead of using floats vs reals
-/


def sho (s : State) (dt : Float) : State :=
  let k := 1.0
  let m := 1.0
  let a := -k / m * s.x
  { x := s.x + s.v * dt, v := s.v + a * dt }

end Foolin


#check Array.size_map

structure Vec (n : Nat) where
  data : Array Float
  sized : n = data.size

def myadd {n : Nat} (v w : Vec n) : Vec n :=
  let data := v.data.zip w.data |>.map (λ (x, y) => x + y)
  {
    data := data,
    sized := by
      simp [data]
      cases v <;> cases w <;> grind

  }

/-
  def myadd {n : Nat} {v : Array Float // } : Vec n :=
  let data := v.data.zip w.data |>.map (λ (x, y) => x + y)
  {
    data := data,
    sized := by
      simp [data]
      cases v <;> cases w <;> grind

  }
-/



-- bare metal? Compiling to C still has dec ref.
-- Requires runtime
-- That balancing robot. How'd they do it. Pi? Linux runtime?




def control x dx :=

/-
def gym_wrap f := do
  IO.Process.ChildProcess.withProcess
    { cmd := "python3"
      args := #[IO.FS.Path.mkString "gym_wrap.py"]
      stdout := IO.Process.Stdout.inherit
      stderr := IO.Process.Stderr.inherit }
    (λ _ => pure ())
-/
