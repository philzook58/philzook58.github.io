
/-
#eval "Hello world!"
#eval 1 + 1

#eval IO.FS.writeFile "/tmp/hello.txt" "Hello, Lean!"

#eval do
  let s <- IO.FS.readFile "/tmp/hello.txt"
  IO.println s
-/

-- type Image = list[list[int]]

/-
#print Image


partial def ppm_of_image (img : Image) : String :=
  let height := img.size
  let width := (img[0]!).size
  let header := "P3\n" ++ toString width ++ " " ++ toString height ++ "\n255\n"
  header
-/

--#eval ppm_of_image #[#[(0, 0, 0), (255, 255, 255), (128, 128, 128)]]
-- #set_option trace.

abbrev Pixel := UInt8 × UInt8 × UInt8
abbrev Image : Type := Array (Array Pixel)

partial def doit (N : Nat) := Id.run do
  let mut img : Image := Array.replicate N (Array.replicate N (0, 0, 0))
  for i in [0:N] do
    for j in [0:N] do
          if ((i : Int)- N/2)^2 + ((j : Int) - N/2)^2 < (N/4)^2 -- This Int conversion sucks. But I'd have a similar problem in many other languages
          then
            --let newrow := (img[i]!).set! j (0, 0, 255)
            img := img.modify i fun row => row.set! j (0, 0, 255)
            --img.set! i newrow
  return img


--#eval doit 500
-- import _drafts.ray
#eval doit 10
--#check Repr
--def main := println! (doit 10)
def main : IO Unit := pure ()

structure Vec3 where
  x : Float
  y : Float
  z : Float
deriving Repr, Inhabited, BEq

instance : Add Vec3 where
  add a b := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

instance : Sub Vec3 where
  sub a b := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

instance : HMul Float Vec3 Vec3 where
  hMul s v := ⟨s * v.x, s * v.y, s * v.z⟩

-- dot product
def dot (a b : Vec3) : Float :=
  a.x * b.x + a.y * b.y + a.z * b.z

def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

-- a x b = - b x a. Need reals to prove. Hmm.


structure Sphere where
  center : Vec3
  radius : Float
  color : Pixel
deriving Repr, Inhabited, BEq

structure Ray where
  origin : Vec3
  direction : Vec3
deriving Repr, Inhabited, BEq


-- async
-- iter
-- new enumeration syntax ...

#eval Lean.versionString

#eval  do
  for i in 1...3 do
    IO.println i
