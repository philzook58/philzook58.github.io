
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

instance : HDiv Vec3 Float Vec3 where
  hDiv v s := ⟨v.x / s, v.y / s, v.z / s⟩

-- dot product
def dot (a b : Vec3) : Float :=
  a.x * b.x + a.y * b.y + a.z * b.z

def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

def hadamard (a b : Vec3) : Vec3 :=
  ⟨a.x * b.x, a.y * b.y, a.z * b.z⟩

def norm (v : Vec3) : Float :=
  Float.sqrt (dot v v)

def normalize (v : Vec3) : Vec3 :=
  let n := norm v
  if n == 0 then v else v / n

def clamp01 (x : Float) : Float :=
  if x < 0 then 0 else if x > 1 then 1 else x

def floatToByte (x : Float) : UInt8 :=
  let y := clamp01 x
  UInt8.ofNat (UInt64.toNat (Float.toUInt64 (y * 255.0)))

def colorToPixel (c : Vec3) : Pixel :=
  (floatToByte c.x, floatToByte c.y, floatToByte c.z)

-- a x b = - b x a. Need reals to prove. Hmm.


structure Sphere where
  center : Vec3
  radius : Float
  color : Vec3
deriving Repr, Inhabited, BEq

structure Ray where
  origin : Vec3
  direction : Vec3
deriving Repr, Inhabited, BEq

structure Light where
  position : Vec3
  color : Vec3
deriving Repr, Inhabited, BEq


-- async
-- iter
-- new enumeration syntax ...

#eval Lean.versionString


def Sphere.intersect (s : Sphere) (r : Ray) : Option (Float × Vec3) :=
  let oc := r.origin - s.center
  let a := dot r.direction r.direction
  let b := 2.0 * dot oc r.direction
  let c := dot oc oc - s.radius * s.radius
  let discriminant := b * b - 4 * a * c
  if discriminant < 0 then
    none
  else
    let t1 := (-b - Float.sqrt discriminant) / (2.0 * a)
    let t2 := (-b + Float.sqrt discriminant) / (2.0 * a)
    if t1 > 0 then
      let pos := r.origin + t1 * r.direction
      let norm := (pos - s.center) / s.radius
      some (t1, norm)
    else if t2 > 0 then
      let pos := r.origin + t2 * r.direction
      let norm := (pos - s.center) / s.radius
      some (t2, norm)
    else
      none

def lights : List Light :=
  [ { position := ⟨50, 50, 0⟩, color := ⟨1, 0.1, 0.4⟩ } ]

def objects : List Sphere :=
  [ { center := ⟨0, 10, 50⟩, radius := 10, color := ⟨1, 0.1, 0.1⟩ }
  , { center := ⟨0, 0, 100⟩, radius := 10, color := ⟨0.1, 1, 0.1⟩ }
  , { center := ⟨-20, 0, 100⟩, radius := 10, color := ⟨0.1, 0.1, 1⟩ } ]

def render (N : Nat) : Image := Id.run do
  let mut img : Image := Array.replicate N (Array.replicate N (0, 0, 0))
  let half := Float.ofNat (N / 2)
  let nFloat := Float.ofNat N
  for i in [0:N] do
    for j in [0:N] do
      let dir := ⟨(Float.ofNat i - half) / nFloat, (Float.ofNat j - half) / nFloat, 1⟩
      let ray := Ray.mk ⟨0, 0, 0⟩ dir
      let mut closestT : Float := 1.0e30
      let mut pixelColor : Pixel := (135, 206, 235) -- sky color
      for obj in objects do
        match obj.intersect ray with
        | some (t, norm) =>
          if t < closestT then
            closestT := t
            let mut col : Vec3 := ⟨0, 0, 0⟩
            let hitPos := ray.origin + t * ray.direction
            for light in lights do
              let lightDir := normalize (light.position - hitPos)
              let diff := dot norm lightDir
              if diff > 0 then
                col := col + diff * (hadamard obj.color light.color)
            pixelColor := colorToPixel col
        | none => ()
      img := img.modify i fun row => row.set! j pixelColor
  img

#check render
/-
#eval  do
  for i in 1...3 do
    IO.println i

-/
