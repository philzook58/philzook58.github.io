import Std.Data.HashMap
abbrev EId := Nat

structure ENode where
  f : String
  args : Array EId -- Probably not Int right?
deriving Repr, DecidableEq, Hashable


#eval ({f := "f", args := #[1,2,3]} : ENode)


structure EGraph where
  uf : Array EId
  memo : Std.HashMap ENode EId
deriving Repr, Inhabited


def makeset : StateM EGraph EId :=
  do
  let eg <- get
  let id := eg.uf.size
  set {eg with uf := eg.uf.push id}
  return id

#eval makeset.run default

#eval (do
  let _ <- makeset
  let _ <- makeset
  let _ <- makeset).run default

partial def find (id : Nat) : StateM EGraph EId := do
  let eg <- get
  let p := eg.uf[id]!
  if p == id then pure id else find p

partial def union (a b : Nat) : StateM EGraph Unit := do
  let a <- find a
  let b <- find b
  if a == b
    then pure ()
    else  do
      let eg <- get
      set {eg with uf := eg.uf.set! a b}

partial def is_equiv (a b : Nat) : StateM EGraph Bool := do
  let a <- find a
  let b <- find b
  return a == b

#eval (do
  let a <- makeset
  let b <- makeset
  let c <- makeset
  union a b
  union b c
  pure <| (<- find a) == (<- find b)
).run default


def add_node (node : ENode) : StateM EGraph EId := do
  -- todo canonicalize
  let eg <- get
  match eg.memo[node]? with
  | some id => pure id
  | none => (do
      let id <- makeset
      modify fun eg => {eg with memo := eg.memo.insert node id}
      pure id)


def const (name : String) : StateM EGraph EId :=
  add_node {f := name, args := #[]}

def app1 (name : String) (x : EId) :=
  add_node {f := name, args := #[x]}

def canonicalize_node  (node : ENode) : StateM EGraph ENode :=
  return {node with args := <-node.args.mapM find}

#eval (do
add_node {f := "foo", args := #[]}
).run default

#eval (do
  let a <- const "a"
  let b <- const "b"
  let c <- const "c"
  union a b
  union b c
  is_equiv a c
).run default


-- not right.
partial def rebuild : StateM EGraph Unit := do
  let eg <- get
  let memo := eg.memo
  modify (fun eg => {eg with memo := default})
  let l := memo.size
  for (node, id) in memo do
    let node <- canonicalize_node node
    -- wrong?
    let _ <- eg.memo[node]?.mapM (fun id1 => union id id1)
    modify (fun eg => {eg with memo := eg.memo.insert node id})
  if (<-get).memo.size == l then
    return ()
  else
    rebuild

#eval (do
  let a <- const "a"
  let b <- const "b"
  let fa <- app1 "f" a
  let fb <- app1 "f" b
  let ffa <- app1 "f" fa
  let ffb <- app1 "f" fb
  union a b
  rebuild
  is_equiv fa fb
).run default



/-
|>.
unexpand
-/
