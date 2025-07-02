-- Lean as a jupyter notebook


-- How to use lean like python

-- https://docs.python.org/3/tutorial/controlflow.html
-- https://learnxinyminutes.com/python/

-- ooh sorry lean doesn't have operator chaining? Not a modern language like python
#eval 1 < 2 && 2 < 3
-- #eval 1 < 2 < 3
-- of course you could macro it in


-- type and isinstance. Hmm.
-- https://leanprover-community.github.io/mathlib4_docs/Init/Dynamic.html#TypeName


-- This is some haskelly stuff.
-- https://hackage.haskell.org/package/base-4.21.0.0/docs/Data-Dynamic.html

unsafe instance : TypeName Nat := TypeName.mk Nat `Nat
-- #eval TypeName.mk Int `Int
-- #eval TypeName.typeName Int
#eval Dynamic.mk 3 |>.get? Nat

structure Foo where
deriving TypeName, Repr

#eval TypeName.typeName Foo
#eval Dynamic.mk Foo.mk |>.get? Foo

-- But is this really isinstance?
-- We'd want a hiearchy of
-- class InstanceOf T T

-- Maybe a better match is coercions


/-

x = int(input("Please enter an integer: "))
Please enter an integer: 42
if x < 0:
    x = 0
    print('Negative changed to zero')
elif x == 0:
    print('Zero')
elif x == 1:
    print('Single')
else:
    print('More')


Use macros to put full python syntax sugar?
But really what is even left?

-/

def checkneg (x : Nat) : IO Unit := do
  if x < 0 then
    IO.println "Negative changed to zero"
  else if x == 0 then
    IO.println "Zero"
  else if x == 1 then
    IO.println "Single"
  else
    IO.println "More"
#eval checkneg 42


/-

for n in range(2, 10):
    for x in range(2, n):
        if n % x == 0:
            print(n, 'equals', x, '*', n//x)
            break
    else:
        # loop fell through without finding a factor
        print(n, 'is a prime number')

-/

#eval
for n in [2:10] do
  let mut found := false
  for x in [2:n] do
    if n % x == 0 then
      IO.println s!"{n} equals {x} * {n / x}"
      found := true
      break
  if !found then
    -- loop fell through without finding a factor
    IO.println s!"{n} is a prime number"
/-
 else
    -- loop fell through without finding a factor
    IO.println s!"{n} is a prime number"
    -/

/-
pairs = [(1, 'one'), (2, 'two'), (3, 'three'), (4, 'four')]
pairs.sort(key=lambda pair: pair[1])
-/
def pairs := [(1, "one"), (2, "two"), (3, "three"), (4, "four")]

-- #eval pairs.sort (fun a b => a.2 < b.2)
