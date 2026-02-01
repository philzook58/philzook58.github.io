{-# LANGUAGE GHC2024 #-}

{- title: Haskell examples
   date: 2024-06-10
   draft: true
   tags: [haskell, programming]
-}
-- https://github.com/diku-dk/ap-e2024-pub
{-
Comment
-}
foo :: Int
foo = 3

bar [] = 42
bar (x : xs) = x + bar xs

data Choices = C1 | C2

frob C1 = 1
frob C2 = 2

data AExpr = Num Int | Add AExpr AExpr

eval (Num n) = n
eval (Add a1 a2) = eval a1 + eval a2

-- >>> 1 + 2
-- 3

{-
So what would make sense? The course made an APL.
That's intigruing

-}
