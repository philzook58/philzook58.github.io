{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}

newtype LVec number basis = LVec {runLVec :: [(number,basis)]}

vadd = (++)
smult s = LVec . fmap (\(n,b) -> (s * n, b)) . runLVec

instance Functor (LVec n) where
	fmap f = LVec . fmap (\(n,b) -> (n, f b)) . runLVec 

directProd :: forall a b f. (LVec a f, LVec b f) -> LVec (a,b) f
directProd = undefined
directSum :: forall a b f. (LVec a f, LVec b f) -> LVec (Either a b) f
directSum = undefined

type LinOp number basis = basis -> LVec number basis

instance (Num n) => Applicative (LVec n) where
   pure e1 = LVec [(1, e1)]
   f <*> x =  LVec $ concatMap (\(n, f') -> fmap (\(n', a) -> (n*n', f' a)) l1) f1  where
   			  l1 = runLVec x
   			  f1 = runLVec f

instance (Num n) => Monad (LVec n) where
   return e1 = LVec [(1, e1)]
   x >>= f =  LVec $ concatMap (\(n,b)-> runLVec (smult n (f b))) $ runLVec x

type Test = forall a. [a]

head' :: (forall a. a) -> ()
head' _ = ()

--delayed :: forall a. (a -> Int, a)
delayed = (const 3, undefined)

data Delayed b = forall a. Delayed (a -> b) a

doit :: (forall a. (a -> b, a)) -> b
doit (x,y) = x y

doit' :: Delayed b -> b
doit' (Delayed f x) = f x

