unsafe inductive FreeM (f : Type -> Type) (a : Type) where
  | Pure : a -> FreeM f a
  | Free : f (FreeM f a) -> FreeM f a
--deriving instance Functor (Free f)

instance (Functor f) : Functor (FreeM f) where
  map := fun g x =>
    match x with
    | FreeM.Pure a => FreeM.Pure (g a)
    | FreeM.Free fa => FreeM.Free (map (map g) fa)
