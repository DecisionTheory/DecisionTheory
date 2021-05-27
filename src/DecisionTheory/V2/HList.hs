{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

module DecisionTheory.V2.HList
  ( EnumerateHList (..),
    HList (..),
    HTuple,
    hToTuple,
    hFromTuple,
    hAsTuple,
    hToSingle,
    hFromSingle,
    hAsSingle,
  )
where

import Data.Kind (Constraint, Type)

-- definition copied from HList package

type HList :: [Type] -> Type
data family HList ts

data instance HList '[] = HNil

data instance HList (x ': xs) = x ::: HList xs

infixr 5 :::

deriving instance Eq (HList '[])

deriving instance (Eq x, Eq (HList xs)) => Eq (HList (x ': xs))

deriving instance Ord (HList '[])

deriving instance (Ord x, Ord (HList xs)) => Ord (HList (x ': xs))

class HTuple v t | v -> t, t -> v where
  hToTuple :: HList v -> t
  hFromTuple :: t -> HList v

hAsTuple :: HTuple v b => (b -> c) -> HList v -> c
hAsTuple f = f . hToTuple

hAsSingle :: (b -> c) -> HList '[b] -> c
hAsSingle f = f . hToSingle

hToSingle :: HList '[x] -> x
hToSingle (a ::: HNil) = a

hFromSingle :: x -> HList '[x]
hFromSingle = (::: HNil)

instance HTuple '[] () where
  hToTuple HNil = ()
  hFromTuple () = HNil

instance HTuple '[a, b] (a, b) where
  hToTuple (a ::: b ::: HNil) = (a, b)
  hFromTuple (a, b) = a ::: b ::: HNil

instance HTuple '[a, b, c] (a, b, c) where
  hToTuple (a ::: b ::: c ::: HNil) = (a, b, c)
  hFromTuple (a, b, c) = a ::: b ::: c ::: HNil

instance HTuple '[a, b, c, d] (a, b, c, d) where
  hToTuple (a ::: b ::: c ::: d ::: HNil) = (a, b, c, d)
  hFromTuple (a, b, c, d) = a ::: b ::: c ::: d ::: HNil

instance HTuple '[a, b, c, d, e] (a, b, c, d, e) where
  hToTuple (a ::: b ::: c ::: d ::: e ::: HNil) = (a, b, c, d, e)
  hFromTuple (a, b, c, d, e) = a ::: b ::: c ::: d ::: e ::: HNil

instance HTuple '[a, b, c, d, e, f] (a, b, c, d, e, f) where
  hToTuple (a ::: b ::: c ::: d ::: e ::: f ::: HNil) = (a, b, c, d, e, f)
  hFromTuple (a, b, c, d, e, f) = a ::: b ::: c ::: d ::: e ::: f ::: HNil

type EnumerateHList :: [Type] -> Constraint
class EnumerateHList (ts :: [Type]) where
  enumerateHList :: [HList ts]

instance EnumerateHList '[] where
  enumerateHList = []

instance (Bounded t, Enum t) => EnumerateHList '[t] where
  enumerateHList = fmap (::: HNil) (enumFrom (minBound @t))

instance (Bounded t, Enum t, EnumerateHList (u : ts)) => EnumerateHList (t : u : ts) where
  enumerateHList = do
    h <- enumFrom (minBound @t)
    ts <- enumerateHList @(u : ts)
    pure (h ::: ts)
