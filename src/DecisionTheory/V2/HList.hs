{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

module DecisionTheory.V2.HList (EnumerateHList (..), HList (..)) where

import Data.HList.HList (HList (..))
import Data.Kind (Constraint, Type)

type EnumerateHList :: [Type] -> Constraint
class EnumerateHList (ts :: [Type]) where
  enumerateHList :: [HList ts]

instance EnumerateHList '[] where
  enumerateHList = []

instance (Bounded t, Enum t) => EnumerateHList '[t] where
  enumerateHList = fmap (`HCons` HNil) (enumFrom (minBound @t))

instance (Bounded t, Enum t, EnumerateHList (u : ts)) => EnumerateHList (t : u : ts) where
  enumerateHList = do
    h <- enumFrom (minBound @t)
    ts <- enumerateHList @(u : ts)
    pure (h `HCons` ts)
