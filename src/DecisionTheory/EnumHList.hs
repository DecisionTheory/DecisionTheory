{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TypeOperators #-}
module DecisionTheory.EnumHList where

import Data.HList.HList (HList (..))
import Data.Kind (Constraint, Type)

type EnumerateHList :: [Type] -> Constraint
class EnumerateHList (ts :: [Type]) where
  enumerateHList :: [HList ts]

instance EnumerateHList '[] where
  enumerateHList = []

instance (Bounded t, Enum t, EnumerateHList ts) => EnumerateHList (t : ts) where
  enumerateHList = do
    h <- enumFrom (minBound @t)
    ts <- enumerateHList @ts
    pure (h `HCons` ts)
