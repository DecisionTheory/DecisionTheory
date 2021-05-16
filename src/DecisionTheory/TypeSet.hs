{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module DecisionTheory.TypeSet
  ( TypeSet,
    AllUnique,
    CheckAllUnique,
    NotElem,
    If,
    IfLazy,
    Elem,
    CheckNotElem,
    Disjoint,
    CheckDisjoint,
    Union,
    SetDifference,
    type (++),
    SubsetOf,
  )
where

import Data.Kind (Constraint, Type)
import GHC.TypeLits (ErrorMessage (..), TypeError)

type Solved :: () -> Constraint
class Solved unit

instance Solved '()

type Failed :: ErrorMessage -> () -> Constraint
class Failed errorMessage unit

instance (TypeError errorMessage) => Failed errorMessage '()

type (++) :: [Type] -> [Type] -> [Type]
type family ts ++ us where
  '[] ++ us = us
  (t : ts) ++ us = t : (ts ++ us)

type IfLazy :: Bool -> (() -> k) -> (() -> k) -> k
type family IfLazy cond then_ else_ where
  IfLazy True then_ _ = then_ '()
  IfLazy False _ else_ = else_ '()

type If :: Bool -> k -> k -> k
type family If cond then_ else_ where
  If True then_ _ = then_
  If False _ else_ = else_

type Elem :: Type -> [Type] -> Bool
type family Elem t ts where
  Elem _ '[] = False
  Elem t (t : _) = True
  Elem t (_ : ts) = Elem t ts

type CheckElem t ts onFail = IfLazy (Elem t ts) Solved onFail

type CheckNotElem t ts onFail = IfLazy (Elem t ts) onFail Solved

type NotElem :: ErrorMessage -> Type -> [Type] -> Constraint
class NotElem onFail t ts

instance (CheckNotElem t ts (Failed onFail)) => NotElem onFail t ts

type CheckAllUnique :: [Type] -> ErrorMessage -> Constraint
type family CheckAllUnique types onFail where
  CheckAllUnique '[] _ = ()
  CheckAllUnique (t : ts) onFail = (NotElem onFail t ts, CheckAllUnique ts onFail)

type AllUnique :: ErrorMessage -> [Type] -> Constraint
class AllUnique onFail ts

instance (CheckAllUnique ts onFail) => AllUnique onFail ts

type DuplicatesInTypeList :: [Type] -> ErrorMessage

type DuplicatesInTypeList ts =
  Text "Duplicated types in type list:"
    :$$: ShowType ts

type TypeSet :: [Type] -> Constraint
class (AllUnique (DuplicatesInTypeList ts) ts) => TypeSet ts

instance (AllUnique (DuplicatesInTypeList ts) ts) => TypeSet ts

type CheckDisjoint :: [Type] -> [Type] -> ErrorMessage -> Constraint

type CheckDisjoint ts us onFail = CheckAllUnique (ts ++ us) onFail

class (TypeSet ts, TypeSet us) => Disjoint onFail ts us

instance (TypeSet ts, TypeSet us, CheckDisjoint ts us onFail) => Disjoint onFail ts us

type IntoSet :: [Type] -> [Type] -> [Type]
type family IntoSet ts us where
  IntoSet ts '[] = ts
  IntoSet ts (u : us) =
    If
      (Elem u ts)
      (IntoSet ts us)
      (IntoSet (u : ts) us)

type Union :: [Type] -> [Type] -> [Type]

type Union ts us = IntoSet '[] (ts ++ us)

type SetDifference :: [Type] -> [Type] -> [Type]
type family SetDifference ts us where
  SetDifference '[] _ = '[]
  SetDifference (t : ts) us =
    If
      (Elem t us)
      (SetDifference ts us)
      (t : SetDifference ts us)

type family ts `SubsetOf` us where
  ts `SubsetOf` us = SetDifference ts us ~ '[]
