{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module DecisionTheory.V2.Stringify
  ( AsLabel (..),
    AsState (..),
    Datally (..),
    Showly (..),
  )
where

import Data.Data (Data, Proxy (..))
import Data.Data qualified as Data
import DecisionTheory.Base (Label (..), State (..))
import Text.Read (readMaybe)

class AsState a where
  toState :: a -> State
  fromState :: State -> Maybe a

class AsLabel a where
  toLabel :: Label

newtype Datally a = Datally a

instance Data a => AsState (Datally a) where
  toState (Datally a) = State . Data.showConstr . Data.toConstr $ a
  fromState (State s) = Datally . Data.fromConstr <$> Data.readConstr (Data.dataTypeOf (undefined :: a)) s

instance Data a => AsLabel (Datally a) where
  toLabel = Label . Data.tyConName . Data.typeRepTyCon . Data.typeRep $ Proxy @a

newtype Showly a = Showly a

instance (Show a, Read a) => AsState (Showly a) where
  toState (Showly a) = State . show $ a
  fromState (State s) = Showly <$> readMaybe s
