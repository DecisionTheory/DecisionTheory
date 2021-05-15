{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module DecisionTheory.TypedGraph2 where

import Data.HList.HList (HList (..))
import Data.Kind (Type)
import DecisionTheory.TypeSet (Disjoint, NotElem, SetDifference, TypeSet, Union, type (++))
import GHC.TypeLits (ErrorMessage (..))

data SimulationType = Deterministic | Stochastic

type family CombineSimulationTypes (st1 :: SimulationType) (st2 :: SimulationType) where
  CombineSimulationTypes 'Deterministic 'Deterministic = 'Deterministic
  CombineSimulationTypes _ _ = 'Stochastic

type Always :: Type -> Type
newtype Always outcome = Always outcome

type Distribution :: Type -> Type
newtype Distribution outcome = Distribution [(Word, outcome)]

type Choice :: [Type] -> Type -> Type
newtype Choice inputs outcome = Choice (TypeSet inputs => HList inputs -> outcome)

type Node :: SimulationType -> [Type] -> Type -> Type
data Node simType inputs outcome where
  NAlways :: Always outcome -> Node simType '[] outcome
  NDistribution :: Distribution outcome -> Node 'Stochastic '[] outcome
  NChoice :: Choice inputs outcome -> Node simType inputs outcome

type NodeOutcomeMayNotBeOneOfInputs :: [Type] -> Type -> ErrorMessage

type NodeOutcomeMayNotBeOneOfInputs inputs outcome =
  'Text "A Node's outcome may not be among its inputs."
    ':$$: 'Text "Inputs:"
    ':$$: 'ShowType inputs
    ':$$: 'Text "Outcome:"
    ':$$: 'ShowType outcome

type NoDuplicatedOutcomesInGraph :: [Type] -> [Type] -> ErrorMessage

type NoDuplicatedOutcomesInGraph outcomes1 outcomes2 =
  'Text "Two nodes in the same graph cannot have the same outcome type."
    ':$$: 'Text "In this case, you are trying to concat the two graphs with "
    ':<>: 'Text "overlapping outcome sets, which would lead to duplicated outcomes."
    ':$$: 'Text "Outcomes of the left-hand graph:"
    ':$$: 'ShowType outcomes1
    ':$$: 'Text "Outcomes of the right-hand graph:"
    ':$$: 'ShowType outcomes2

type OutcomeShouldPrecedeInput leftHandInputs rightHandOutcomes =
  'Text "To avoid circular graphs, they must be constructed such that outcomes "
    ':<>: 'Text "are defined before (i.e. to the left) of inputs. You are trying to "
    ':<>: 'Text "concatenate two graphs in a way that violates this, because the "
    ':<>: 'Text "left-hand graph expects inputs that match outcomes of the right-hand "
    ':<>: 'Text "graph."
    ':$$: 'Text "Inputs of the left-hand graph:"
    ':$$: 'ShowType leftHandInputs
    ':$$: 'Text "Outcomes of right-hand graph:"
    ':$$: 'ShowType rightHandOutcomes

type ValidGraphNode inputs outcome =
  NotElem (NodeOutcomeMayNotBeOneOfInputs inputs outcome) outcome inputs

type MayConcatGraphs inputs1 outcomes1 inputs2 outcomes2 =
  ( Disjoint (NoDuplicatedOutcomesInGraph outcomes1 outcomes2) outcomes1 outcomes2,
    Disjoint (OutcomeShouldPrecedeInput inputs1 outcomes2) outcomes2 inputs1
  )

type Graph :: SimulationType -> [Type] -> [Type] -> Type
data Graph simType inputs outcomes where
  GNode ::
    ValidGraphNode inputs outcome =>
    Node simType inputs outcome ->
    Graph simType inputs '[outcome]
  GConcat ::
    MayConcatGraphs inputs1 outcomes1 inputs2 outcomes2 =>
    Graph simType1 inputs1 outcomes1 ->
    Graph simType2 inputs2 outcomes2 ->
    Graph
      (CombineSimulationTypes simType1 simType2)
      (Union inputs1 (SetDifference inputs2 outcomes1))
      (outcomes1 ++ outcomes2)

always :: outcome -> Graph simType '[] '[outcome]
always = GNode . NAlways . Always

distribution :: [(Word, outcome)] -> Graph 'Stochastic '[] '[outcome]
distribution = GNode . NDistribution . Distribution

choose :: ValidGraphNode inputs outcome => (HList inputs -> outcome) -> Graph simType inputs '[outcome]
choose = GNode . NChoice . Choice

(%=) :: b -> a -> (a, b)
v %= weight = (weight, v)

(.*.) ::
  MayConcatGraphs inputs1 outcomes1 inputs2 outcomes2 =>
  Graph simType1 inputs1 outcomes1 ->
  Graph simType2 inputs2 outcomes2 ->
  Graph
    (CombineSimulationTypes simType1 simType2)
    (Union inputs1 (SetDifference inputs2 outcomes1))
    (outcomes1 ++ outcomes2)
(.*.) = GConcat

infixr 5 .*.

--------------------------------------------------------------------------------
---- Compiler

class Compile t where
  type Compiled t :: Type

--------------------------------------------------------------------------------
---- Example: Xor Blackmail

data Infestation = Termites | NoTermites deriving (Eq, Show)

data Predisposition = Payer | Refuser deriving (Eq, Show)

data Prediction = Skeptic | Gullible deriving (Eq, Show)

data Observation = Letter | NoLetter deriving (Eq, Show)

data Action = Pay | Refuse deriving (Eq, Show)

newtype Value = Value Int deriving (Eq, Show)

xorBlackmail ::
  Graph
    'Stochastic
    '[]
    '[ Infestation,
       Predisposition,
       Prediction,
       Observation,
       Action,
       Value
     ]
xorBlackmail =
  distribution
    [ Termites %= 50,
      NoTermites %= 50
    ]
    .*. distribution
      [ Payer %= 50,
        Refuser %= 50
      ]
    .*. choose
      ( \case
          Termites `HCons` Payer `HCons` HNil -> Skeptic
          Termites `HCons` Refuser `HCons` HNil -> Gullible
          NoTermites `HCons` Payer `HCons` HNil -> Gullible
          NoTermites `HCons` Refuser `HCons` HNil -> Gullible
      )
    .*. choose
      ( \case
          (Gullible `HCons` HNil) -> Letter
          (Skeptic `HCons` HNil) -> NoLetter
      )
    .*. choose
      ( \case
          (Payer `HCons` HNil) -> Pay
          (Refuser `HCons` HNil) -> Refuse
      )
    .*. choose
      ( \case
          Termites `HCons` Pay `HCons` HNil -> (Value $ -1001000)
          Termites `HCons` Refuse `HCons` HNil -> (Value $ -1000000)
          NoTermites `HCons` Pay `HCons` HNil -> (Value $ -1000)
          NoTermites `HCons` Refuse `HCons` HNil -> (Value 0)
      )
