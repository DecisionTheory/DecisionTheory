{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}

module DecisionTheory.V2.TypedGraph
  ( module DecisionTheory.V2.TypedGraph,
    HList (..),
  )
where

import Data.Data (Data, Proxy (Proxy))
import Data.Data qualified as Data
import Data.Kind (Constraint, Type)
import DecisionTheory.Base (Label (..), Labeled (..), State (..))
import DecisionTheory.Graph qualified as U
import DecisionTheory.Probability (Probability, (%=))
import DecisionTheory.V2.HList (EnumerateHList (..), HList (..))
import DecisionTheory.V2.TypeSet (Disjoint, NotElem, SetDifference, TypeSet, Union)
import GHC.TypeLits (ErrorMessage (..))
import Text.Read (readMaybe)

type Always :: Type -> Type
newtype Always outcome = Always outcome

type Distribution :: Type -> Type
newtype Distribution outcome = Distribution [Probability outcome]

type Choice :: [Type] -> Type -> Type
newtype Choice inputs outcome = Choice (TypeSet inputs => HList inputs -> outcome)

type Node :: U.SimulationType -> [Type] -> Type -> Type
data Node simType inputs outcome where
  NAlways :: Always outcome -> Node simType '[] outcome
  NDistribution :: Distribution outcome -> Node 'U.Stochastic '[] outcome
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

type AllOutcomes :: GraphShape -> [Type]
type family AllOutcomes shape where
  AllOutcomes ('N _ outcome) = '[outcome]
  AllOutcomes (left ':*: right) = Union (AllOutcomes left) (AllOutcomes right)

type OpenInputs :: GraphShape -> [Type]
type family OpenInputs shape where
  OpenInputs ('N inputs _) = inputs
  OpenInputs (left ':*: right) = Union (OpenInputs left) (SetDifference (OpenInputs right) (AllOutcomes left))

type MayConcatGraphs inputs1 outcomes1 inputs2 outcomes2 =
  ( Disjoint (NoDuplicatedOutcomesInGraph outcomes1 outcomes2) outcomes1 outcomes2,
    Disjoint (OutcomeShouldPrecedeInput inputs1 outcomes2) outcomes2 inputs1
  )

data GraphShape
  = N [Type] Type
  | (:*:) GraphShape GraphShape

type Graph :: U.SimulationType -> GraphShape -> Type
data Graph simType shape where
  GNode ::
    ValidGraphNode requiredInputs outcome =>
    Node simType requiredInputs outcome ->
    Graph simType ('N requiredInputs outcome)
  GConcat ::
    MayConcatGraphs (OpenInputs shape1) (AllOutcomes shape1) (OpenInputs shape2) (AllOutcomes shape2) =>
    Graph simType shape1 ->
    Graph simType shape2 ->
    Graph simType (shape1 ':*: shape2)

always :: outcome -> Graph simType ('N '[] outcome)
always = GNode . NAlways . Always

distribution :: [Probability outcome] -> Graph 'U.Stochastic ('N '[] outcome)
distribution = GNode . NDistribution . Distribution

choose :: ValidGraphNode inputs outcome => (HList inputs -> outcome) -> Graph simType ('N inputs outcome)
choose = GNode . NChoice . Choice

(.*.) ::
  MayConcatGraphs (OpenInputs shape1) (AllOutcomes shape1) (OpenInputs shape2) (AllOutcomes shape2) =>
  Graph simType shape1 ->
  Graph simType shape2 ->
  Graph simType (shape1 ':*: shape2)
(.*.) = GConcat

infixr 5 .*.

--------------------------------------------------------------------------------
---- Compiler

class Compile t where
  type Compiled t :: Type
  compile :: t -> Compiled t

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

type CompilableInputs :: [Type] -> Constraint

type CompilableInputs inputs =
  ( TypeSet inputs,
    EnumerateHList inputs,
    Compile (HList inputs),
    Compiled (HList inputs) ~ [U.Guard]
  )

type CompilableOutcome outcome = (AsState outcome, AsLabel outcome)

instance
  ( outcomes ~ '[outcome],
    CompilableOutcome outcome,
    CompilableInputs inputs
  ) =>
  Compile (Graph simType ('N inputs outcome))
  where
  type Compiled (Graph simType ('N inputs outcome)) = U.Graph simType
  compile (GNode node) =
    U.Graph [Labeled (toLabel @outcome) (compile node)]

instance
  ( Compile (Graph simType shapeLeft),
    Compiled (Graph simType shapeLeft) ~ U.Graph simType,
    Compile (Graph simType shapeRight),
    Compiled (Graph simType shapeRight) ~ U.Graph simType
  ) =>
  Compile (Graph simType (shapeLeft ':*: shapeRight))
  where
  type Compiled (Graph simType (shapeLeft ':*: shapeRight)) = U.Graph simType
  compile (GConcat gleft gright) =
    U.Graph ((U.unGraph . compile) gleft ++ (U.unGraph . compile) gright)

instance
  ( CompilableInputs inputs,
    CompilableOutcome outcome
  ) =>
  Compile (Node simType inputs outcome)
  where
  type Compiled (Node simType inputs outcome) = U.Node simType
  compile (NAlways a) = compileAlways a
  compile (NDistribution a) = compileDistribution a
  compile (NChoice a) = compileChoice a

compileAlways :: AsState a => Always a -> U.Node simType
compileAlways (Always outcome) = U.Always (toState outcome)

compileDistribution :: AsState a => Distribution a -> U.Node 'U.Stochastic
compileDistribution (Distribution weightedOutcomes) =
  U.Distribution (fmap (fmap toState) weightedOutcomes)

compileChoice ::
  forall inputs outcome simType.
  (CompilableInputs inputs, CompilableOutcome outcome) =>
  Choice inputs outcome ->
  U.Node simType
compileChoice (Choice choiceFn) = U.Conditional (toClause <$> enumerateHList @inputs)
  where
    toClause params = U.Clause (compile params) (toState $ choiceFn params)

instance Compile (HList '[]) where
  type Compiled (HList '[]) = [U.Guard]
  compile _ = []

instance
  ( AsLabel t,
    AsState t,
    Compile (HList ts),
    Compiled (HList ts) ~ [U.Guard]
  ) =>
  Compile (HList (t : ts))
  where
  type Compiled (HList (t : ts)) = [U.Guard]
  compile (a `HCons` as) = U.Guard (toLabel @t) (toState a) : compile as

--------------------------------------------------------------------------------
---- Example: Xor Blackmail

data Infestation = Termites | NoTermites
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Infestation)

data Predisposition = Payer | Refuser
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Predisposition)

data Prediction = Skeptic | Gullible
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Prediction)

data Observation = Letter | NoLetter
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Observation)

data Action = Pay | Refuse
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Action)

newtype Value = Value Int
  deriving stock (Eq, Show, Data)
  deriving newtype (Enum, Bounded)
  deriving (AsLabel) via (Datally Value)
  deriving (AsState) via (Showly Int)

xorBlackmail ::
  Graph
    'U.Stochastic
    ( 'N '[] Infestation
        ':*: ( 'N '[] Predisposition
                 ':*: ( 'N '[Infestation, Predisposition] Prediction
                          ':*: ( 'N '[Prediction] Observation
                                   ':*: ( 'N '[Predisposition] Action
                                            ':*: 'N '[Infestation, Action] Value
                                        )
                               )
                      )
             )
    )
xorBlackmail =
  distribution
    [ Termites %= 0.5,
      NoTermites %= 0.5
    ]
    .*. distribution
      [ Payer %= 0.5,
        Refuser %= 0.5
      ]
    .*. choose
      ( \case
          Termites `HCons` Payer `HCons` HNil -> Skeptic
          Termites `HCons` Refuser `HCons` HNil -> Gullible
          NoTermites `HCons` Payer `HCons` HNil -> Gullible
          NoTermites `HCons` Refuser `HCons` HNil -> Skeptic
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
