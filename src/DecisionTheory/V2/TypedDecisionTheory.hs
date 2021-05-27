{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module DecisionTheory.V2.TypedDecisionTheory where

import Data.Kind (Constraint, Type)
import Data.Maybe (fromJust)
import qualified DecisionTheory.Base as B
import qualified DecisionTheory.DecisionTheory as DT
import qualified DecisionTheory.Graph as UG
import DecisionTheory.V2.Stringify (AsLabel (..), AsState (..))
import DecisionTheory.V2.TypeSet (Elem)
import qualified DecisionTheory.V2.TypedGraph as TG
import GHC.TypeLits (ErrorMessage (..), TypeError)

type NoOpenInputs :: [Type] -> Constraint
type family NoOpenInputs openInputs where
  NoOpenInputs '[] = ()
  NoOpenInputs openInputs =
    TypeError
      ( 'Text "Cannot decide on a graph with open inputs. This graph is missing the following nodes:"
          ':$$: 'ShowType openInputs
      )

type Decidable :: TG.GraphShape -> [Type] -> Type -> Type -> UG.SimulationType -> Constraint

type Decidable shape guards action result simType =
  ( TG.Compile (TG.Guards guards),
    TG.Compiled (TG.Guards guards) ~ [UG.Guard],
    TG.Compile (TG.Graph simType shape),
    TG.Compiled (TG.Graph simType shape) ~ UG.Graph simType,
    AsLabel action,
    AsState action,
    AsLabel result,
    AsState result,
    NoOpenInputs (TG.OpenInputs shape)
  )

type Solutions a = [(a, DT.Utility)]

type DecisionTheory shape guards action result =
  TG.Guards guards ->
  (result -> DT.Utility) ->
  TG.Graph UG.Stochastic shape ->
  Solutions action

dt ::
  forall shape (guards :: [Type]) action result simType.
  Decidable shape guards action result 'UG.Stochastic =>
  DT.Hypothesis ->
  DecisionTheory shape guards action result
dt h gs uf g = map result $ DT.dt h guards search graph
  where
    guards = TG.compile gs
    search = DT.Search (uf . fromJust . fromState) (toLabel @action) (toLabel @result)
    graph = TG.compile g
    result :: DT.Solution -> (action, DT.Utility)
    result (DT.Decision s u) = (fromJust $ fromState s, u)

edt ::
  forall shape (guards :: [Type]) action result simType.
  Decidable shape guards action result 'UG.Stochastic =>
  DecisionTheory shape guards action result
edt = dt DT.condition

cdt ::
  forall shape (guards :: [Type]) action result simType.
  Decidable shape guards action result 'UG.Stochastic =>
  DecisionTheory shape guards action result
cdt = dt DT.intervene

type ValidInterventionNode :: Type -> Bool -> Constraint
type family ValidInterventionNode interventionNode isAnOutcome where
  ValidInterventionNode _ True = ()
  ValidInterventionNode interventionNode False =
    TypeError
      ( 'Text "Can only intervene on nodes that exist in a graph, but"
          ':$$: 'ShowType interventionNode
          ':$$: 'Text "does not."
      )

fdt ::
  forall interventionNode shape (guards :: [Type]) action result simType.
  ( Decidable shape guards action result 'UG.Stochastic,
    AsLabel interventionNode,
    ValidInterventionNode interventionNode (interventionNode `Elem` TG.AllOutcomes shape)
  ) =>
  DecisionTheory shape guards action result
fdt = dt $ DT.counterFactualize $ toLabel @interventionNode
