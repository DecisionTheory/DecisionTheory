{-# LANGUAGE
    AllowAmbiguousTypes
  , ConstraintKinds
  , DataKinds
  , FlexibleContexts
  , KindSignatures
  , MonoLocalBinds
  , ScopedTypeVariables
  #-}

module DecisionTheory.TypedDecisionTheory
  ( Solutions
  , dt
  , edt
  , cdt
  , fdt
  , ValidInterventionNode
  ) where

  import Data.Data
  import Data.Typeable
  import Data.Maybe (fromJust)

  import qualified DecisionTheory.Base as B
  import qualified DecisionTheory.DecisionTheory as DT
  import qualified DecisionTheory.Graph as UG
  import qualified DecisionTheory.TypedGraph as TG

  type Compilable a v p    g gi go = ( TG.Stateable a
                                     , TG.Labelable a
                                     , TG.Stateable v
                                     , TG.Labelable v
                                     , TG.Compilable (TG.Guard p) [UG.Guard]
                                     , TG.Compilable (TG.E gi go (TG.Graph g)) (UG.Graph UG.Stochastic)
                                     )
  type Decidable  a v p pi g gi go = ( Compilable a v p g gi go
                                     , TG.AllInputsSatisfied (TG.Difference pi go)
                                     )
  type Solutions a = [(a, DT.Utility)]

  dt :: forall a v p pi po g gi go.
          Decidable a v p pi g gi go
          => DT.Hypothesis
          -> TG.E pi po (TG.Guard p)
          -> (v -> DT.Utility)
          -> TG.E gi go (TG.Graph g)
          -> Solutions a
  dt h gs uf g = map result $ DT.dt h guards search graph
    where guards        = TG.compile gs
          search        = DT.Search (uf . fromJust . TG.ofState) (TG.toLabel (undefined :: a)) (TG.toLabel (undefined :: v))
          graph         = TG.compile g
          result        :: (B.State, DT.Utility) -> (a, DT.Utility)
          result (s, u) = (fromJust $ TG.ofState s, u)


  edt :: forall a v p pi po g gi go.
           Decidable a v p pi g gi go
           => TG.E pi po (TG.Guard p)
           -> (v -> DT.Utility)
           -> TG.E gi go (TG.Graph g)
           -> Solutions a
  edt = dt DT.condition

  cdt :: forall a v p pi po g gi go.
           Decidable a v p pi g gi go
           => TG.E pi po (TG.Guard p)
           -> (v -> DT.Utility)
           -> TG.E gi go (TG.Graph g)
           -> Solutions a
  cdt = dt DT.intervene

  class ValidInterventionNode (i :: [*])
  instance ValidInterventionNode '[]

  fdt :: forall t a v p pi po g gi go.
           ( Decidable a v p pi g gi go
           , TG.Labelable t
           , ValidInterventionNode (TG.Difference '[t] go)
           )
           => TG.E pi po (TG.Guard p)
           -> (v -> DT.Utility)
           -> TG.E gi go (TG.Graph g)
           -> Solutions a
  fdt = dt $ DT.counterFactualize $ TG.toLabel $ (undefined :: t)
