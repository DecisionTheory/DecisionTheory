{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, MonoLocalBinds, ConstraintKinds #-}

module DecisionTheory.TypedDecisionTheory (dt, edt, cdt, fdt ) where

  import qualified DecisionTheory.Base as B
  import qualified DecisionTheory.DecisionTheory as DT
  import qualified DecisionTheory.Graph as UG
  import qualified DecisionTheory.TypedGraph as TG

  import Data.Data
  import Data.Maybe (fromJust)

  type Compilable a v p g gi go = (TG.Stateable a, TG.Labelable a, TG.Stateable v, TG.Labelable v, TG.Compilable (TG.Guard p) [UG.Guard], TG.Compilable (TG.E gi go (TG.Graph g)) (UG.Graph UG.Stochastic))
  type Decidable a v p pi g gi go = (Compilable a v p g gi go, TG.AllInputsSatisfied (TG.Difference pi go))

  dt :: forall a v p pi po g gi go. (Decidable a v p pi g gi go) => DT.Hypothesis -> TG.E pi po (TG.Guard p) -> (v -> DT.Utility) -> TG.E gi go (TG.Graph g) -> (a, DT.Utility)
  dt h gs uf g = result $ DT.dt h guards search graph
    where guards        = TG.compile gs
          search        = DT.Search (uf . fromJust . TG.ofState) (TG.toLabel (undefined :: a)) (TG.toLabel (undefined :: v))
          graph         = TG.compile g
          result        :: (B.State, DT.Utility) -> (a, DT.Utility)
          result (s, u) = (fromJust $ TG.ofState s, u)


  edt :: Decidable a v p pi g gi go => TG.E pi po (TG.Guard p) -> (v -> DT.Utility) -> TG.E gi go (TG.Graph g) -> (a, DT.Utility)
  edt = dt DT.condition

  cdt :: Decidable a v p pi g gi go => TG.E pi po (TG.Guard p) -> (v -> DT.Utility) -> TG.E gi go (TG.Graph g) -> (a, DT.Utility)
  cdt = dt DT.intervene

  fdt :: Decidable a v p pi g gi go => B.Label -> TG.E pi po (TG.Guard p) -> (v -> DT.Utility) -> TG.E gi go (TG.Graph g) -> (a, DT.Utility)
  fdt = dt . DT.counterFactualize
