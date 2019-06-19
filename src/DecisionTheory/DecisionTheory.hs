module DecisionTheory.DecisionTheory where

  import qualified Data.List as L
  import qualified Data.Maybe as M

  import Data.Ord (comparing)
  import Data.Foldable (toList)

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import DecisionTheory.Graph

  -- FIXME newtype
  type Utility = Float

  data Search = Search (State -> Utility) Label Label
  stdSearch :: Search
  stdSearch = Search uf (Label "Action") (Label "Value")
    where uf (State s) = read s

  type Hypothesis = (Guard -> Endo [Probability (Graph Deterministic)])

  unstableDT :: Foldable t => Hypothesis -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  unstableDT hypothesis gs (Search uf a o) g = L.maximumBy (comparing snd) . map expectation $ hypotheticals
    where hypotheticals :: [(State, [Probability (Graph Deterministic)])]
          hypotheticals = M.mapMaybe (hypothetical.conclusion) $ choices a $ branches g
          hypothetical (_, []) = Nothing
          hypothetical c       = Just c
          conclusion v = (v, hypothesis (Guard a v) possibleBranches)
          possibleBranches = foldl (flip condition) (branches g) gs
          expectedValue :: Probability (Graph Deterministic) -> Utility
          expectedValue (Probability g v) = ((* fromRational v) . uf) $ M.fromJust $ find o g
          expectation :: (State, [Probability (Graph Deterministic)]) -> (State, Utility)
          expectation (v, ps) = (v, sum $ map expectedValue ps)

  dt :: Foldable t => Hypothesis -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  dt hypothesis gs s@(Search _ a _) g | fst decision == fst dominance = decision
                                      | otherwise                     = error ("OMG! " ++ show dominance ++ " /= " ++ show decision)
    where decision :: (State, Utility)
          decision = unstableDT hypothesis (Guard a (fst dominance) : toList gs) s g
          dominance :: (State, Utility)
          dominance = unstableDT hypothesis gs s g

  edt :: Foldable t => t Guard -> Search -> Graph Stochastic -> (State, Utility)
  edt = dt condition

  cdt :: [Guard] -> Search -> Graph Stochastic -> (State, Utility)
  cdt = dt intervene

  fdt :: Foldable t => Label -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  fdt = dt . counterFactualize

  condition :: Hypothesis
  condition (Guard l v) = normalize . filter branchSatisfiesGuard
    where branchSatisfiesGuard (Probability g _) = Just v == find l g

  intervene :: Hypothesis
  intervene (Guard l v) = normalize . map (mapBranches intervention)
    where intervention :: Endo (Labeled (Node Deterministic))
          intervention ln@(Labeled l' _) | l == l'   = Labeled l (Always v)
                                         | otherwise = ln


  {-- We start with a uniform prior over the possible predispositions, then compute the possible universes
      for each possible intervention on predisposition, and finally condition that distribution on the
      choice of action we're evaluating.
   --}
  counterFactualize :: Label -> Hypothesis
  counterFactualize l g ps = condition g $ normalize $ concatMap (\s -> intervene (Guard l s) ps) $ choices l ps
