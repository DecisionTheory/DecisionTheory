{-# LANGUAGE
    ViewPatterns
  , GeneralizedNewtypeDeriving
  #-}
module DecisionTheory.DecisionTheory
  ( Utility (..)
  , Search (..)
  , stdSearch
  , Hypothesis
  , Solutions
  , condition
  , dt
  , edt
  , intervene
  , cdt
  , counterFactualize
  , fdt
  )
  where

  import qualified Data.List as L
  import qualified Data.Maybe as M

  import Data.Ord (comparing)
  import Data.Foldable (toList)

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import DecisionTheory.Graph

  newtype Utility = Utility Float deriving (Num, Fractional, Eq, Ord, Show, Read)

  data Search = Search (State -> Utility) Label Label

  stdSearch :: Search
  stdSearch = Search uf (Label "Action") (Label "Value")
    where uf (State s) = Utility $ read s

  type Hypothesis = (Guard -> Endo [Probability (Graph Deterministic)])
  type Solution = (State, Utility)
  type Solutions = [Solution]


  unstableDT :: Foldable f => Hypothesis -> f Guard -> Search -> Graph Stochastic -> Solution
  unstableDT hypothesis gs (Search uf a o) g = L.maximumBy (comparing snd) . map expectation $ hypotheticals
    where hypotheticals :: [(State, [Probability (Graph Deterministic)])]
          hypotheticals = M.mapMaybe (hypothetical.conclusion) $ choices a $ branches g
          hypothetical (_, []) = Nothing
          hypothetical c       = Just c
          conclusion v = (v, hypothesis (Guard a v) possibleBranches)
          possibleBranches = foldl (flip condition) (branches g) gs
          expectedValue :: Probability (Graph Deterministic) -> Utility
          expectedValue (unProbability -> (g, v)) = ((* fromRational v) . uf) $ M.fromJust $ find o g
          expectation :: (State, [Probability (Graph Deterministic)]) -> Solution
          expectation (v, ps) = (v, sum $ map expectedValue ps)

  dt :: Foldable f => Hypothesis -> f Guard -> Search -> Graph Stochastic -> Solutions
  dt hypothesis gs s@(Search _ a _) g = let s = solve gs
                                         in reverse $ loop s []
    where loop :: Solution -> Solutions -> Solutions
          loop s@(v, _) ss = let s' = solve (guard v)
                             in if s' `elem` ss then ss else loop s' (s':ss)
          guard :: State -> [Guard]
          guard v = (Guard a v : toList gs)
          solve :: Foldable f => f Guard -> Solution
          solve gs = unstableDT hypothesis gs s g

  edt :: Foldable f => f Guard -> Search -> Graph Stochastic -> Solutions
  edt = dt condition

  cdt :: [Guard] -> Search -> Graph Stochastic -> Solutions
  cdt = dt intervene

  fdt :: Foldable f => Label -> f Guard -> Search -> Graph Stochastic -> Solutions
  fdt = dt . counterFactualize

  condition :: Hypothesis
  condition (Guard l v) = normalize . filter branchSatisfiesGuard
    where branchSatisfiesGuard (probabilityElement -> g) = Just v == find l g

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
