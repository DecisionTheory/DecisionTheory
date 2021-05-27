{-# LANGUAGE
    ViewPatterns
  , GeneralizedNewtypeDeriving
  #-}
{-# LANGUAGE DataKinds #-}
module DecisionTheory.DecisionTheory
  ( Utility (..)
  , Search (..)
  , stdSearch
  , Hypothesis
  , Decision (..)
  , Solution
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

  type Hypothesis = (Guard -> Endo [Branch])
  data Decision a = Decision State a deriving (Eq, Show)
  instance Ord a => Ord (Decision a) where
    Decision s1 a1 <= Decision s2 a2 = (a1, s1) <= (a2, s2)
  instance Functor Decision where
    fmap f (Decision s a) = Decision s (f a)
  decide :: (State -> a) -> (State -> Decision a)
  decide f s = Decision s (f s)

  consequence :: Decision a -> a
  consequence (Decision _ a) = a

  type Solution = Decision Utility
  type Solutions = [Solution]

  unstableDT :: Foldable f => Hypothesis -> f Guard -> Search -> Graph 'Stochastic -> Solution
  unstableDT hypothesis gs search@(Search uf a o) g = decision $ hypotheticals $ possibleActions
    where possibleActions = choices a $ branches g
          possibleBranches = foldl (flip condition) (branches g) gs
          hypotheticals :: [State] -> [Decision [Branch]]
          hypotheticals = filter (not.null.consequence) . map (decide simulation)
          simulation :: State -> [Branch]
          simulation s = hypothesis (Guard a s) possibleBranches
          decision :: [Decision [Branch]] -> Solution
          decision = L.maximum . map (fmap (sum . map (branchUtility search)))

  branchUtility :: Search -> Branch -> Utility
  branchUtility search = expectedValue . fmap (outcomeUtility search)

  outcomeUtility :: Search -> Graph 'Deterministic -> Utility
  outcomeUtility (Search uf _ o) = uf . M.fromJust . find o

  expectedValue :: Probability Utility -> Utility
  expectedValue (unProbability -> (a, p)) = a * fromRational p

  dt :: Foldable f => Hypothesis -> f Guard -> Search -> Graph 'Stochastic -> Solutions
  dt hypothesis gs s@(Search _ a _) g = let s = solve gs
                                         in reverse $ loop s []
    where loop :: Solution -> Solutions -> Solutions
          loop s@(Decision v _) ss = let s' = solve (guard v)
                                     in if s' `elem` ss then ss else loop s' (s':ss)
          guard :: State -> [Guard]
          guard v = (Guard a v : toList gs)
          solve :: Foldable f => f Guard -> Solution
          solve gs = unstableDT hypothesis gs s g

  edt :: Foldable f => f Guard -> Search -> Graph 'Stochastic -> Solutions
  edt = dt condition

  cdt :: [Guard] -> Search -> Graph 'Stochastic -> Solutions
  cdt = dt intervene

  fdt :: Foldable f => Label -> f Guard -> Search -> Graph 'Stochastic -> Solutions
  fdt = dt . counterFactualize

  condition :: Hypothesis
  condition (Guard l v) = normalize . filter branchSatisfiesGuard
    where branchSatisfiesGuard (probabilityElement -> g) = Just v == find l g

  intervene :: Hypothesis
  intervene (Guard l v) = normalize . map (mapBranches intervention)
    where intervention :: Endo (Labeled (Node 'Deterministic))
          intervention ln@(Labeled l' _) | l == l'   = Labeled l (Always v)
                                         | otherwise = ln


  {-- We start with a uniform prior over the possible predispositions, then compute the possible universes
      for each possible intervention on predisposition, and finally condition that distribution on the
      choice of action we're evaluating.
   --}
  counterFactualize :: Label -> Hypothesis
  counterFactualize l g ps = condition g $ normalize $ concatMap (\s -> intervene (Guard l s) ps) $ choices l ps
