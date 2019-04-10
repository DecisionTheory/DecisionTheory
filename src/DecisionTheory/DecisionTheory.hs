module DecisionTheory.DecisionTheory where

  import qualified Data.List as L
  import qualified Data.Maybe as M

  import Data.Ord (comparing)
  import Data.Foldable (toList)
  import Data.Function (on)

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import DecisionTheory.Graph

  type Utility = Float

  data Search = Search (State -> Utility) Label Label
  stdSearch = (Search uf (Label "action") (Label "value"))
    where uf (State s) = read s

  dt :: Foldable t => (Guard -> Endo [Probability (Graph Deterministic)]) -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  dt hypothesis gs (Search uf a o) g = L.maximumBy (comparing snd) $ map expectation $ hypotheticals
    where hypotheticals :: [(State, [Probability (Graph Deterministic)])]
          hypotheticals = M.catMaybes $ map (hypothetical.conclusion) $ choices a $ branches g
          hypothetical (v, []) = Nothing
          hypothetical c       = Just c
          conclusion v = (v, hypothesis (Guard a v) possibleBranches)
          possibleBranches = foldl (flip condition) (branches g) gs
          expectedValue :: Probability (Graph Deterministic) -> Utility
          expectedValue (Probability g v) = ((* (fromRational v)) . uf) $ M.fromJust $ find o g
          expectation :: (State, [Probability (Graph Deterministic)]) -> (State, Utility)
          expectation (v, ps) = (v, sum $ map expectedValue ps)

  stableDT :: Foldable t => (Guard -> Endo [Probability (Graph Deterministic)]) -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  stableDT hypothesis gs s@(Search _ a _) g | fst decision == fst dominance = decision
                                            | otherwise                     = error ("OMG! " ++ (show dominance) ++ " /= " ++ (show decision))
    where decision :: (State, Utility)
          decision = dt hypothesis ((Guard a (fst dominance)): toList gs) s g
          dominance :: (State, Utility)
          dominance = dt hypothesis gs s g

  edt :: Foldable t => t Guard -> Search -> Graph Stochastic -> (State, Utility)
  edt = stableDT condition

  cdt :: [Guard] -> Search -> Graph Stochastic -> (State, Utility)
  cdt = stableDT intervene

  fdt :: Foldable t => Label -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  fdt = stableDT . counterFactualize

  condition :: Guard -> Endo [Probability (Graph Deterministic)]
  condition (Guard l v) = normalize . filter branchSatisfiesGuard
    where branchSatisfiesGuard (Probability g _) = Just v == find l g

  intervene :: Guard -> Endo [Probability (Graph Deterministic)]
  intervene (Guard l v) = normalize . map (mapBranches intervention)
    where intervention :: Endo (Labeled (Node Deterministic))
          intervention ln@(Labeled l' _) | l == l'   = Labeled l (Always v)
                                         | otherwise = ln


  {-- We start with a uniform prior over the possible predispositions, then compute the possible universes
      for each possible intervention on predisposition, and finally condition that distribution on the
      choice of action we're evaluating.
   --}
  counterFactualize :: Label -> Guard -> Endo [Probability (Graph Deterministic)]
  counterFactualize l g ps = condition g $ normalize $ concatMap (\s -> intervene (Guard l s) ps) $ choices l ps

  weighted :: [Probability (State, Utility)] -> [(State, Utility)]
  weighted = map weight . L.groupBy ((==) `on` name) . L.sortOn name
    where name            :: Probability (State, Utility) -> State
          name            = fst.probabilityElement
          score           :: Probability (State, Utility) -> Utility
          score           = snd.probabilityElement
          weightedScore   :: Probability (State, Utility) -> Utility
          weightedScore p = fromRational (probabilityValue p) * score p
          weight          :: [Probability (State, Utility)] -> (State, Utility)
          weight ps       = (name $ head ps, (sum $ map weightedScore ps) / (fromRational $ sum $ map probabilityValue ps))

{--
  data Predisposition = Accurate | Inaccurate


  a = find typedParfitsHitchhiker :: Accuracy
  instance TGraph g => Find a (TypedGraph a g) where
    find (TypedGraph (Always a)) = a
    ...

  instance TGraph g, Find a g => Find a (TypedGraph b g) where
    find (_ :+: g) = find g

  TypedGraph Predisposition (TypedGraph Accuracy (TypedGraph Offer (TypedGraph Location (TypedGraph Action (TypedGraph Value (EmptyGraph))))))

  typedParfitsHitchhiker =
      Distribution [  Trustworthy %= 0.5
                   ,Untrustworthy %= 0.5
                   ]
  :+: Distribution [  Accurate %= 0.99
                   ,Inaccurate %= 0.01
                   ]
  :+: When (  Trustworthy :&:   Accurate)   Ride
  :|: When (  Trustworthy :&: Inaccurate) NoRide
  :|: When (Untrustworthy :&:   Accurate) NoRide
  :|: When (Untrustworthy :&: Inaccurate)   Ride
  :+: When   Ride City
  :|: When NoRide Desert
  :+: When (  Trustworthy :&:   City)   Pay
  :|: Otherwise                       NoPay
  :+: When (  Pay :&:   City)   Value -1000
  :+: When (NoPay :&:   City)   Value 0
  :|: Otherwise                 Value -1000000
  :+: Graph0
--}
