{-# LANGUAGE EmptyDataDecls, GADTs, StandaloneDeriving, OverloadedStrings #-}

module DecisionTheory where
{--
 TODO
  Introduzir typeclasses nos locais apropriados
  Introduzir tipos mais explícitos
  Remover estruturas que não se pagam
 --}

  import Data.List (groupBy, sortBy, sortOn, maximumBy, uncons, null, nub, sort)
  import Data.Maybe (catMaybes,fromJust)
  import Data.Ord (comparing)
  import Data.Function (on)
  import qualified Data.Map.Strict as Map
  import Data.Ratio (Rational)
  import Data.Foldable (toList)
  import GHC.Exts (IsString(fromString))

  type Endo a = a -> a

  newtype Label = Label String
    deriving (Eq, Ord, Show)

  instance IsString Label where
    fromString = Label

  newtype State = State String
    deriving (Eq, Ord, Show)

  instance IsString State where
    fromString = State

  data Stochastic
  data Deterministic

  data Probability a = Probability a Rational
    deriving (Eq, Show)
  unProbability (Probability a r) = (a, r)
  probabilityElement (Probability a _) = a
  probabilityValue   (Probability _ r) = r

  mkProbability :: a -> Rational -> Probability a
  mkProbability a x | x > 0 && x < 1 = Probability a x
                    | otherwise      = error $ "Invalid probability " ++ show x

  prior :: Rational -> Probability ()
  prior = Probability ()

  instance Functor Probability where
    fmap f (Probability e v) = Probability (f e) v

  instance Applicative Probability where
    pure a = Probability a 1
    (Probability f x) <*> (Probability a y) = Probability (f a) (x * y)

  instance Monad Probability where
    (Probability a x) >>= k = let Probability b y = k a in Probability b (x * y)

  data Distribution a = Distribution_ [Probability a]
    deriving (Eq, Show)

  mkDistribution :: [Probability a] -> Distribution a
  mkDistribution ps = Distribution_ $ filter ((>0).probabilityValue) $ map normalize ps
    where
      normalize (Probability a x) = Probability a (x/t)
      t = sum $ map probabilityValue ps

  data Node a where
     Always :: State -> Node a
     Distribution :: [Probability State] -> Node Stochastic
     Conditional :: [Clause] -> Node a

  data Guard = Guard Label State
    deriving (Eq, Show)

  data Clause = Clause [Guard] State
    deriving (Eq, Show)

  clauseValue (Clause _ v) = v

  deriving instance Eq (Node a) 
  deriving instance Show (Node a)

  data Graph a = Graph [Labeled (Node a)]
    deriving (Eq, Show)
  unGraph (Graph g) = g

  data Labeled a = Labeled Label a
    deriving (Eq, Show)

  instance Functor Labeled where
    fmap f (Labeled l a) = Labeled l (f a)

  type Utility = Float

  data Search = Search (State -> Utility) Label Label
  stdSearch = (Search uf "action" "value")
    where uf (State s) = read s

  dot :: String -> Graph a -> String
  dot s (Graph lns) = "digraph " ++ s ++ " {\r\n" ++ nodes ++ "}\r\n"
    where nodes = foldr (++) "" $ map prettyPrint lns
          prettyPrint (Labeled (Label l) n) = describe l n ++ "\r\n"
          describe l (Conditional cs) = foldr (++) "" $ map (\k -> k ++ " -> " ++ l ++ ";\r\n") $ clauses cs
          describe l _                = l
          clauses = nub . sort . concatMap (\(Clause gs _) -> guards gs)
          guards  = nub . sort . map (\(Guard (Label n) _) -> n)

  dt :: Foldable t => (Guard -> Endo [Probability (Graph Deterministic)]) -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  dt hypothesis gs (Search uf a o) g = maximumBy (comparing snd) $ map expectation $ hypotheticals
    where hypotheticals :: [(State, [Probability (Graph Deterministic)])]
          hypotheticals = catMaybes $ map (hypothetical.conclusion) $ choices a $ branches g
          hypothetical (v, []) = Nothing
          hypothetical c       = Just c
          conclusion v = (v, hypothesis (Guard a v) possibleBranches)
          possibleBranches = foldl (flip condition) (branches g) gs
          expectedValue :: Probability (Graph Deterministic) -> Utility
          expectedValue (Probability g v) = ((* (fromRational v)) . uf) $ fromJust $ find o g
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

  find :: Label -> Graph Deterministic -> Maybe State
  find l g@(Graph lns) = resolve =<< getByLabel lns
    where getByLabel :: [Labeled (Node a)] -> Maybe (Node a)
          getByLabel [] = Nothing
          getByLabel ((Labeled l' n):lns) | l' == l = Just n
                                          | otherwise = getByLabel lns
          resolve :: Node Deterministic -> Maybe State
          resolve (Always v) = Just v
          resolve (Conditional cs) = fmap (clauseValue.fst) $ uncons $ filter clauseMatches cs
          clauseMatches :: Clause -> Bool
          clauseMatches (Clause gs _) = all guardMatches gs
          guardMatches (Guard l' v) = find l' g == Just v

  probabilities :: Label -> [Probability (Graph Deterministic)] -> [Probability State]
  probabilities l = squash (when (==)) . catMaybes . map find'
    where find' (Probability g p) = fmap (flip Probability p) (find l g)

  when :: (a -> a -> Bool) -> (a -> a -> Maybe a)
  when (==) a1 a2 | a1 == a2  = Just a1
                  | otherwise = Nothing

  squash :: Ord a => (a -> a -> Maybe a) -> Endo [Probability a]
  squash (>+<) = squash' . sortOn unProbability
    where squash' (p1:p2:ps) = case merge p1 p2 of
                                 Nothing -> p1:squash' (p2:ps)
                                 Just p3 ->    squash' (p3:ps)
          squash' ps         = ps
          merge (Probability a x) (Probability b y) = fmap (flip Probability (x+y)) (a >+< b)

  choices :: Label -> [Probability (Graph Deterministic)] -> [State]
  choices l = map probabilityElement . probabilities l

  weighted :: [Probability (State, Utility)] -> [(State, Utility)]
  weighted = map weight . groupBy ((==) `on` name) . sortOn name
    where name            :: Probability (State, Utility) -> State
          name            = fst.probabilityElement
          score           :: Probability (State, Utility) -> Utility
          score           = snd.probabilityElement
          weightedScore   :: Probability (State, Utility) -> Utility
          weightedScore p = fromRational (probabilityValue p) * score p
          weight          :: [Probability (State, Utility)] -> (State, Utility)
          weight ps       = (name $ head ps, (sum $ map weightedScore ps) / (fromRational $ sum $ map probabilityValue ps))

  branches :: Graph Stochastic -> [Probability (Graph Deterministic)]
  branches (Graph ls) = filter ((>0) . snd . unProbability) $ loop ls
    where prepend l = fmap $ \(Graph ls) -> Graph (l:ls)
          loop []                                 = [Probability (Graph []) 1.0]
          loop ((Labeled l (Always a))       :ls) = map (prepend (Labeled l (Always a)))      $ loop ls
          loop ((Labeled l (Conditional c))  :ls) = map (prepend (Labeled l (Conditional c))) $ loop ls
          loop ((Labeled l (Distribution ps)):ls) = [branch l pa pb | pa <- ps, pb <- loop ls]
          branch :: Label -> Probability State -> Endo (Probability (Graph b))
          branch l pa pb = do s <- pa
                              Graph ls' <- pb
                              let l' = Labeled l $ Always s
                              return $ Graph (l':ls')

  condition :: Guard -> Endo [Probability (Graph Deterministic)]
  condition (Guard l v) = normalize . filter branchSatisfiesGuard
    where branchSatisfiesGuard (Probability g _) = Just v == find l g

  normalize :: Endo [Probability a]
  normalize ps = normalize' (sum (map probabilityValue ps)) ps
    where normalize' _ []     = []
          normalize' t (p:ps) = (prior (1/t) >> p) : normalize' t ps

  cdt :: [Guard] -> Search -> Graph Stochastic -> (State, Utility)
  cdt = stableDT intervene

  intervene :: Guard -> Endo [Probability (Graph Deterministic)]
  intervene (Guard l v) = normalize . map (mapBranches intervention)
    where intervention :: Endo (Labeled (Node Deterministic))
          intervention ln@(Labeled l' _) | l == l'   = Labeled l (Always v)
                                         | otherwise = ln

  mapBranches :: Endo (Labeled (Node a)) -> Endo (Probability (Graph a))
  mapBranches f = fmap (\(Graph lns) -> Graph (map f lns))

  replaceG :: Endo (Labeled (Node a)) -> Endo (Graph a)
  replaceG f (Graph lns) = Graph $ map f lns


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

  fdt :: Foldable t => Label -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  fdt = stableDT . counterFactualize

  {-- We start with a uniform prior over the possible predispositions, then compute the possible universes 
      for each possible intervention on predisposition, and finally condition that distribution on the 
      choice of action we're evaluating.
   --}
  counterFactualize :: Label -> Guard -> Endo [Probability (Graph Deterministic)]
  counterFactualize l g ps = condition g $ normalize $ concatMap (\s -> intervene (Guard l s) ps) $ choices l ps
