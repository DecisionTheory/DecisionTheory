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

  testSquash = test "Squash" [Probability "A" 0.3, Probability "B" 0.7] $ squash (when (==)) [Probability "A" 0.1, Probability "B" 0.4, Probability "A" 0.2, Probability "B" 0.3]

  test :: (Eq a, Show a) => String -> a -> a -> Either String (String, String, String)
  test s  a b | a == b    = Left ("Ok " ++ s)
              | otherwise = Right ("Failed " ++ s, show a, show b)

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

  weird = Graph [Labeled "a" a
                ,Labeled "b" b
                ,Labeled "c" c
                ]
    where a = Distribution [Probability "a1" 0.5
                           ,Probability "a2" 0.5
                           ]
          b = Conditional [Clause [Guard "a" "a1"] "b1"
                          ,Clause [Guard "a" "a2"] "b2"
                          ]
          c = Conditional [Clause [Guard "a" "a1", Guard "b" "b1"] "c1"
                          ,Clause [Guard "a" "a1", Guard "b" "b2"] "c2"
                          ,Clause [Guard "a" "a2", Guard "b" "b1"] "c3"
                          ,Clause [Guard "a" "a2", Guard "b" "b2"] "c4"
                          ]
  testProbabilitiesForWeird =
    test "ProbabilitiesForWeird" [Probability "c1" 0.5, Probability "c4" 0.5] $ probabilities "c" $ branches weird

  weirder = [Probability (Graph [Labeled "a" $ Always "a1"
                                ,Labeled "b" $ Conditional [Clause [Guard "a" "a1"] "b1"]
                                ,Labeled "c" $ Conditional [Clause [Guard "a" "a1", Guard "b" "b1"] "c1"]
                                ]
                         )
                         0.5
            ,Probability (Graph [Labeled "a" $ Always "a2"
                                ,Labeled "b" $ Conditional [Clause [Guard "a" "a2"] "b2"]
                                ,Labeled "c" $ Conditional [Clause [Guard "a" "a2", Guard "b" "b2"] "c4"]
                                ]
                         )
                         0.5
            ]

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

  testWeirdBranches = test "WeirdBranches" expected actual
    where actual = branches weird 
          expected = [Probability (Graph [Labeled "a" (Always "a1")
                                         ,Labeled "b" (Conditional [Clause [Guard "a" "a1"] "b1",Clause [Guard "a" "a2"] "b2"])
                                         ,Labeled "c" (Conditional [Clause [Guard "a" "a1",Guard "b" "b1"] "c1",Clause [Guard "a" "a1",Guard "b" "b2"] "c2",Clause [Guard "a" "a2",Guard "b" "b1"] "c3",Clause [Guard "a" "a2",Guard "b" "b2"] "c4"])
                                         ]) 0.5
                     ,Probability (Graph [Labeled "a" (Always "a2")
                                         ,Labeled "b" (Conditional [Clause [Guard "a" "a1"] "b1",Clause [Guard "a" "a2"] "b2"])
                                         ,Labeled "c" (Conditional [Clause [Guard "a" "a1",Guard "b" "b1"] "c1",Clause [Guard "a" "a1",Guard "b" "b2"] "c2",Clause [Guard "a" "a2",Guard "b" "b1"] "c3",Clause [Guard "a" "a2",Guard "b" "b2"] "c4"])
                                         ]) 0.5
                     ]

  testBranches = test "Branches" expected actual
    where actual = branches (Graph [Labeled "a" $ Distribution [Probability "a1" 0.1
                                                               ,Probability "a2" 0.9
                                                               ]
                                   ,Labeled "b" $ Distribution [Probability "b1" 0.3
                                                               ,Probability "b2" 0.7
                                                               ]
                                   ])
          expected = [Probability (Graph [Labeled "a" (Always "a1"),Labeled "b" (Always "b1")]) 0.03
                     ,Probability (Graph [Labeled "a" (Always "a1"),Labeled "b" (Always "b2")]) 0.07
                     ,Probability (Graph [Labeled "a" (Always "a2"),Labeled "b" (Always "b1")]) 0.27
                     ,Probability (Graph [Labeled "a" (Always "a2"),Labeled "b" (Always "b2")]) 0.63
                     ]

  xorBlackmail = Graph [Labeled "infestation" infestation
                       ,Labeled "prediction"  prediction
                       ,Labeled "action"      action
                       ,Labeled "value"       value
                       ,Labeled "observation" observation
                       ]
    where infestation = Distribution [Probability "termites" 0.5
                                     ,Probability "no termites" 0.5
                                     ]
          prediction  = Conditional [Clause [Guard "infestation" "termites",    Guard "action" "pay"   ] "skeptic"
                                    ,Clause [Guard "infestation" "termites",    Guard "action" "refuse"] "gullible"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "pay"   ] "gullible"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "refuse"] "skeptic"
                                    ]
          observation = Conditional [Clause [Guard "prediction" "gullible"] "letter"
                                    ,Clause [Guard "prediction" "skeptic"]  "no letter"
                                    ]
          action      = Distribution [Probability "pay" 0.01
                                     ,Probability "refuse" 0.99
                                     ]
          value       = Conditional [Clause [Guard "infestation" "termites",    Guard "action" "pay"   ] "-1001000"
                                    ,Clause [Guard "infestation" "termites",    Guard "action" "refuse"] "-1000000"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "pay"   ] "-1000"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "refuse"] "-0"
                                    ]

  edtChoiceForXorBlackmail = edt [Guard "observation" "letter"] stdSearch xorBlackmail

  testEdtChoiceForXorBlackmail = test "EdtChoiceForXorBlackmail" ("pay", -1000.0) $ edtChoiceForXorBlackmail

  condition :: Guard -> Endo [Probability (Graph Deterministic)]
  condition (Guard l v) = normalize . filter branchSatisfiesGuard
    where branchSatisfiesGuard (Probability g _) = Just v == find l g

  normalize :: Endo [Probability a]
  normalize ps = normalize' (sum (map probabilityValue ps)) ps
    where normalize' _ []     = []
          normalize' t (p:ps) = (prior (1/t) >> p) : normalize' t ps

  testNormalize =  test "Normalize" [Probability "A" 0.25,Probability "B" 0.75] $ normalize [Probability "A" 0.1, Probability "B" 0.3]

  causalXorBlackmail = Graph [Labeled "infestation"    infestation
                             ,Labeled "predisposition" predisposition
                             ,Labeled "prediction"     prediction
                             ,Labeled "action"         action
                             ,Labeled "value"          value
                             ,Labeled "observation"    observation
                             ]
    where infestation    = Distribution [Probability "termites" 0.5
                                        ,Probability "no termites" 0.5
                                        ]
          predisposition = Distribution [Probability "payer"   0.5
                                        ,Probability "refuser" 0.5
                                        ]
          prediction     = Conditional [Clause [Guard "infestation" "termites",    Guard "predisposition" "payer"  ] "skeptic"
                                       ,Clause [Guard "infestation" "termites",    Guard "predisposition" "refuser"] "gullible"
                                       ,Clause [Guard "infestation" "no termites", Guard "predisposition" "payer"  ] "gullible"
                                       ,Clause [Guard "infestation" "no termites", Guard "predisposition" "refuser"] "skeptic"
                                       ]
          observation = Conditional [Clause [Guard "prediction" "gullible"] "letter"
                                    ,Clause [Guard "prediction" "skeptic"]  "no letter"
                                    ]
          action      = Conditional [Clause [Guard "predisposition" "payer"]   "pay"
                                    ,Clause [Guard "predisposition" "refuser"] "refuse"
                                    ]
          value       = Conditional [Clause [Guard "infestation" "termites",    Guard "action" "pay"   ] "-1001000"
                                    ,Clause [Guard "infestation" "termites",    Guard "action" "refuse"] "-1000000"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "pay"   ] "-1000"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "refuse"] "-0"
                                    ]

  edtChoiceForCausalXorBlackmail = edt [Guard "observation" "letter"] stdSearch causalXorBlackmail

  testEdtChoiceForCausalXorBlackmail = test "EdtChoiceForCausalXorBlackmail" ("pay", -1000.0) edtChoiceForCausalXorBlackmail

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

  cdtChoiceForCausalXorBlackmail = cdt [Guard "observation" "letter"] stdSearch causalXorBlackmail
  testCdtChoiceForCausalXorBlackmail = test "CdtChoiceForCausalXorBlackmail" ("refuse", -1000000.0) cdtChoiceForCausalXorBlackmail


  deathInDamascus = Graph [Labeled "predisposition" predisposition
                          ,Labeled "action"         action
                          ,Labeled "death"          death
                          ,Labeled "outcome"        outcome
                          ,Labeled "value"          value
                          ]
    where predisposition = Distribution [Probability "fleer"  0.5
                                        ,Probability "stayer" 0.5
                                        ]
          action      = Conditional [Clause [Guard "predisposition" "fleer"]  "flee"
                                    ,Clause [Guard "predisposition" "stayer"] "stay"
                                    ]
          death       = Conditional [Clause [Guard "predisposition" "fleer"]  "aleppo"
                                    ,Clause [Guard "predisposition" "stayer"] "damascus"
                                    ]
          outcome        = Conditional [Clause [Guard "action" "stay", Guard "death" "damascus"] "stay and die"
                                       ,Clause [Guard "action" "stay", Guard "death" "aleppo"  ] "stay and live"
                                       ,Clause [Guard "action" "flee", Guard "death" "damascus"] "flee and live"
                                       ,Clause [Guard "action" "flee", Guard "death" "aleppo"  ] "flee and die"
                                       ]
          value          = Conditional [Clause [Guard "outcome" "stay and die" ]    "0"
                                       ,Clause [Guard "outcome" "stay and live"] "1000"
                                       ,Clause [Guard "outcome" "flee and live"]  "999"
                                       ,Clause [Guard "outcome" "flee and die" ]   "-1"
                                       ]

  edtChoiceForDeathInDamascus = edt [] stdSearch deathInDamascus
  testEdtChoiceForDeathInDamascus = test "EdtChoiceForDeathInDamascus" ("stay", 0.0) edtChoiceForDeathInDamascus

  cdtDominanceForDeathInDamascus = [dt intervene [Guard "action" "stay"] stdSearch deathInDamascus
                                   ,dt intervene [Guard "action" "flee"] stdSearch deathInDamascus
                                   ]

  testCdtDominanceForDeathInDamascus = test "CdtDominanceForDeathInDamascus" [("flee",999.0),("stay",1000.0)] cdtDominanceForDeathInDamascus


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

  parfitsHitchhiker = Graph [Labeled "predisposition" predisposition
                            ,Labeled "accuracy"       accuracy
                            ,Labeled "offer"          offer
                            ,Labeled "location"       location
                            ,Labeled "action"         action
                            ,Labeled "value"          value
                            ]
    where predisposition = Distribution [Probability "trustworthy" 0.5
                                        ,Probability "untrustworthy" 0.5
                                        ]
          accuracy       = Distribution [Probability "accurate"   0.99
                                        ,Probability "inaccurate" 0.01
                                        ]
          offer          = Conditional [Clause [Guard "predisposition" "trustworthy",   Guard "accuracy" "accurate"]   "ride"
                                       ,Clause [Guard "predisposition" "trustworthy",   Guard "accuracy" "inaccurate"] "no ride"
                                       ,Clause [Guard "predisposition" "untrustworthy", Guard "accuracy" "accurate"]   "no ride"
                                       ,Clause [Guard "predisposition" "untrustworthy", Guard "accuracy" "inaccurate"] "ride"
                                       ]
          location       = Conditional [Clause [Guard "offer" "ride"]    "city"
                                       ,Clause [Guard "offer" "no ride"] "desert"
                                       ]
          action         = Conditional [Clause [Guard "predisposition" "trustworthy", Guard "location" "city"] "pay"
                                       ,Clause [] "no pay"
                                       ]
          value          = Conditional [Clause [Guard "action" "pay",    Guard "location" "city"] "-1000"
                                       ,Clause [Guard "action" "no pay", Guard "location" "city"] "0"
                                       ,Clause []                                                 "-1000000"
                                       ]

  edtChoiceForParfitsHitchhiker = edt [] stdSearch parfitsHitchhiker
  testEdtChoiceForParfitsHitchhiker = test "EdtChoiceForParfitsHitchhiker" ("pay", -1000) edtChoiceForParfitsHitchhiker

  edtChoiceForParfitsHitchhikerGivenInCity = edt [Guard "location" "city"] stdSearch parfitsHitchhiker
  testEdtChoiceForParfitsHitchhikerGivenInCity = test "EdtChoiceForParfitsHitchhikerGivenInCity" ("no pay", 0) edtChoiceForParfitsHitchhikerGivenInCity

  cdtChoiceForParfitsHitchhiker = cdt [] stdSearch parfitsHitchhiker
  testCdtChoiceForParfitsHitchhiker = test "CdtChoiceForParfitsHitchhiker" ("no pay",-990099.0) cdtChoiceForParfitsHitchhiker

  cdtChoiceForParfitsHitchhikerGivenInCity = cdt [Guard "location" "city"] stdSearch parfitsHitchhiker
  testCdtChoiceForParfitsHitchhikerGivenInCity = test "CdtChoiceForParfitsHitchhikerGivenInCity" ("no pay", 0) cdtChoiceForParfitsHitchhikerGivenInCity

  fdt :: Foldable t => Label -> t Guard -> Search -> Graph Stochastic -> (State, Utility)
  fdt = stableDT . counterFactualize

  {-- We start with a uniform prior over the possible predispositions, then compute the possible universes 
      for each possible intervention on predisposition, and finally condition that distribution on the 
      choice of action we're evaluating.
   --}
  counterFactualize :: Label -> Guard -> Endo [Probability (Graph Deterministic)]
  counterFactualize l g ps = condition g $ normalize $ concatMap (\s -> intervene (Guard l s) ps) $ choices l ps

  fdtChoiceForCausalXorBlackmail = fdt (Label "predisposition") [Guard (Label "observation") (State "letter")] stdSearch causalXorBlackmail
  testFdtChoiceForCausalXorBlackmail = test "FdtChoiceForCausalXorBlackmail" ("refuse",-1000000.0) fdtChoiceForCausalXorBlackmail

  fdtChoiceForDeathInDamascus = fdt (Label "predisposition") [] stdSearch deathInDamascus
  testFdtChoiceDeathInDamascus = test "FdtChoiceForDeathInDamascus" ("stay",0.0) fdtChoiceForDeathInDamascus

  fdtChoiceForParfitsHitchhiker = fdt (Label "predisposition") [Guard (Label "location") (State "city")] stdSearch parfitsHitchhiker
  testFdtChoiceForParfitsHitchhiker = test "FdtChoiceForParfitsHitchhiker" ("pay",-1000.0) fdtChoiceForParfitsHitchhiker

  tests = [testSquash
          ,testProbabilitiesForWeird
          ,testWeirdBranches
          ,testBranches
          ,testNormalize
          ,testEdtChoiceForXorBlackmail
          ,testEdtChoiceForCausalXorBlackmail
          ,testCdtChoiceForCausalXorBlackmail
          ,testEdtChoiceForDeathInDamascus
          ,testCdtDominanceForDeathInDamascus
          ,testEdtChoiceForParfitsHitchhiker
          ,testEdtChoiceForParfitsHitchhikerGivenInCity
          ,testCdtChoiceForParfitsHitchhiker
          ,testCdtChoiceForParfitsHitchhikerGivenInCity
          ,testFdtChoiceForCausalXorBlackmail
          ,testFdtChoiceDeathInDamascus
          ,testFdtChoiceForParfitsHitchhiker
          ]
