{-# LANGUAGE EmptyDataDecls, GADTs, StandaloneDeriving #-}

module EDT where
  import Data.List (groupBy, sortBy, sortOn, maximumBy, uncons, null)
  import Data.Maybe (catMaybes,fromJust)
  import Data.Ord (comparing)
  import Data.Function (on)
  import qualified Data.Map.Strict as Map
  import Data.Ratio (Rational)
  import Data.Foldable (toList)

  type Endo a = a -> a

  data Stochastic
  data Deterministic

  data Node a where
     Always :: String -> Node a
     Distribution :: [Probability String] -> Node Stochastic
     Conditional :: [Clause] -> Node a

  deriving instance Eq (Node a) 
  deriving instance Show (Node a)

  data Graph a = Graph [Labeled (Node a)]
    deriving (Eq, Show)
  unGraph (Graph g) = g

  class WithLabel l where
    label :: l -> String 

  data Labeled a = Labeled String a
    deriving (Eq, Show)

  instance WithLabel (Labeled a) where
    label (Labeled s _) = s

  data Probability a = Probability a Rational
    deriving (Eq, Show)
  unProbability (Probability a r) = (a, r)
  probabilityElement (Probability a _) = a
  probabilityValue   (Probability _ r) = r

  data Guard = Guard String String
    deriving (Eq, Show)

  instance WithLabel Guard where
    label (Guard s _) = s

  data Clause = Clause [Guard] String
    deriving (Eq, Show)

  clauseValue (Clause _ v) = v

  type Utility = Float

  newcomb = Graph [Labeled "action"         action
                  ,Labeled "accuracy"       accuracy
                  ,Labeled "prediction"     prediction
                  ,Labeled "predisposition" predisposition
                  ,Labeled "box_b"          box_b
                  ,Labeled "outcome"        outcome
                  ,Labeled "value"          value
                  ]
    where action         = Distribution [Probability "onebox" 0.01
                                        ,Probability "twobox" 0.99
                                        ]
          accuracy       = Distribution [Probability "accurate"   0.99
                                        ,Probability "inaccurate" 0.01
                                        ]
          prediction     = Conditional [Clause [Guard "predisposition" "oneboxer", Guard "accuracy"   "accurate"] "p1"
                                       ,Clause [Guard "predisposition" "twoboxer", Guard "accuracy"   "accurate"] "p2"
                                       ,Clause [Guard "predisposition" "oneboxer", Guard "accuracy" "inaccurate"] "p2"
                                       ,Clause [Guard "predisposition" "twoboxer", Guard "accuracy" "inaccurate"] "p1"
                                       ]
          predisposition = Conditional [Clause [Guard "action" "onebox"] "oneboxer"
                                       ,Clause [Guard "action" "twobox"] "twoboxer"
                                       ]
          box_b          = Conditional [Clause [Guard "prediction" "p1"] "full"
                                       ,Clause [Guard "prediction" "p2"] "empty"
                                       ]
          outcome        = Conditional [Clause [Guard "action" "onebox", Guard "box_b" "full" ] "1f"
                                       ,Clause [Guard "action" "twobox", Guard "box_b" "full" ] "2f"
                                       ,Clause [Guard "action" "onebox", Guard "box_b" "empty"] "1e"
                                       ,Clause [Guard "action" "twobox", Guard "box_b" "empty"] "2e"
                                       ]
          value          = Conditional [Clause [Guard "outcome" "1f"] "1000000"
                                       ,Clause [Guard "outcome" "2f"] "1001000"
                                       ,Clause [Guard "outcome" "1e"]       "0"
                                       ,Clause [Guard "outcome" "2e"]    "1000"
                                       ]

  edtChoiceForNewcomb = edt [] (Search read "action" "value") newcomb

  testEdtChoiceForNewcomb = test "EdtChoiceForNewcomb" ("onebox", 990000.0) $ edtChoiceForNewcomb

  testNewcombChoices = test "NewcombChoices" ["onebox", "twobox"] $ choices "action" $ branches newcomb

  data Search = Search (String -> Utility) String String

  dt :: Foldable t => (Guard -> Endo [Probability (Graph Deterministic)]) -> t Guard -> Search -> Graph Stochastic -> (String, Utility)
  dt hypothesis gs (Search uf a o) g = maximumBy (comparing snd) $ map expectation $ hypotheticals
    where hypotheticals :: [(String, [Probability (Graph Deterministic)])]
          hypotheticals = catMaybes $ map (hypothetical.conclusion) $ choices a $ branches g
          hypothetical (v, []) = Nothing
          hypothetical c       = Just c
          conclusion v = (v, hypothesis (Guard a v) possibleBranches)
          possibleBranches = foldl (flip condition) (branches g) gs
          expectedValue (Probability g v) = ((* (fromRational v)) . uf) $ fromJust $ find o g
          expectation (v, ps) = (v, sum $ map expectedValue ps)

  stableDT :: Foldable t => (Guard -> Endo [Probability (Graph Deterministic)]) -> t Guard -> Search -> Graph Stochastic -> (String, Utility)
  stableDT hypothesis gs s@(Search _ a _) g | fst decision == fst dominance = decision
                                            | otherwise                     = error ("OMG! " ++ (show dominance) ++ " /= " ++ (show decision))
    where decision :: (String, Utility)
          decision = dt hypothesis ((Guard a (fst dominance)): toList gs) s g
          dominance :: (String, Utility)
          dominance = dt hypothesis gs s g

  edt :: Foldable t => t Guard -> Search -> Graph Stochastic -> (String, Utility)
  edt = stableDT condition

  find :: String -> Graph Deterministic -> Maybe String
  find l g@(Graph lns) = resolve =<< getByLabel lns
    where getByLabel :: [Labeled (Node a)] -> Maybe (Node a)
          getByLabel [] = Nothing
          getByLabel ((Labeled l' n):lns) | l' == l = Just n
                                          | otherwise = getByLabel lns
          resolve :: Node Deterministic -> Maybe String
          resolve (Always v) = Just v
          resolve (Conditional cs) = fmap (clauseValue.fst) $ uncons $ filter clauseMatches cs
          clauseMatches :: Clause -> Bool
          clauseMatches (Clause gs _) = all guardMatches gs
          guardMatches (Guard l' v) = find l' g == Just v

  probabilities :: String -> [Probability (Graph Deterministic)] -> [Probability String]
  probabilities l = squash (when (==)) . catMaybes . map find'
    where find' (Probability g p) = fmap (`Probability` p) (find l g)


  when :: (a -> a -> Bool) -> (a -> a -> Maybe a)
  when (==) a1 a2 | a1 == a2  = Just a1
                  | otherwise = Nothing

  testSquash = test "Squash" [Probability "A" 0.3, Probability "B" 0.7] $ squash (when (==)) [Probability "A" 0.1, Probability "B" 0.4, Probability "A" 0.2, Probability "B" 0.3]

  test s  a b | a == b    = Left ("Ok " ++ s)
              | otherwise = Right ("Failed " ++ s, a, b)

  squash :: Ord a => (a -> a -> Maybe a) -> Endo [Probability a]
  squash (>+<) = squash' . sortOn unProbability
    where squash' (p1:p2:ps) = maybe (p1:squash' (p2:ps)) (\a3 -> squash' ((Probability a3 (probabilityValue p1 + probabilityValue p2)):ps)) (probabilityElement p1 >+< probabilityElement p2)
          squash' ps         = ps

  choices :: String -> [Probability (Graph Deterministic)] -> [String]
  choices l = map probabilityElement . probabilities l

  weighted :: [Probability (String, Utility)] -> [(String, Utility)]
  weighted = map weight . groupBy ((==) `on` name) . sortOn name
    where name            :: Probability (String, Utility) -> String
          name            = fst.probabilityElement
          score           :: Probability (String, Utility) -> Utility
          score           = snd.probabilityElement
          weightedScore   :: Probability (String, Utility) -> Utility
          weightedScore p = fromRational (probabilityValue p) * score p
          weight          :: [Probability (String, Utility)] -> (String, Utility)
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
    where loop [] = [Probability (Graph []) 1.0]
          loop ((Labeled l (Always a)):ls) = map (prepend (Labeled l (Always a))) $ loop ls
          loop ((Labeled l (Distribution ps)):ls) = do (Probability s p1) <- ps
                                                       (Probability (Graph ls') p2) <- loop ls
                                                       return (Probability (Graph ((Labeled l $ Always s):ls')) (p1 * p2))
          loop ((Labeled l (Conditional c)):ls) = map (prepend (Labeled l (Conditional c))) $ loop ls
          prepend l (Probability (Graph ls) p) = Probability (Graph (l:ls)) p

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


  causalNewcomb = Graph [Labeled "action"         action
                        ,Labeled "accuracy"       accuracy
                        ,Labeled "prediction"     prediction
                        ,Labeled "predisposition" predisposition
                        ,Labeled "box_b"          box_b
                        ,Labeled "outcome"        outcome
                        ,Labeled "value"          value
                        ]
    where predisposition = Distribution [Probability "oneboxer" 0.5
                                        ,Probability "twoboxer" 0.5
                                        ]
          action         = Conditional [Clause [Guard "predisposition" "oneboxer"] "onebox"
                                       ,Clause [Guard "predisposition" "twoboxer"] "twobox"
                                       ]
          accuracy       = Distribution [Probability "accurate"   0.99
                                        ,Probability "inaccurate" 0.01
                                        ]
          prediction     = Conditional [Clause [Guard "predisposition" "oneboxer", Guard "accuracy"   "accurate"] "p1"
                                       ,Clause [Guard "predisposition" "twoboxer", Guard "accuracy"   "accurate"] "p2"
                                       ,Clause [Guard "predisposition" "oneboxer", Guard "accuracy" "inaccurate"] "p2"
                                       ,Clause [Guard "predisposition" "twoboxer", Guard "accuracy" "inaccurate"] "p1"
                                       ]
          box_b          = Conditional [Clause [Guard "prediction" "p1"] "full"
                                       ,Clause [Guard "prediction" "p2"] "empty"
                                       ]
          outcome        = Conditional [Clause [Guard "action" "onebox", Guard "box_b" "full" ] "1f"
                                       ,Clause [Guard "action" "twobox", Guard "box_b" "full" ] "2f"
                                       ,Clause [Guard "action" "onebox", Guard "box_b" "empty"] "1e"
                                       ,Clause [Guard "action" "twobox", Guard "box_b" "empty"] "2e"
                                       ]
          value          = Conditional [Clause [Guard "outcome" "1f"] "1000000"
                                       ,Clause [Guard "outcome" "2f"] "1001000"
                                       ,Clause [Guard "outcome" "1e"]       "0"
                                       ,Clause [Guard "outcome" "2e"]    "1000"
                                       ]
  edtChoiceForCausalNewcomb = edt [] (Search read "action" "value") causalNewcomb

  testEdtChoiceForCausalNewcomb = test "EdtChoiceForCausalNewcomb" ("onebox", 990000.0) $ edtChoiceForCausalNewcomb

  testCausalNewcombChoices = test "CausalNewcombChoices" ["onebox", "twobox"] $ choices "action" $ branches newcomb

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

  edtChoiceForXorBlackmail = edt [Guard "observation" "letter"] (Search read "action" "value") xorBlackmail

  testEdtChoiceForXorBlackmail = test "EdtChoiceForXorBlackmail" ("pay", -1000.0) $ edtChoiceForXorBlackmail

  condition :: Guard -> Endo [Probability (Graph Deterministic)]
  condition (Guard l v) = normalize . filter branchSatisfiesGuard
    where branchSatisfiesGuard (Probability g _) = Just v == find l g

  normalize :: Endo [Probability a]
  normalize ps = normalize' (sum (map probabilityValue ps)) ps
    where normalize' _ []     = []
          normalize' t (p:ps) = Probability (probabilityElement p) (probabilityValue p / t) : normalize' t ps

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

  edtChoiceForCausalXorBlackmail = edt [Guard "observation" "letter"] (Search read "action" "value") causalXorBlackmail

  testEdtChoiceForCausalXorBlackmail = test "EdtChoiceForCausalXorBlackmail" ("pay", -1000.0) edtChoiceForCausalXorBlackmail

  cdt :: [Guard] -> Search -> Graph Stochastic -> (String, Utility)
  cdt = stableDT intervene

  intervene :: Guard -> Endo [Probability (Graph Deterministic)]
  intervene (Guard l v) = normalize . map (mapBranches intervention)
    where intervention :: Endo (Labeled (Node Deterministic))
          intervention ln@(Labeled l' _) | l == l'   = Labeled l (Always v)
                                         | otherwise = ln

  mapBranches :: Endo (Labeled (Node a)) -> Endo (Probability (Graph a))
  mapBranches f (Probability (Graph lns) v) = Probability (Graph (map f lns)) v

  cdtChoiceForCausalNewcomb = cdt [] (Search read "action" "value") causalNewcomb
  testCdtChoiceForCausalNewcomb = test "CdtChoiceForCausalNewcomb" ("twobox", 11000.0) cdtChoiceForCausalNewcomb

  cdtChoiceForCausalXorBlackmail = cdt [Guard "observation" "letter"] (Search read "action" "value") causalXorBlackmail
  testCdtChoiceForCausalXorBlackmail = test "CausalXorBlackmail" ("refuse", -1000000.0) cdtChoiceForCausalXorBlackmail


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

  stdSearch = (Search read "action" "value")

  edtChoiceForDeathInDamascus = edt [] (Search read "action" "value") deathInDamascus
  testEdtChoiceForDeathInDamascus = test "EdtChoiceForDeathInDamascus" ("stay", 0.0) edtChoiceForDeathInDamascus

  cdtDominanceForDeathInDamascus = [dt intervene [Guard "action" "stay"] (Search read "action" "value") deathInDamascus
                                   ,dt intervene [Guard "action" "flee"] (Search read "action" "value") deathInDamascus
                                   ]

  testCdtDominanceForDeathInDamascus = test "CdtDominanceForDeathInDamascus" [("flee",999.0),("stay",1000.0)] cdtDominanceForDeathInDamascus

  tests = (testEdtChoiceForNewcomb
          ,testNewcombChoices
          ,testSquash
          ,testProbabilitiesForWeird
          ,testWeirdBranches
          ,testBranches
          ,testEdtChoiceForCausalNewcomb
          ,testCausalNewcombChoices
          ,testNormalize
          ,testEdtChoiceForXorBlackmail
          ,testEdtChoiceForCausalXorBlackmail
          ,testCdtChoiceForCausalNewcomb
          ,testCdtChoiceForCausalXorBlackmail
          ,testEdtChoiceForDeathInDamascus
          ,testCdtDominanceForDeathInDamascus
          )

