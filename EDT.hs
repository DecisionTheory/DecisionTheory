{-# LANGUAGE EmptyDataDecls, GADTs, StandaloneDeriving #-}

module EDT where
  import Data.List (groupBy, sortBy, sortOn, maximumBy, uncons)
  import Data.Maybe (catMaybes)
  import Data.Ord (comparing)
  import Data.Function (on)
  import qualified Data.Map.Strict as Map
  import Data.Ratio (Rational)

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
    where action         = Distribution [Probability "onebox" 0.5
                                        ,Probability "twobox" 0.5
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

  testNewcombChoices = test "NewcombChoices" ["onebox", "twobox"] $ choices "action" newcomb

  data Search = Search (String -> Utility) String String

  edt :: [Guard] -> Search -> Graph Stochastic -> (String, Utility)
  edt gs (Search uf a o) g = maximumBy (comparing snd) $ map (\(v, ps) -> (v, sum $ map expectedValue ps)) conditions
    where conditions :: [(String, [Probability (Graph Deterministic)])]
          conditions = map imagine $ choices a g
          imagine v = (v, condition (Guard a v) conditionedBranches)
          conditionedBranches = foldl (flip condition) (branches g) gs
          expectedValue p = maybe 0.0 ((* (fromRational $ probabilityValue p)) . uf) $ find o $ probabilityElement p


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

  probabilities :: String -> Graph Stochastic -> [Probability String]
  probabilities l = squash (when (==)) . catMaybes . map find' . branches
    where find' (Probability g p) = fmap (`Probability` p) (find l g)


  when :: (a -> a -> Bool) -> (a -> a -> Maybe a)
  when (==) a1 a2 | a1 == a2  = Just a1
                  | otherwise = Nothing

  testSquash = test "Squash" [Probability "A" 0.3, Probability "B" 0.7] $ squash (when (==)) [Probability "A" 0.1, Probability "B" 0.4, Probability "A" 0.2, Probability "B" 0.3]

  test s  a b | a == b    = Left ("Ok " ++ s)
              | otherwise = Right ("Failed " ++ s, a, b)

  squash :: Ord a => (a -> a -> Maybe a) -> [Probability a] -> [Probability a]
  squash (>+<) = squash' . sortOn unProbability
    where squash' (p1:p2:ps) = maybe (p1:squash' (p2:ps)) (\a3 -> squash' ((Probability a3 (probabilityValue p1 + probabilityValue p2)):ps)) (probabilityElement p1 >+< probabilityElement p2)
          squash' ps         = ps

  choices :: String -> Graph Stochastic -> [String]
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
  testProbabilitiesForWeird = test "ProbabilitiesForWeird" [Probability "c1" 0.5, Probability "c4" 0.5] $ probabilities "c" weird

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

  testCausalNewcombChoices = test "CausalNewcombChoices" ["onebox", "twobox"] $ choices "action" newcomb

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
          action      = Distribution [Probability "pay" 0.5
                                     ,Probability "refuse" 0.5
                                     ]
          value       = Conditional [Clause [Guard "infestation" "termites",    Guard "action" "pay"   ] "-1001000"
                                    ,Clause [Guard "infestation" "termites",    Guard "action" "refuse"] "-1000000"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "pay"   ] "-1000"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "refuse"] "-0"
                                    ]

  edtChoiceForXorBlackmail = edt [Guard "observation" "letter"] (Search read "action" "value") xorBlackmail

  testEdtChoiceForXorBlackmail = test "EdtChoiceForXorBlackmail" ("pay", -1000.0) $ edtChoiceForXorBlackmail

  -- TODO refactor condition' to use filter
  condition :: Guard -> [Probability (Graph Deterministic)] -> [Probability (Graph Deterministic)]
  condition (Guard l v) = normalize . condition'
    where condition' :: [Probability (Graph Deterministic)] -> [Probability (Graph Deterministic)]
          condition' [] = []
          condition' (p:ps) = case conditionBranch (probabilityElement p) of
                                Just g  -> Probability g (probabilityValue p) : condition' ps
                                Nothing -> condition' ps
          conditionBranch :: Graph Deterministic -> Maybe (Graph Deterministic)
          conditionBranch g | Just v == find l g = Just g
                            | otherwise          = Nothing

  normalize :: [Probability a] -> [Probability a]
  normalize ps = normalize' (sum (map probabilityValue ps)) ps
    where normalize' _ []     = []
          normalize' t (p:ps) = Probability (probabilityElement p) (probabilityValue p / t) : normalize' t ps

  testNormalize =  test "Normalize" [Probability "A" 0.25,Probability "B" 0.75] $ normalize [Probability "A" 0.1, Probability "B" 0.3]

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
          )