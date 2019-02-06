{-# LANGUAGE EmptyDataDecls, GADTs, StandaloneDeriving #-}

module EDT where
  import Data.List (groupBy, sortBy, sortOn, maximumBy, uncons, nub)
  import Data.Maybe (catMaybes)
  import Data.Ord (comparing)
  import Data.Function (on)

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

  data Probability a = Probability a Float
    deriving (Eq, Show)
  unProbability (Probability a f) = (a, f)

  data Guard = Guard String String
    deriving (Eq, Show)

  instance WithLabel Guard where
    label (Guard s _) = s

  data Clause = Clause [Guard] String
    deriving (Eq, Show)

  clauseValue (Clause _ v) = v

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

  edtChoiceForNewcomb = edt (Search read "action" "value") newcomb

  expectedEdtChoiceForNewcomb = ("onebox", 990000.0) == edtChoiceForNewcomb



  data Search = Search (String -> Float) String String
  edt :: Search -> Graph Stochastic -> (String, Float)
  edt (Search uf a o) = consolidate . catMaybes . map expectedValue . branches
    where expectedValue (Probability g v) = do a' <- find a g
                                               o' <- find o g
                                               return $ Probability (a', uf o') v
          consolidate = maximumBy (comparing snd) . weighted

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
  probabilities l = catMaybes . map find' . branches
    where find' (Probability g p) = fmap (`Probability` p) (find l g)

  --TODO implement squash to consolidate duplicates

  choices :: String -> Graph Stochastic -> [String]
  choices l = nub . map (fst.unProbability) . probabilities l

  weighted :: [Probability (String, Float)] -> [(String, Float)]
  weighted = map weight . groupBy ((==) `on` name) . sortOn name
    where name            = fst.fst.unProbability
          score           = snd.fst.unProbability
          probability     = snd.unProbability
          weightedScore p = probability p * score p
          weight ps       = (name $ head ps, (sum $ map weightedScore ps) / (sum $ map probability ps))

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
  expectedProbabilitiesForWeird = [Probability "c1" 0.5, Probability "c4" 0.5] == probabilities "c" weird

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

  expectedWeirdBranches = expected == actual
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

  expectedBranches = expected == actual
    where actual = branches (Graph [Labeled "a" $ Distribution [Probability "a1" 0.1
                                                               ,Probability "a2" 0.9
                                                               ]
                                   ,Labeled "b" $ Distribution [Probability "b1" 0.3
                                                               ,Probability "b2" 0.7
                                                               ]
                                   ])
          expected = [Probability (Graph [Labeled "a" (Always "a1"),Labeled "b" (Always "b1")]) 3.0000001e-2
                     ,Probability (Graph [Labeled "a" (Always "a1"),Labeled "b" (Always "b2")]) 0.07
                     ,Probability (Graph [Labeled "a" (Always "a2"),Labeled "b" (Always "b1")]) 0.27
                     ,Probability (Graph [Labeled "a" (Always "a2"),Labeled "b" (Always "b2")]) 0.63
                     ]
