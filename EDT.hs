module EDT where
  import Data.List (groupBy, sortOn, maximumBy)
  import Data.Ord (comparing)
  import Data.Function (on)

  data Graph = Graph [Labeled Node]
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

  data Node = Always String
            | Distribution [Probability String]
            | Conditional [Clause]
    deriving (Eq, Show)

  newcomb = Graph [Labeled "action"         action
                  ,Labeled "accuracy"       accuracy
                  ,Labeled "prediction"     prediction
                  ,Labeled "predisposition" predisposition
                  ,Labeled "box_b"          box_b
                  ,Labeled "outcome"        outcome
                  ,Labeled "value"          value
                  ]
    where action         = Distribution [Probability "onebox" undefined
                                        ,Probability "twobox" undefined
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

  findG :: String -> Graph -> [Probability String]
  findG l g@(Graph xs) = squash $ find' xs
    where find' []     = []
          find' (x:xs) = found x ++ (find' xs)
          found (Labeled s n) | l == s    = case n of
                                              Always a        -> [Probability a 1.0]
                                              Distribution ds -> ds
                                              Conditional  ds -> concatMap computeDependentProbabilities ds
                              | otherwise = []
          computeDependentProbabilities (Clause gs v) = probabilityForGuards g 1.0 v gs
          squash = map sumProbabilities . groupBy ((==) `on` (fst.unProbability)) . sortOn (fst.unProbability)
          sumProbabilities ps@((Probability v _):_) = Probability v (sum $ map (snd.unProbability) ps)

  probabilityForGuards :: Graph -> Float -> String -> [Guard] -> [Probability String]
  probabilityForGuards _ 0 _ _          = []
  probabilityForGuards _ p v []         = [Probability v p]
  probabilityForGuards g p v ((Guard n e):gs) = probabilityForGuards (intervene n e g) (p * (sum $ map (probabilityForGuard e) $ findG n g)) v gs
  probabilityForGuard e (Probability v p) | v == e    = p
                                          | otherwise = 0.0

  mapG :: (Labeled  Node -> Node) -> Graph -> Graph
  mapG f (Graph [])     = Graph []
  mapG f (Graph (n:ns)) = Graph ((Labeled (label n) (f n)) : (unGraph $ mapG f (Graph ns)))

  intervene :: String -> String -> Graph -> Graph
  intervene l c g = mapG (\(Labeled s n) -> if (s == l) then (Always c) else n) g

  choices :: String -> Graph -> [String]
  choices l = map (fst.unProbability) . findG l

  bestChoice :: (String -> Float) -> String -> String -> Graph -> (String, Float)
  bestChoice uf a v g = maximumBy (comparing snd) $ map (\(c,g) -> (c, ev $ findG v g)) gs
    where gs = map (\c -> (c, intervene a c g)) $ choices a g
          ev = sum . map (\(Probability v p) -> uf v * p)

  edtChoiceForNewcomb = bestChoice read "action" "value" newcomb

  expectedEdtChoiceForNewcomb = ("onebox", 990000.0) == edtChoiceForNewcomb

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
  expectedFindGForWeird = [Probability "c1" 0.5, Probability "c4" 0.5] == findG "c" weird

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

  branches :: Graph -> [Probability Graph]
  branches (Graph ls) = loop ls
    where loop [] = [Probability (Graph []) 1.0]
          loop (l@(Labeled _ (Always _)):ls) = map (prepend l) $ loop ls
          loop ((Labeled l (Distribution ps)):ls) = do (Probability s p1) <- ps
                                                       (Probability (Graph ls') p2) <- loop ls
                                                       return (Probability (Graph ((Labeled l $ Always s):ls')) (p1 * p2))
          loop (l@(Labeled _ (Conditional _)):ls) = map (prepend l) $ loop ls
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

{--
  decondition :: Graph -> Graph
  decondition g@(Graph ls) = loop ls
    where loop [] = Graph []
          loop (l@(Labeled _ (Always _)):ls) = Graph (l:loop ls)
          loop ((Labeled s (Conditional cs)):ls) = case decondition' g cs of
                                                     Nothing -> Graph (loop ls)
                                                     Just l -> Graph (l:loop ls)
          decondition' _ [] = Nothing
          decondition' g ((Clause guards o):cs) = do Guard l e <- guards
--}