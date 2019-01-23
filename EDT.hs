module EDT where
  import Data.List (groupBy, sortOn, maximumBy)
  import Data.Ord (comparing)
  import Data.Function (on)

  data Graph = Graph [(String, Node)]
    deriving (Eq, Show)
  unGraph (Graph g) = g

  data Node = Distribution [(String,Float)]
            | Depends [([(String,String)],String)]
    deriving (Eq, Show)

  newcomb = Graph [("action",         action)
                  ,("accuracy",       accuracy)
                  ,("prediction",     prediction)
                  ,("predisposition", predisposition)
                  ,("box_b",          box_b)
                  ,("outcome",        outcome)
                  ,("value",          value)
                  ]
    where action         = Distribution [("onebox", undefined), ("twobox", undefined)]
          accuracy       = Distribution [("accurate", 0.99), ("inaccurate", 0.01)]
          prediction     = Depends [([("predisposition", "oneboxer"), ("accuracy",   "accurate")], "p1")
                                   ,([("predisposition", "twoboxer"), ("accuracy",   "accurate")], "p2")
                                   ,([("predisposition", "oneboxer"), ("accuracy", "inaccurate")], "p2")
                                   ,([("predisposition", "twoboxer"), ("accuracy", "inaccurate")], "p1")
                                   ]
          predisposition = Depends [([("action", "onebox")], "oneboxer")
                                   ,([("action", "twobox")], "twoboxer")
                                   ]
          box_b          = Depends [([("prediction", "p1")], "full")
                                   ,([("prediction", "p2")], "empty")
                                   ]
          outcome        = Depends [([("action", "onebox"), ("box_b", "full" )], "1f")
                                   ,([("action", "twobox"), ("box_b", "full" )], "2f")
                                   ,([("action", "onebox"), ("box_b", "empty")], "1e")
                                   ,([("action", "twobox"), ("box_b", "empty")], "2e")
                                   ]
          value          = Depends [([("outcome", "1f")], "1000000")
                                   ,([("outcome", "2f")], "1001000")
                                   ,([("outcome", "1e")],       "0")
                                   ,([("outcome", "2e")],    "1000")
                                   ]

  data Probability = Probability (String, Float)
    deriving (Eq, Show)
  unProbability (Probability p) = p

  findG :: String -> Graph -> [Probability]
  findG l g@(Graph xs) = squash $ find' xs
    where find' []     = []
          find' (x:xs) = found x ++ (find' xs)
          found (s, n) | l == s    = case n of
                                       Distribution ds -> map Probability ds
                                       Depends      ds -> concatMap computeDependentProbabilities ds
                       | otherwise = []
          computeDependentProbabilities (gs,v) = probabilityForGuards 1.0 v gs
          probabilityForGuards 0 _ _          = []
          probabilityForGuards p v []         = [Probability (v, p)]
          probabilityForGuards p v ((n,e):gs) = probabilityForGuards (p * (sum $ map (probabilityForGuard e) $ findG n g)) v gs
          probabilityForGuard e (Probability (v, p)) | v == e    = p
                                                     | otherwise = 0.0
          squash = map sumProbabilities . groupBy ((==) `on` (fst.unProbability)) . sortOn (fst.unProbability)
          sumProbabilities ps@((Probability (v,_)):_) = Probability (v, sum $ map (snd.unProbability) ps)

  mapG :: ((String,Node) -> Node) -> Graph -> Graph
  mapG f (Graph [])     = Graph []
  mapG f (Graph (n:ns)) = Graph ((fst n, f n) : (unGraph $ mapG f (Graph ns)))

  intervene :: String -> String -> Graph -> Graph
  intervene l c g = mapG (\(s,n) -> if (s == l) then (Distribution [(c, 1.0)]) else n) g

  choices :: String -> Graph -> [String]
  choices l = map (fst.unProbability) . findG l


  bestChoice :: (String -> Float) -> String -> String -> Graph -> (String, Float)
  bestChoice uf a v g = maximumBy (comparing snd) $ map (\(c,g) -> (c, ev $ findG v g)) gs
    where gs = map (\c -> (c, intervene a c g)) $ choices a g
          ev = sum . map (\(Probability (v,p)) -> uf v * p)

  edtChoiceForNewcomb = bestChoice read "action" "value" newcomb
