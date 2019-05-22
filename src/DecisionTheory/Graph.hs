{-# LANGUAGE EmptyDataDecls, GADTs, StandaloneDeriving #-}

module DecisionTheory.Graph where

  import qualified Data.List as L
  import qualified Data.Maybe as M

  import DecisionTheory.Base
  import DecisionTheory.Probability

  data Stochastic
  data Deterministic

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

  dot :: String -> Graph a -> String
  dot s (Graph lns) = "digraph " ++ s ++ " {\r\n" ++ nodes ++ "}\r\n"
    where nodes = foldr (++) "" $ map prettyPrint lns
          prettyPrint (Labeled (Label l) n) = describe l n ++ "\r\n"
          describe l (Conditional cs) = foldr (++) "" $ map (\k -> k ++ " -> " ++ l ++ ";\r\n") $ clauses cs
          describe l _                = l
          clauses = L.nub . L.sort . concatMap (\(Clause gs _) -> guards gs)
          guards  = L.nub . L.sort . map (\(Guard (Label n) _) -> n)

  find :: Label -> Graph Deterministic -> Maybe State
  find l g@(Graph lns) = resolve =<< getByLabel lns
    where getByLabel :: [Labeled (Node a)] -> Maybe (Node a)
          getByLabel [] = Nothing
          getByLabel ((Labeled l' n):lns) | l' == l = Just n
                                          | otherwise = getByLabel lns
          resolve :: Node Deterministic -> Maybe State
          resolve (Always v) = Just v
          resolve (Conditional cs) = fmap (clauseValue.fst) $ L.uncons $ filter clauseMatches cs
          clauseMatches :: Clause -> Bool
          clauseMatches (Clause gs _) = all guardMatches gs
          guardMatches (Guard l' v) = find l' g == Just v

  probabilities :: Label -> [Probability (Graph Deterministic)] -> [Probability State]
  probabilities l = squash (when (==)) . M.catMaybes . map find'
    where find' (Probability g p) = fmap (flip Probability p) (find l g)
          when :: (a -> a -> Bool) -> (a -> a -> Maybe a)
          when (==) a1 a2 | a1 == a2  = Just a1
                          | otherwise = Nothing

  choices :: Label -> [Probability (Graph Deterministic)] -> [State]
  choices l = map probabilityElement . probabilities l

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


  mapBranches :: Endo (Labeled (Node a)) -> Endo (Probability (Graph a))
  mapBranches f = fmap (\(Graph lns) -> Graph (map f lns))

  replaceG :: Endo (Labeled (Node a)) -> Endo (Graph a)
  replaceG f (Graph lns) = Graph $ map f lns
