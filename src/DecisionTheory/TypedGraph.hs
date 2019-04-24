{-# LANGUAGE StandaloneDeriving, DataKinds, TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts #-}

module DecisionTheory.TypedGraph where

  import DecisionTheory.Base
  import DecisionTheory.Probability




  data DistributionT a
  data ConditionalT a
  data AlwaysT a
  data AppendT a b

  data family Graph g
  data instance Graph (DistributionT a) = Distribution [Probability a]
  data instance Graph (ConditionalT a) = Case a
  data instance Graph (AlwaysT a) = Always a
  data instance Graph (AppendT a b) = Graph a :*: Graph b

  infixr 3 :*:

  instance Show a => Show (Graph (DistributionT a)) where
    show (Distribution ps) = "Distribution " ++ show ps
  instance Show a => Show (Graph (ConditionalT a)) where
    show (Case a) = "Case (" ++ show a ++ ")"
  instance Show a => Show (Graph (AlwaysT a)) where
    show (Always a) = "Always " ++ show a
  instance (Show (Graph a), Show (Graph b)) => Show (Graph (AppendT a b)) where
    show (a :*: b) = show a ++ " :*: " ++ show b




  data GuardedT a
  data UnguardedT
  data DisjunctionT a b

  data family Clause c
  data instance Clause (GuardedT a, v) = When a v
  data instance Clause (DisjunctionT a b, v) = Clause (a, v) :|: Clause (b, v)
  data instance Clause (UnguardedT, v) = Otherwise v

  infixr 5 :|:

  instance (Show a, Show v) => Show (Clause (GuardedT a, v)) where
    show (When a v) = "When (" ++ show a ++ ") " ++ show v
  instance (Show (Clause (a, v)), Show (Clause (b, v)), Show v) => Show (Clause (DisjunctionT a b, v)) where
    show (a :|: b) = show a ++ " :|: " ++ show b
  instance (Show v) => Show (Clause (UnguardedT, v)) where
    show (Otherwise v) = "Otherwise " ++ show v




  data IsT a
  data AndT a b

  data family Guard g
  data instance Guard (IsT a) = Is a
  data instance Guard (AndT a b) = Guard a :&: Guard b

  infixr 7 :&:

  instance Show a => Show (Guard (IsT a)) where
    show (Is a) = show a
  instance (Show (Guard a), Show (Guard b)) => Show (Guard (AndT a b)) where
    show (a :&: b) = show a ++ " :&: " ++ show b
