{-# LANGUAGE StandaloneDeriving, DataKinds, TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts
           , MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, DeriveDataTypeable
  #-}

module DecisionTheory.TypedGraph where

  import Data.Data

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as U




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




  class Unboxed a where
    unboxed :: a -> String

  data Box a = Box a
    deriving (Eq, Show)
  unbox (Box a) = a

  class Stateable a where
    toState :: a -> State

  instance Data a => Stateable a where
    toState = State . showConstr . toConstr

  instance {-# OVERLAPS #-} Unboxed a => Stateable (Box a) where
    toState = State . unboxed . unbox

  class Labelable a where
    toLabel :: a -> Label

  instance Typeable a => Labelable a where
    toLabel = Label . tyConName . typeRepTyCon . typeOf

  instance {-# OVERLAPS #-} Labelable a => Labelable (Box a) where
    toLabel = toLabel . unbox




  class NodeValue a b | a -> b where
    nodeValue :: a -> b

  instance NodeValue (Graph (DistributionT a)) a where
    nodeValue (Distribution ps) = probabilityElement $ head $ ps 
  instance NodeValue (Graph (AlwaysT a)) a where
    nodeValue (Always a) = a
  instance NodeValue c a => NodeValue (Graph (ConditionalT c)) a where
    nodeValue (Case c) = nodeValue c
  instance (NodeValue (Graph a) c, NodeValue (Graph b) c) => NodeValue (Graph (AppendT a b)) c where
    nodeValue (a :*: _) = nodeValue a

  instance NodeValue (Clause (UnguardedT, v)) v where
    nodeValue (Otherwise v) = v
  instance (NodeValue (Clause (a, v)) v, NodeValue (Clause (b, v)) v) => NodeValue (Clause (DisjunctionT a b, v)) v where
    nodeValue (a :|: _) = nodeValue a
  instance NodeValue (Clause (GuardedT a, v)) v where
    nodeValue (When _ v) = v




  class Compilable a b | a -> b where
    compile :: a -> b

  instance (Labelable a, Stateable a) => Compilable (Graph (AlwaysT a)) (U.Graph U.Stochastic) where
    compile n@(Always a) = U.Graph [Labeled (toLabel $ nodeValue n) (U.Always $ toState a)]
  instance (Labelable a, Stateable a) => Compilable (Graph (DistributionT a)) (U.Graph U.Stochastic) where
    compile n@(Distribution ps) = U.Graph [Labeled (toLabel $ nodeValue n) (U.Distribution $ map (fmap toState) ps)]
  instance (NodeValue (Graph (ConditionalT c)) v, Labelable v, Compilable c [U.Clause]) => Compilable (Graph (ConditionalT c)) (U.Graph U.Stochastic) where
    compile n@(Case c) = U.Graph [Labeled (toLabel $ nodeValue n) (U.Conditional $ compile c)]
  instance (Compilable (Graph a) (U.Graph U.Stochastic), Compilable (Graph b) (U.Graph U.Stochastic)) => Compilable (Graph (AppendT a b)) (U.Graph U.Stochastic) where
    compile (a :*: b) = U.Graph ((U.unGraph . compile) a ++ (U.unGraph . compile) b)

  instance Stateable v => Compilable (Clause (UnguardedT, v)) [U.Clause] where
    compile (Otherwise v) = [U.Clause [] (toState v)]
  instance (Compilable (Clause (a, v)) [U.Clause], Compilable (Clause (b, v)) [U.Clause], Stateable v) => Compilable (Clause (DisjunctionT a b, v)) [U.Clause] where
    compile (a :|: b) = compile a ++ compile b
  instance (Compilable a [U.Guard], Stateable v) => Compilable (Clause (GuardedT a, v)) [U.Clause] where
    compile (When a v) = [U.Clause (compile a) (toState v)]

  instance (Labelable a, Stateable a) => Compilable (Guard (IsT a)) [U.Guard] where
    compile (Is a) = [U.Guard (toLabel a) (toState a)]
  instance (Compilable (Guard a) [U.Guard], Compilable (Guard b) [U.Guard]) => Compilable (Guard (AndT a b)) [U.Guard] where
    compile (a :&: b) = compile a ++ compile b
