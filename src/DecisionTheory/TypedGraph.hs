{-# LANGUAGE DataKinds, TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts
           , MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, GADTs
           , ScopedTypeVariables
  #-}

module DecisionTheory.TypedGraph where

  import Data.Data

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as U




  type family Delete a b where
    Delete a '[] = '[]
    Delete a (a ': t) = Delete a t
    Delete a (h ': t) = h ': Delete a t

  type family Nub (as :: [*]) where
    Nub    '[]    = '[]
    Nub (x ': xs) = x ': Delete x (Nub xs)

  type family Union a b where
    Union '[]        bs       = bs
    Union  as       '[]       = as
    Union (a ': as) (a ': bs) = a      ': Union (Delete a as) (Delete a bs)
    Union (a ': as) (b ': bs) = a ': b ': Union (Delete b as) (Delete a bs)

  type family Difference as bs where
    Difference as '[] = as
    Difference '[] bs = '[]
    Difference as (b ': bs) = Difference (Delete b as) bs

  type family Intersection as bs where
    Intersection as bs = (Difference (Union as bs) (Union (Difference as bs) (Difference bs as)))

  class IsEmpty (e :: [*])
  instance IsEmpty '[]

  newtype E (i :: [*]) (o :: [*]) a = E a

  instance Eq a => Eq (E i o a) where
    (E a) == (E b) = a == b
  instance Show a => Show (E i o a) where
    show (E a) = show a




  data TrueT
  data IsT a
  data AndT a b

  data Guard :: * -> * where
    GTrue :: Guard TrueT
    Is :: a -> Guard (IsT a)
    (:&:) :: Guard a -> Guard b -> Guard (AndT a b)
  infixr 7 :&:

  instance Eq (Guard TrueT) where
    _ == _  = True
  instance Eq a => Eq (Guard (IsT a)) where
    Is a    == Is b    = a == b
  instance (Eq (Guard a), Eq (Guard b)) => Eq (Guard (AndT a b)) where
    (a :&: b) == (c :&: d) = a == c && b == d
  instance Show (Guard TrueT) where
    show (GTrue) = "true"
  instance Show a => Show (Guard (IsT a)) where
    show (Is a) = show a
  instance (Show (Guard a), Show (Guard b)) => Show (Guard (AndT a b)) where
    show (a :&: b) = show a ++ " .&. " ++ show b

  true :: E '[] '[] (Guard TrueT)
  true = E GTrue

  is :: a -> E '[a] '[] (Guard (IsT a))
  is a = E (Is a)

  class And a b c | a b -> c where
    (.&.) :: E ia '[] (Guard a) -> E ib '[] (Guard b) -> E (Union ia ib) '[] (Guard c)
  infixr 7 .&.

  instance And TrueT b b where
    (E GTrue) .&. (E b) = E b

  instance And a TrueT a where
    (E a) .&. (E GTrue) = E a

  instance And (IsT a) (IsT b) (AndT (IsT a) (IsT b)) where
    (E a) .&. (E b) = E (a :&: b)

  instance And (IsT a) (AndT b c) (AndT (IsT a) (AndT b c)) where
    (E a) .&. (E b) = E (a :&: b)




  data GuardedT a
  data UnguardedT
  data DisjunctionT a b

  data Clause :: * -> * -> * where
    When      ::    Guard g ->          o -> Clause (GuardedT     g)   o
    (:|:)     :: Clause c o -> Clause d o -> Clause (DisjunctionT c d) o
    Otherwise ::                        o -> Clause  UnguardedT        o

  instance (Eq (Guard g), Eq o) => Eq (Clause (GuardedT g) o) where
    (When c a) == (When d b) = (c == d) && (a == b)
  instance (Eq (Clause c o), Eq (Clause d o)) => Eq (Clause (DisjunctionT c d) o) where
    (a :|: b) == (c :|: d) = (a == c) && (b == d)
  instance Eq o => Eq (Clause UnguardedT o) where
    Otherwise a == Otherwise b = a == b
  instance (Show (Guard g), Show o) => Show (Clause (GuardedT g) o) where
    show (When c o) = "when (" ++ show c ++ ") " ++ show o
  instance (Show (Clause c o), Show (Clause d o), Show o) => Show (Clause (DisjunctionT c d) o) where
    show (a :|: b) = show a ++ " .|. " ++ show b
  instance (Show o) => Show (Clause UnguardedT o) where
    show (Otherwise o) = "fallback " ++ show o

  class NoCircularity (io :: [*])
  instance NoCircularity '[]

  when :: NoCircularity (Intersection i '[o]) => E i '[] (Guard g) -> o -> E i '[o] (Clause (GuardedT g) o)
  when (E g) o = E (When g o)

  (.|.) :: E i '[o] (Clause c o) -> E j '[o] (Clause d o) -> E (Union i j) '[o] (Clause (DisjunctionT c d) o)
  infixr 5 .|.
  E c .|. E d = E (c :|: d)

  fallback :: o -> E '[] '[o] (Clause UnguardedT o)
  fallback a = E (Otherwise a)




  data DistributionT a
  data ConditionalT a
  data AlwaysT a
  data AppendT a b

  data Graph :: * -> * where
    Distribution :: [Probability o] -> Graph (DistributionT o)
    Case :: Clause c o -> Graph (ConditionalT (Clause c o))
    Always :: o -> Graph (AlwaysT o)
    (:*:) :: Graph g -> Graph h -> Graph (AppendT g h)
  infixr 3 :*:

  instance Show o => Show (Graph (DistributionT o)) where
    show (Distribution ps) = "distribution " ++ show ps
  instance Show (Clause c o) => Show (Graph (ConditionalT (Clause c o))) where
    show (Case a) = "depends (" ++ show a ++ ")"
  instance Show o => Show (Graph (AlwaysT o)) where
    show (Always a) = "always " ++ show a
  instance (Show (Graph a), Show (Graph b)) => Show (Graph (AppendT a b)) where
    show (a :*: b) = show a ++ " .*. " ++ show b

  instance Eq o => Eq (Graph (DistributionT o)) where
    Distribution o == Distribution p = o == p
  instance Eq o => Eq (Graph (AlwaysT o)) where
    Always o == Always p = o == p
  instance Eq c => Eq (Graph (ConditionalT c)) where
    Case c == Case d = c == d
  instance (Eq (Graph g), Eq (Graph h)) => Eq (Graph (AppendT g h)) where
    (a :*: b) == (c :*: d) = (a == c) && (b == d)

  distribution :: [Probability o] -> E '[] '[o] (Graph (DistributionT o))
  distribution ps = E (Distribution ps)

  always :: o -> E '[] '[o] (Graph (AlwaysT o))
  always o = E (Always o)

  depends :: E i '[o] (Clause c o) -> E i '[o] (Graph (ConditionalT (Clause c o)))
  depends (E c) = E (Case c)

  class NoDuplicatedOutputs (o :: [*])
  instance NoDuplicatedOutputs '[]

  class OutputShouldPrecedeInput (o :: [*])
  instance OutputShouldPrecedeInput '[]

  (.*.) :: (NoDuplicatedOutputs (Intersection '[o] p), OutputShouldPrecedeInput (Intersection i p)) => E i '[o] (Graph g) -> E j p (Graph h) -> E (Union i (Difference j '[o])) (Union '[o] p)  (Graph (AppendT g h))
  infixr 3 .*.
  E g .*. E h = E (g :*: h)




  class Stateable a where
    toState :: a -> State
    ofState :: State -> Maybe a


  instance {-# OVERLAPPABLE #-} forall a. Data a => Stateable a where
    toState = State . showConstr . toConstr
    ofState (State s) = (fromConstr <$> readConstr (dataTypeOf (undefined :: a)) s)

  class Labelable a where
    toLabel :: a -> Label

  instance {-# OVERLAPPABLE #-} Typeable a => Labelable a where
    toLabel = Label . tyConName . typeRepTyCon . typeOf




  class NodeValue a b | a -> b where
    nodeValue :: a -> b

  instance NodeValue (Graph (DistributionT a)) a where
    nodeValue (Distribution ps) = probabilityElement . head $ ps
  instance NodeValue (Graph  (AlwaysT a)) a where
    nodeValue (Always a) = a
  instance NodeValue (Clause c a) a => NodeValue (Graph (ConditionalT (Clause c a))) a where
    nodeValue (Case c) = nodeValue c
  instance (NodeValue (Graph a) c, NodeValue (Graph b) c) => NodeValue (Graph (AppendT a b)) c where
    nodeValue (a :*: _) = nodeValue a

  instance NodeValue (Clause UnguardedT v) v where
    nodeValue (Otherwise v) = v
  instance (NodeValue (Clause a v) v, NodeValue (Clause b v) v) => NodeValue (Clause (DisjunctionT a b) v) v where
    nodeValue (a :|: _) = nodeValue a
  instance NodeValue (Clause (GuardedT a) v) v where
    nodeValue (When _ v) = v




  class Compilable a b | a -> b where
    compile :: a -> b

  instance (Labelable a, Stateable a) => Compilable (Graph (AlwaysT a)) (U.Graph U.Stochastic) where
    compile n@(Always a) = U.Graph [Labeled (toLabel $ nodeValue n) (U.Always $ toState a)]
  instance (Labelable a, Stateable a) => Compilable (Graph (DistributionT a)) (U.Graph U.Stochastic) where
    compile n@(Distribution ps) = U.Graph [Labeled (toLabel $ nodeValue n) (U.Distribution $ map (fmap toState) ps)]
  instance (NodeValue (Clause c a) a, Labelable a, Compilable (Clause c a) [U.Clause]) => Compilable (Graph (ConditionalT (Clause c a))) (U.Graph U.Stochastic) where
    compile n@(Case c) = U.Graph [Labeled (toLabel $ nodeValue n) (U.Conditional $ compile c)]
  instance (Compilable (Graph a) (U.Graph U.Stochastic), Compilable (Graph b) (U.Graph U.Stochastic)) => Compilable (Graph (AppendT a b)) (U.Graph U.Stochastic) where
    compile (a :*: b) = U.Graph ((U.unGraph . compile) a ++ (U.unGraph . compile) b)

  instance Stateable v => Compilable (Clause UnguardedT v) [U.Clause] where
    compile (Otherwise v) = [U.Clause [] (toState v)]
  instance (Compilable (Clause a v) [U.Clause], Compilable (Clause b v) [U.Clause], Stateable v) => Compilable (Clause (DisjunctionT a b) v) [U.Clause] where
    compile (a :|: b) = compile a ++ compile b
  instance (Compilable (Guard g) [U.Guard], Stateable v) => Compilable (Clause (GuardedT g) v) [U.Clause] where
    compile (When a v) = [U.Clause (compile a) (toState v)]

  instance Compilable (Guard TrueT) [U.Guard] where
    compile (GTrue) = []
  instance (Labelable a, Stateable a) => Compilable (Guard (IsT a)) [U.Guard] where
    compile (Is a) = [U.Guard (toLabel a) (toState a)]
  instance (Compilable (Guard a) [U.Guard], Compilable (Guard b) [U.Guard]) => Compilable (Guard (AndT a b)) [U.Guard] where
    compile (a :&: b) = compile a ++ compile b


  class AllInputsSatisfied (i :: [*])
  instance AllInputsSatisfied '[]

  instance (AllInputsSatisfied i, Compilable (Graph g) (U.Graph U.Stochastic)) => Compilable (E i o (Graph g)) (U.Graph U.Stochastic) where
    compile (E g) = compile g

  instance (Compilable (Guard g) [U.Guard]) => Compilable (E i o (Guard g)) [U.Guard] where
    compile (E g) = compile g
