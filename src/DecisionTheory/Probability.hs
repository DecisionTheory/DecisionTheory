module DecisionTheory.Probability
  ( Probability ()
  , unProbability
  , probabilityElement
  , probabilityValue
  , (%=)
  , squash
  , normalize
  ) where

  import qualified Data.List as L

  import DecisionTheory.Base

  data Probability a = Probability a Rational
    deriving (Eq, Show)

  unProbability :: Probability a -> (a, Rational)
  unProbability (Probability a r) = (a, r)

  probabilityElement :: Probability a -> a
  probabilityElement (Probability a _) = a

  probabilityValue :: Probability a -> Rational
  probabilityValue (Probability _ r) = r

  (%=) :: a -> Rational -> Probability a
  (%=) = Probability

  prior :: Rational -> Probability ()
  prior = Probability ()

  instance Functor Probability where
    fmap f (Probability e v) = Probability (f e) v

  instance Applicative Probability where
    pure a = Probability a 1
    (Probability f x) <*> (Probability a y) = Probability (f a) (x * y)

  instance Monad Probability where
    (Probability a x) >>= k = let Probability b y = k a in Probability b (x * y)

  squash :: Ord a => (a -> a -> Maybe a) -> Endo [Probability a]
  squash (>+<) = squash' . L.sortOn unProbability
    where squash' (p1:p2:ps) = case merge p1 p2 of
                                 Nothing -> p1:squash' (p2:ps)
                                 Just p3 ->    squash' (p3:ps)
          squash' ps         = ps
          merge (Probability a x) (Probability b y) = fmap (flip Probability (x+y)) (a >+< b)

  normalize :: Endo [Probability a]
  normalize ps = normalize' (sum (map probabilityValue ps)) ps
    where normalize' _ []     = []
          normalize' t (p:ps) = (prior (1/t) >> p) : normalize' t ps
