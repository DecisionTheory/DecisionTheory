module DecisionTheory.Base where
  import GHC.Exts (IsString(fromString))
  import System.IO.Unsafe

  type Endo a = a -> a

  newtype Label = Label String
    deriving (Eq, Ord, Show)

  instance IsString Label where
    fromString = Label

  newtype State = State String
    deriving (Eq, Ord, Show)

  instance IsString State where
    fromString = State

  data Labeled a = Labeled Label a
    deriving (Eq, Show)

  instance Functor Labeled where
    fmap f (Labeled l a) = Labeled l (f a)

  tap l a = unsafePerformIO (print $ show l ++ show a) `seq` a
