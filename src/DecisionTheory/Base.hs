module DecisionTheory.Base where
  import GHC.Exts (IsString(fromString))

  type Endo a = a -> a

  newtype Label = Label String
    deriving (Eq, Ord, Show)

  instance IsString Label where
    fromString = Label

  newtype State = State String
    deriving (Eq, Ord, Show)

  instance IsString State where
    fromString = State
