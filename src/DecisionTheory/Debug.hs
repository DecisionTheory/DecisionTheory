module DecisionTheory.Debug
  ( tap
  ) where

  import System.IO.Unsafe ( unsafePerformIO )

  tap :: (Show l, Show a) => l -> a -> a
  tap l a = unsafePerformIO (print $ show l ++ show a) `seq` a
