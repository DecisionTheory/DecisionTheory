{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- HLINT ignore "Redundant do" -}

module Newcomb (tests) where

  import Test.Hspec

  import Data.Data
  import Text.Read

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as U
  import DecisionTheory.TypedGraph
  import DecisionTheory.DecisionTheory

  newcomb :: U.Graph U.Stochastic
  newcomb = U.Graph [Labeled "Predisposition" predisposition
                    ,Labeled "Accuracy"       accuracy
                    ,Labeled "Action"         action
                    ,Labeled "Prediction"     prediction
                    ,Labeled "BoxB"           box_b
                    ,Labeled "Outcome"        outcome
                    ,Labeled "Value"          value
                    ]
    where predisposition = U.Distribution [Probability "Oneboxer" 0.5
                                          ,Probability "Twoboxer" 0.5
                                          ]
          accuracy       = U.Distribution [Probability "Accurate"   0.99
                                          ,Probability "Inaccurate" 0.01
                                          ]
          action         = U.Conditional [U.Clause [U.Guard "Predisposition" "Oneboxer"] "Onebox"
                                         ,U.Clause [U.Guard "Predisposition" "Twoboxer"] "Twobox"
                                         ]
          prediction     = U.Conditional [U.Clause [U.Guard "Predisposition" "Oneboxer", U.Guard "Accuracy" "Accurate"]   "P1"
                                         ,U.Clause [U.Guard "Predisposition" "Twoboxer", U.Guard "Accuracy" "Accurate"]   "P2"
                                         ,U.Clause [U.Guard "Predisposition" "Oneboxer", U.Guard "Accuracy" "Inaccurate"] "P2"
                                         ,U.Clause [U.Guard "Predisposition" "Twoboxer", U.Guard "Accuracy" "Inaccurate"] "P1"
                                         ]
          box_b          = U.Conditional [U.Clause [U.Guard "Prediction" "P1"] "Full"
                                         ,U.Clause [U.Guard "Prediction" "P2"] "Empty"
                                         ]
          outcome        = U.Conditional [U.Clause [U.Guard "Action" "Onebox", U.Guard "BoxB" "Full"]  "F1"
                                         ,U.Clause [U.Guard "Action" "Twobox", U.Guard "BoxB" "Full"]  "F2"
                                         ,U.Clause [U.Guard "Action" "Onebox", U.Guard "BoxB" "Empty"] "E1"
                                         ,U.Clause [U.Guard "Action" "Twobox", U.Guard "BoxB" "Empty"] "E2"
                                         ]
          value          = U.Conditional [U.Clause [U.Guard "Outcome" "F1"] "1000000"
                                         ,U.Clause [U.Guard "Outcome" "F2"] "1001000"
                                         ,U.Clause [U.Guard "Outcome" "E1"]       "0"
                                         ,U.Clause [U.Guard "Outcome" "E2"]    "1000"
                                         ]

  data Predisposition = Oneboxer | Twoboxer   deriving (Eq, Show, Typeable, Data)
  data Action         = Onebox   | Twobox     deriving (Eq, Show, Typeable, Data)
  data Accuracy       = Accurate | Inaccurate deriving (Eq, Show, Typeable, Data)
  data Prediction     = P1       | P2         deriving (Eq, Show, Typeable, Data)
  data BoxB           = Full     | Empty      deriving (Eq, Show, Typeable, Data)
  data Outcome        = F1 | F2  | E1 | E2    deriving (Eq, Show, Typeable, Data)
  newtype Value       = Value Int             deriving (Eq, Show, Typeable, Data)

  instance {-# OVERLAPPING #-} Stateable Value where
    toState (Value n) = State $ show n
    ofState (State s) = Value <$> readMaybe s

  typedNewcomb =
        Distribution [Oneboxer %= 0.5
                     ,Twoboxer %= 0.5
                     ]
    :*: Distribution [  Accurate %= 0.99
                     ,Inaccurate %= 0.01
                     ]
    :*: Case (When (Is Oneboxer) Onebox
          :|: When (Is Twoboxer) Twobox)
    :*: Case (When (Is Oneboxer :&: Is   Accurate) P1
          :|: When (Is Twoboxer :&: Is   Accurate) P2
          :|: When (Is Oneboxer :&: Is Inaccurate) P2
          :|: When (Is Twoboxer :&: Is Inaccurate) P1)
    :*: Case (When (Is P1)  Full
          :|: When (Is P2) Empty)
    :*: Case (When (Is Onebox :&: Is  Full) F1
          :|: When (Is Twobox :&: Is  Full) F2
          :|: When (Is Onebox :&: Is Empty) E1
          :|: When (Is Twobox :&: Is Empty) E2)
    :*: Case (When (Is F1) (Value 1000000)
          :|: When (Is F2) (Value 1001000)
          :|: When (Is E1) (Value       0)
          :|: When (Is E2) (Value    1000))

  newcombOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  newcombOf t = t [] stdSearch newcomb

  unreliableNewcomb :: U.Graph U.Stochastic
  unreliableNewcomb = U.replaceG unreliability newcomb
    where unreliability ln@(Labeled l _) | l == "Accuracy" = Labeled l $ U.Distribution [Probability "Accurate"   0.5
                                                                                        ,Probability "Inaccurate" 0.5
                                                                                        ]
                                         | otherwise       = ln

  lessUnreliableNewcomb :: U.Graph U.Stochastic
  lessUnreliableNewcomb = U.replaceG lesserUnreliability newcomb
    where lesserUnreliability ln@(Labeled l _) | l == "Accuracy" = Labeled l $ U.Distribution [Probability "Accurate"   0.51
                                                                                              ,Probability "Inaccurate" 0.49
                                                                                              ]
                                               | otherwise       = ln

  tests :: IO ()
  tests = hspec $ do
    describe "Newcomb" $ do
      it "Newcomb allows one to onebox or twobox" $ do
        U.choices "Action" (U.branches newcomb) `shouldBe` ["Onebox", "Twobox"]
      it "EDT chooses to onebox" $ do
        newcombOf edt `shouldBe` ("Onebox", 990000.0)
      it "CDT chooses to twobox" $ do
        newcombOf cdt `shouldBe` ("Twobox", 11000.0)
      it "FDT chooses to onebox" $ do
        newcombOf (fdt "Predisposition") `shouldBe` ("Onebox", 990000.0)
      it "FDT chooses to onebox even with transparency" $ do
        fdt "Predisposition" [U.Guard "BoxB" "Full"] stdSearch newcomb `shouldBe` ("Onebox", 1000000.0)
      it "FDT chooses to twobox when Omega prediction is unreliable" $ do
        fdt "Predisposition" [] stdSearch unreliableNewcomb `shouldBe` ("Twobox",501000.0)
      it "FDT chooses to onebox when Omega prediction is less unreliable" $ do
        fdt "Predisposition" [] stdSearch lessUnreliableNewcomb `shouldBe` ("Onebox",510000.0)
      it "Typed graph should compile to the untyped graph" $ do
        compile typedNewcomb `shouldBe` newcomb
