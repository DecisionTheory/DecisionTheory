{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- HLINT ignore "Redundant do" -}

module Newcomb (tests) where
  import Test.Hspec

  import Data.Data
  import Text.Read

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as UG
  import qualified DecisionTheory.DecisionTheory as U
  import qualified DecisionTheory.TypedGraph as TG
  import qualified DecisionTheory.TypedDecisionTheory as T
  import DecisionTheory.TypedGraph(distribution, choose, when, is, elsewise, (.*.), (.|.), (.&.))

  untypedNewcomb :: UG.Graph UG.Stochastic
  untypedNewcomb = UG.Graph [Labeled "Accuracy"       accuracy
                            ,Labeled "Predisposition" predisposition
                            ,Labeled "Action"         action
                            ,Labeled "Prediction"     prediction
                            ,Labeled "BoxB"           box_b
                            ,Labeled "Outcome"        outcome
                            ,Labeled "Value"          value
                            ]
    where predisposition = UG.Distribution ["Oneboxer" %= 0.5
                                           ,"Twoboxer" %= 0.5
                                           ]
          accuracy       = UG.Distribution [  "Accurate" %= 0.99
                                           ,"Inaccurate" %= 0.01
                                           ]
          action         = UG.Conditional [UG.Clause [UG.Guard "Predisposition" "Oneboxer"] "Onebox"
                                          ,UG.Clause [UG.Guard "Predisposition" "Twoboxer"] "Twobox"
                                          ]
          prediction     = UG.Conditional [UG.Clause [UG.Guard "Predisposition" "Oneboxer", UG.Guard "Accuracy"   "Accurate"] "P1"
                                          ,UG.Clause [UG.Guard "Predisposition" "Twoboxer", UG.Guard "Accuracy"   "Accurate"] "P2"
                                          ,UG.Clause [UG.Guard "Predisposition" "Oneboxer", UG.Guard "Accuracy" "Inaccurate"] "P2"
                                          ,UG.Clause [UG.Guard "Predisposition" "Twoboxer", UG.Guard "Accuracy" "Inaccurate"] "P1"
                                          ]
          box_b          = UG.Conditional [UG.Clause [UG.Guard "Prediction" "P1"] "Full"
                                          ,UG.Clause [UG.Guard "Prediction" "P2"] "Empty"
                                          ]
          outcome        = UG.Conditional [UG.Clause [UG.Guard "Action" "Onebox", UG.Guard "BoxB" "Full"]  "F1"
                                          ,UG.Clause [UG.Guard "Action" "Twobox", UG.Guard "BoxB" "Full"]  "F2"
                                          ,UG.Clause [UG.Guard "Action" "Onebox", UG.Guard "BoxB" "Empty"] "E1"
                                          ,UG.Clause [UG.Guard "Action" "Twobox", UG.Guard "BoxB" "Empty"] "E2"
                                          ]
          value          = UG.Conditional [UG.Clause [UG.Guard "Outcome" "F1"] "1000000"
                                          ,UG.Clause [UG.Guard "Outcome" "F2"] "1001000"
                                          ,UG.Clause [UG.Guard "Outcome" "E1"]       "0"
                                          ,UG.Clause [UG.Guard "Outcome" "E2"]    "1000"
                                          ]

  data Predisposition = Oneboxer | Twoboxer   deriving (Eq, Show, Typeable, Data)
  data Action         = Onebox   | Twobox     deriving (Eq, Show, Typeable, Data)
  data Accuracy       = Accurate | Inaccurate deriving (Eq, Show, Typeable, Data)
  data Prediction     = P1       | P2         deriving (Eq, Show, Typeable, Data)
  data BoxB           = Full     | Empty      deriving (Eq, Show, Typeable, Data)
  data Outcome        = F1 | F2  | E1 | E2    deriving (Eq, Show, Typeable, Data)
  newtype Value       = Value Int             deriving (Eq, Show, Typeable, Data)

  instance {-# OVERLAPPING #-} TG.Stateable Value where
    toState (Value n) = State $ show n
    ofState (State s) = Value <$> readMaybe s

  utilityFunction :: Value -> U.Utility
  utilityFunction (Value v) = fromIntegral v

  partial =
        distribution @Predisposition [Oneboxer %= 0.5
                                     ,Twoboxer %= 0.5
                                     ]
    .*. choose @Action     (when (is Oneboxer) Onebox
                        .|. when (is Twoboxer) Twobox)
    .*. choose @Prediction (when (is Oneboxer .&. is   Accurate) P1
                        .|. when (is Twoboxer .&. is   Accurate) P2
                        .|. when (is Oneboxer .&. is Inaccurate) P2
                        .|. when (is Twoboxer .&. is Inaccurate) P1)
    .*. choose @BoxB       (when (is P1)  Full
                        .|. when (is P2) Empty)
    .*. choose @Outcome    (when (is Onebox .&. is  Full) F1
                        .|. when (is Twobox .&. is  Full) F2
                        .|. when (is Onebox .&. is Empty) E1
                        .|. when (is Twobox .&. is Empty) E2)
    .*. choose @Value      (when (is F1) (Value 1000000)
                        .|. when (is F2) (Value 1001000)
                        .|. when (is E1) (Value       0)
                        .|. when (is E2) (Value    1000))
  newcomb =
        distribution @Accuracy [  Accurate %= 0.99
                               ,Inaccurate %= 0.01
                               ]
    .*. partial

  newcombOf t = t TG.true utilityFunction newcomb

  unreliableNewcomb =
        distribution @Accuracy [  Accurate %= 0.5
                               ,Inaccurate %= 0.5
                               ]
    .*. partial
  lessUnreliableNewcomb =
        distribution @Accuracy [  Accurate %= 0.51
                               ,Inaccurate %= 0.49
                               ]
    .*. partial

  tests :: IO ()
  tests = hspec $
    describe "Newcomb" $ do
      it "Newcomb allows one to onebox or twobox" $
        UG.choices "Action" (UG.branches untypedNewcomb) `shouldBe` ["Onebox", "Twobox"]
      it "Typed graph should compile to the untyped graph" $
        TG.compile newcomb `shouldBe` untypedNewcomb
      it "EDT chooses to onebox" $ newcombOf  T.edt                  `shouldBe` [(Onebox, 990000.0)]
      it "CDT chooses to twobox" $ newcombOf  T.cdt                  `shouldBe` [(Twobox,  11000.0)]
      it "FDT chooses to onebox" $ newcombOf (T.fdt @Predisposition) `shouldBe` [(Onebox, 990000.0)]
      it "FDT chooses to onebox even with transparency" $
        T.fdt @Predisposition (is Full) utilityFunction newcomb      `shouldBe` [(Onebox, 1000000.0)]
      it "FDT chooses to twobox when Omega prediction is unreliable" $
        T.fdt @Predisposition TG.true utilityFunction unreliableNewcomb      `shouldBe` [(Twobox, 501000.0)]
      it "FDT chooses to onebox when Omega prediction is less unreliable" $
        T.fdt @Predisposition TG.true utilityFunction lessUnreliableNewcomb  `shouldBe` [(Onebox, 510000.0)]
