{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{- HLINT ignore "Redundant do" -}

module V2.Newcomb where

import Data.Data (Data)
import DecisionTheory.Base (Labeled (Labeled))
import DecisionTheory.DecisionTheory (Utility)
import qualified DecisionTheory.Graph as UG
import DecisionTheory.Probability ((%=))
import DecisionTheory.V2.HList (hAsSingle, hAsTuple, hFromSingle)
import DecisionTheory.V2.Stringify (AsLabel, AsState, Datally (..), Showly (..))
import qualified DecisionTheory.V2.TypedDecisionTheory as TypedDT
import DecisionTheory.V2.TypedGraph (choose, distribution, (.*.))
import qualified DecisionTheory.V2.TypedGraph as TG
import Test.Hspec (describe, hspec, it, shouldBe)

untypedNewcomb :: UG.Graph 'UG.Stochastic
untypedNewcomb =
  UG.Graph
    [ Labeled "Accuracy" accuracy,
      Labeled "Predisposition" predisposition,
      Labeled "Action" action,
      Labeled "Prediction" prediction,
      Labeled "BoxB" box_b,
      Labeled "Outcome" outcome,
      Labeled "Value" value
    ]
  where
    predisposition =
      UG.Distribution
        [ "Oneboxer" %= 0.5,
          "Twoboxer" %= 0.5
        ]
    accuracy =
      UG.Distribution
        [ "Accurate" %= 0.99,
          "Inaccurate" %= 0.01
        ]
    action =
      UG.Conditional
        [ UG.Clause [UG.Guard "Predisposition" "Oneboxer"] "Onebox",
          UG.Clause [UG.Guard "Predisposition" "Twoboxer"] "Twobox"
        ]
    prediction =
      UG.Conditional
        [ UG.Clause [UG.Guard "Predisposition" "Oneboxer", UG.Guard "Accuracy" "Accurate"] "P1",
          UG.Clause [UG.Guard "Predisposition" "Oneboxer", UG.Guard "Accuracy" "Inaccurate"] "P2",
          UG.Clause [UG.Guard "Predisposition" "Twoboxer", UG.Guard "Accuracy" "Accurate"] "P2",
          UG.Clause [UG.Guard "Predisposition" "Twoboxer", UG.Guard "Accuracy" "Inaccurate"] "P1"
        ]
    box_b =
      UG.Conditional
        [ UG.Clause [UG.Guard "Prediction" "P1"] "Full",
          UG.Clause [UG.Guard "Prediction" "P2"] "Empty"
        ]
    outcome =
      UG.Conditional
        [ UG.Clause [UG.Guard "Action" "Onebox", UG.Guard "BoxB" "Full"] "F1",
          UG.Clause [UG.Guard "Action" "Onebox", UG.Guard "BoxB" "Empty"] "E1",
          UG.Clause [UG.Guard "Action" "Twobox", UG.Guard "BoxB" "Full"] "F2",
          UG.Clause [UG.Guard "Action" "Twobox", UG.Guard "BoxB" "Empty"] "E2"
        ]
    value =
      UG.Conditional
        [ UG.Clause [UG.Guard "Outcome" "F1"] "1000000",
          UG.Clause [UG.Guard "Outcome" "F2"] "1001000",
          UG.Clause [UG.Guard "Outcome" "E1"] "0",
          UG.Clause [UG.Guard "Outcome" "E2"] "1000"
        ]

data Predisposition = Oneboxer | Twoboxer
  deriving (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Predisposition)

data Action = Onebox | Twobox
  deriving (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Action)

data Accuracy = Accurate | Inaccurate
  deriving (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Accuracy)

data Prediction = P1 | P2
  deriving (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Prediction)

data BoxB = Full | Empty
  deriving (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally BoxB)

data Outcome = F1 | F2 | E1 | E2
  deriving (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Outcome)

newtype Value = Value Int
  deriving stock (Eq, Show, Data)
  deriving newtype (Enum, Bounded)
  deriving (AsLabel) via (Datally Value)
  deriving (AsState) via (Showly Int)

utilityFunction :: Value -> Utility
utilityFunction (Value v) = fromIntegral v

partial :: TG.Graph 'UG.Stochastic _
partial =
  distribution @Predisposition
    [ Oneboxer %= 0.5,
      Twoboxer %= 0.5
    ]
    .*. choose
      ( hAsSingle $ \case
          Oneboxer -> Onebox
          Twoboxer -> Twobox
      )
    .*. choose
      ( hAsTuple $ \case
          (Oneboxer, Accurate) -> P1
          (Twoboxer, Accurate) -> P2
          (Oneboxer, Inaccurate) -> P2
          (Twoboxer, Inaccurate) -> P1
      )
    .*. choose
      ( hAsSingle $ \case
          P1 -> Full
          P2 -> Empty
      )
    .*. choose
      ( hAsTuple $ \case
          (Onebox, Full) -> F1
          (Twobox, Full) -> F2
          (Onebox, Empty) -> E1
          (Twobox, Empty) -> E2
      )
    .*. choose
      ( hAsSingle $ \case
          F1 -> Value 1000000
          F2 -> Value 1001000
          E1 -> Value 0
          E2 -> Value 1000
      )

newcomb :: TG.Graph 'UG.Stochastic _
newcomb =
  distribution @Accuracy
    [ Accurate %= 0.99,
      Inaccurate %= 0.01
    ]
    .*. partial

newcombOf :: TypedDT.DecisionTheory _ '[] action Value -> TypedDT.Solutions action
newcombOf t = t TG.HNil utilityFunction newcomb

unreliableNewcomb :: TG.Graph 'UG.Stochastic _
unreliableNewcomb =
  distribution @Accuracy
    [ Accurate %= 0.5,
      Inaccurate %= 0.5
    ]
    .*. partial

lessUnreliableNewcomb :: TG.Graph 'UG.Stochastic _
lessUnreliableNewcomb =
  distribution @Accuracy
    [ Accurate %= 0.51,
      Inaccurate %= 0.49
    ]
    .*. partial

tests :: IO ()
tests = hspec $
  describe "Newcomb" $ do
    it "Newcomb allows one to onebox or twobox" $
      UG.choices "Action" (UG.branches untypedNewcomb) `shouldBe` ["Onebox", "Twobox"]
    it "Typed graph should compile to the untyped graph" $
      TG.compile newcomb `shouldBe` untypedNewcomb
    it "EDT chooses to onebox" $ newcombOf TypedDT.edt `shouldBe` [(Onebox, 990000.0)]
    it "CDT chooses to twobox" $ newcombOf TypedDT.cdt `shouldBe` [(Twobox, 11000.0)]
    it "FDT chooses to onebox" $ newcombOf (TypedDT.fdt @Predisposition) `shouldBe` [(Onebox, 990000.0)]
    it "FDT chooses to onebox even with transparency" $
      TypedDT.fdt @Predisposition (hFromSingle Full) utilityFunction newcomb `shouldBe` [(Onebox, 1000000.0)]
    it "FDT chooses to twobox when Omega prediction is unreliable" $
      TypedDT.fdt @Predisposition TG.HNil utilityFunction unreliableNewcomb `shouldBe` [(Twobox, 501000.0)]
    it "FDT chooses to onebox when Omega prediction is less unreliable" $
      TypedDT.fdt @Predisposition TG.HNil utilityFunction lessUnreliableNewcomb `shouldBe` [(Onebox, 510000.0)]
