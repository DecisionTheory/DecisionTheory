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

module V2.ParfitsHitchhiker where

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

untypedParfitsHitchhiker :: UG.Graph 'UG.Stochastic
untypedParfitsHitchhiker =
  UG.Graph
    [ Labeled "Predisposition" predisposition,
      Labeled "Accuracy" accuracy,
      Labeled "Offer" offer,
      Labeled "Location" location,
      Labeled "Action" action,
      Labeled "Value" value
    ]
  where
    predisposition =
      UG.Distribution
        [ "Trustworthy" %= 0.5,
          "Untrustworthy" %= 0.5
        ]
    accuracy =
      UG.Distribution
        [ "Accurate" %= 0.99,
          "Inaccurate" %= 0.01
        ]
    offer =
      UG.Conditional
        [ UG.Clause [UG.Guard "Predisposition" "Trustworthy", UG.Guard "Accuracy" "Accurate"] "Ride",
          UG.Clause [UG.Guard "Predisposition" "Trustworthy", UG.Guard "Accuracy" "Inaccurate"] "NoRide",
          UG.Clause [UG.Guard "Predisposition" "Untrustworthy", UG.Guard "Accuracy" "Accurate"] "NoRide",
          UG.Clause [UG.Guard "Predisposition" "Untrustworthy", UG.Guard "Accuracy" "Inaccurate"] "Ride"
        ]
    location =
      UG.Conditional
        [ UG.Clause [UG.Guard "Offer" "Ride"] "City",
          UG.Clause [UG.Guard "Offer" "NoRide"] "Desert"
        ]
    action =
      UG.Conditional
        [ UG.Clause [UG.Guard "Predisposition" "Trustworthy", UG.Guard "Location" "City"] "Pay",
          UG.Clause [UG.Guard "Predisposition" "Trustworthy", UG.Guard "Location" "Desert"] "NoPay",
          UG.Clause [UG.Guard "Predisposition" "Untrustworthy", UG.Guard "Location" "City"] "NoPay",
          UG.Clause [UG.Guard "Predisposition" "Untrustworthy", UG.Guard "Location" "Desert"] "NoPay"
        ]
    value =
      UG.Conditional
        [ UG.Clause [UG.Guard "Action" "Pay", UG.Guard "Location" "City"] "-1000",
          UG.Clause [UG.Guard "Action" "Pay", UG.Guard "Location" "Desert"] "-1000000",
          UG.Clause [UG.Guard "Action" "NoPay", UG.Guard "Location" "City"] "0",
          UG.Clause [UG.Guard "Action" "NoPay", UG.Guard "Location" "Desert"] "-1000000"
        ]

data Predisposition = Trustworthy | Untrustworthy
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Predisposition)

data Accuracy = Accurate | Inaccurate
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Accuracy)

data Location = City | Desert
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Location)

data Action = Pay | NoPay
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Action)

data Offer = Ride | NoRide
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Offer)

newtype Value = Value Int
  deriving stock (Eq, Show, Data)
  deriving newtype (Bounded, Enum)
  deriving (AsLabel) via (Datally Value)
  deriving (AsState) via (Showly Int)

utilityFunction :: Value -> Utility
utilityFunction (Value v) = fromIntegral v

parfitsHitchhiker :: TG.Graph 'UG.Stochastic _
parfitsHitchhiker =
  distribution
    [ Trustworthy %= 0.5,
      Untrustworthy %= 0.5
    ]
    .*. distribution
      [ Accurate %= 0.99,
        Inaccurate %= 0.01
      ]
    .*. choose
      ( hAsTuple $ \case
          (Trustworthy, Accurate) -> Ride
          (Trustworthy, Inaccurate) -> NoRide
          (Untrustworthy, Accurate) -> NoRide
          (Untrustworthy, Inaccurate) -> Ride
      )
    .*. choose
      ( hAsSingle $ \case
          Ride -> City
          NoRide -> Desert
      )
    .*. choose
      ( hAsTuple $ \case
          (Trustworthy, City) -> Pay
          _ -> NoPay
      )
    .*. choose
      ( hAsTuple $ \case
          (Pay, City) -> Value $ -1000
          (NoPay, City) -> Value 0
          _ -> Value $ -1000000
      )

parfitsHitchhikerOf :: TypedDT.DecisionTheory _ '[] action Value -> TypedDT.Solutions action
parfitsHitchhikerOf t = t TG.HNil utilityFunction parfitsHitchhiker

parfitsHitchhikerInTheCityOf :: TypedDT.DecisionTheory _ '[Location] action Value -> TypedDT.Solutions action
parfitsHitchhikerInTheCityOf t = t (hFromSingle City) utilityFunction parfitsHitchhiker

tests :: IO ()
tests = hspec $
  describe "Parfit's Hitchhiker" $ do
    it "Parfit's Hitchhiker allows one to pay or no pay" $
      UG.choices "Action" (UG.branches untypedParfitsHitchhiker) `shouldBe` ["NoPay", "Pay"]
    it "Typed graph should compile to the untyped graph" $
      TG.compile parfitsHitchhiker `shouldBe` untypedParfitsHitchhiker
    it "EDT initially chooses to pay" $ parfitsHitchhikerOf TypedDT.edt `shouldBe` [(Pay, -1000.0)]
    it "EDT later chooses to no pay" $ parfitsHitchhikerInTheCityOf TypedDT.edt `shouldBe` [(NoPay, 0.0)]
    it "CDT initially chooses to no pay" $ parfitsHitchhikerOf TypedDT.cdt `shouldBe` [(NoPay, -990099.0)]
    it "CDT later still chooses to no pay" $ parfitsHitchhikerInTheCityOf TypedDT.cdt `shouldBe` [(NoPay, 0.0)]
    it "FDT initially chooses to pay" $ parfitsHitchhikerOf (TypedDT.fdt @Predisposition) `shouldBe` [(Pay, -1000.0)]
    it "FDT later still chooses to pay" $ parfitsHitchhikerInTheCityOf (TypedDT.fdt @Predisposition) `shouldBe` [(Pay, -1000.0)]
