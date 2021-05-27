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

module V2.DeathInDamascus where

import Data.Data (Data)
import DecisionTheory.Base (Labeled (Labeled))
import DecisionTheory.DecisionTheory (Utility)
import qualified DecisionTheory.Graph as UG
import DecisionTheory.Probability ((%=))
import DecisionTheory.V2.HList (hAsSingle, hAsTuple)
import DecisionTheory.V2.Stringify (AsLabel, AsState, Datally (..), Showly (..))
import qualified DecisionTheory.V2.TypedDecisionTheory as TypedDT
import DecisionTheory.V2.TypedGraph (choose, distribution, (.*.))
import qualified DecisionTheory.V2.TypedGraph as TG
import Test.Hspec (describe, hspec, it, shouldBe)

untypedDeathInDamascus :: UG.Graph 'UG.Stochastic
untypedDeathInDamascus =
  UG.Graph
    [ Labeled "Predisposition" predisposition,
      Labeled "Action" action,
      Labeled "Death" death,
      Labeled "Outcome" outcome,
      Labeled "Value" value
    ]
  where
    predisposition =
      UG.Distribution
        [ "Fleer" %= 0.5,
          "Stayer" %= 0.5
        ]
    action =
      UG.Conditional
        [ UG.Clause [UG.Guard "Predisposition" "Fleer"] "Flee",
          UG.Clause [UG.Guard "Predisposition" "Stayer"] "Stay"
        ]
    death =
      UG.Conditional
        [ UG.Clause [UG.Guard "Predisposition" "Fleer"] "Aleppo",
          UG.Clause [UG.Guard "Predisposition" "Stayer"] "Damascus"
        ]
    outcome =
      UG.Conditional
        [ UG.Clause [UG.Guard "Action" "Flee", UG.Guard "Death" "Aleppo"] "FleeAndDie",
          UG.Clause [UG.Guard "Action" "Flee", UG.Guard "Death" "Damascus"] "FleeAndLive",
          UG.Clause [UG.Guard "Action" "Stay", UG.Guard "Death" "Aleppo"] "StayAndLive",
          UG.Clause [UG.Guard "Action" "Stay", UG.Guard "Death" "Damascus"] "StayAndDie"
        ]
    value =
      UG.Conditional
        [ UG.Clause [UG.Guard "Outcome" "StayAndDie"] "0",
          UG.Clause [UG.Guard "Outcome" "StayAndLive"] "1000",
          UG.Clause [UG.Guard "Outcome" "FleeAndDie"] "-1",
          UG.Clause [UG.Guard "Outcome" "FleeAndLive"] "999"
        ]

data Predisposition = Fleer | Stayer
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Predisposition)

data Action = Flee | Stay
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Action)

data Death = Aleppo | Damascus
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Death)

data Outcome
  = StayAndDie
  | StayAndLive
  | FleeAndDie
  | FleeAndLive
  deriving stock (Eq, Show, Data, Bounded, Enum)
  deriving (AsLabel, AsState) via (Datally Outcome)

newtype Value = Value Int
  deriving stock (Eq, Show, Data)
  deriving newtype (Bounded, Enum)
  deriving (AsLabel) via (Datally Value)
  deriving (AsState) via (Showly Int)

utilityFunction :: Value -> Utility
utilityFunction (Value v) = fromIntegral v

deathInDamascus :: TG.Graph 'UG.Stochastic _
deathInDamascus =
  distribution
    [ Fleer %= 0.5,
      Stayer %= 0.5
    ]
    .*. choose
      ( hAsSingle $ \case
          Fleer -> Flee
          Stayer -> Stay
      )
    .*. choose
      ( hAsSingle $ \case
          Fleer -> Aleppo
          Stayer -> Damascus
      )
    .*. choose
      ( hAsTuple $ \case
          (Stay, Damascus) -> StayAndDie
          (Stay, Aleppo) -> StayAndLive
          (Flee, Damascus) -> FleeAndLive
          (Flee, Aleppo) -> FleeAndDie
      )
    .*. choose
      ( hAsSingle $ \case
          StayAndDie -> Value 0
          StayAndLive -> Value 1000
          FleeAndLive -> Value 999
          FleeAndDie -> Value $ -1
      )

deathInDamascusOf :: TypedDT.DecisionTheory _ '[] action Value -> TypedDT.Solutions action
deathInDamascusOf t = t TG.HNil utilityFunction deathInDamascus

tests :: IO ()
tests = hspec $
  describe "Death in Damascus" $ do
    it "Death in Damascus allows one to stay or flee" $
      UG.choices "Action" (UG.branches untypedDeathInDamascus) `shouldBe` ["Flee", "Stay"]
    it "Typed graph should compile to the untyped graph" $
      TG.compile deathInDamascus `shouldBe` untypedDeathInDamascus
    it "CDT's chooses to both stay and flee" $
      deathInDamascusOf TypedDT.cdt `shouldBe` [(Flee, 999.0), (Stay, 1000.0)]
    it "EDT chooses to stay" $ deathInDamascusOf TypedDT.edt `shouldBe` [(Stay, 0.0)]
    it "FDT chooses to stay" $ deathInDamascusOf (TypedDT.fdt @Predisposition) `shouldBe` [(Stay, 0.0)]
