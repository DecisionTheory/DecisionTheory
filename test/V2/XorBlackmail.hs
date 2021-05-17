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

module V2.XorBlackmail (tests) where

import Data.Data (Data)
import DecisionTheory.Base (Labeled (Labeled))
import qualified DecisionTheory.Graph as UG
import DecisionTheory.Probability ((%=))
import DecisionTheory.V2.HList (hAsSingle, hAsTuple)
import DecisionTheory.V2.Stringify (AsLabel, AsState, Datally (..), Showly (..))
import DecisionTheory.V2.TypedGraph (choose, distribution, (.*.))
import qualified DecisionTheory.V2.TypedGraph as TG
import Test.Hspec (describe, hspec, it, shouldBe)

untypedXorBlackmail :: UG.Graph 'UG.Stochastic
untypedXorBlackmail =
  UG.Graph
    [ Labeled "Infestation" infestation,
      Labeled "Predisposition" predisposition,
      Labeled "Prediction" prediction,
      Labeled "Observation" observation,
      Labeled "Action" action,
      Labeled "Value" value
    ]
  where
    infestation =
      UG.Distribution
        [ "Termites" %= 0.5,
          "NoTermites" %= 0.5
        ]
    predisposition =
      UG.Distribution
        [ "Payer" %= 0.5,
          "Refuser" %= 0.5
        ]
    prediction =
      UG.Conditional
        [ UG.Clause [UG.Guard "Infestation" "Termites", UG.Guard "Predisposition" "Payer"] "Skeptic",
          UG.Clause [UG.Guard "Infestation" "Termites", UG.Guard "Predisposition" "Refuser"] "Gullible",
          UG.Clause [UG.Guard "Infestation" "NoTermites", UG.Guard "Predisposition" "Payer"] "Gullible",
          UG.Clause [UG.Guard "Infestation" "NoTermites", UG.Guard "Predisposition" "Refuser"] "Skeptic"
        ]
    observation =
      UG.Conditional
        [ UG.Clause [UG.Guard "Prediction" "Skeptic"] "NoLetter",
          UG.Clause [UG.Guard "Prediction" "Gullible"] "Letter"
        ]
    action =
      UG.Conditional
        [ UG.Clause [UG.Guard "Predisposition" "Payer"] "Pay",
          UG.Clause [UG.Guard "Predisposition" "Refuser"] "Refuse"
        ]
    value =
      UG.Conditional
        [ UG.Clause [UG.Guard "Infestation" "Termites", UG.Guard "Action" "Pay"] "-1001000",
          UG.Clause [UG.Guard "Infestation" "Termites", UG.Guard "Action" "Refuse"] "-1000000",
          UG.Clause [UG.Guard "Infestation" "NoTermites", UG.Guard "Action" "Pay"] "-1000",
          UG.Clause [UG.Guard "Infestation" "NoTermites", UG.Guard "Action" "Refuse"] "0"
        ]

data Infestation = Termites | NoTermites
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Infestation)

data Predisposition = Payer | Refuser
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Predisposition)

data Prediction = Skeptic | Gullible
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Prediction)

data Observation = Letter | NoLetter
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Observation)

data Action = Pay | Refuse
  deriving (Eq, Show, Data, Enum, Bounded)
  deriving (AsLabel, AsState) via (Datally Action)

newtype Value = Value Int
  deriving stock (Eq, Show, Data)
  deriving newtype (Enum, Bounded)
  deriving (AsLabel) via (Datally Value)
  deriving (AsState) via (Showly Int)

xorBlackmail :: TG.Graph _ _
xorBlackmail =
  distribution
    [ Termites %= 0.5,
      NoTermites %= 0.5
    ]
    .*. distribution
      [ Payer %= 0.5,
        Refuser %= 0.5
      ]
    .*. choose
      ( hAsTuple $ \case
          (Termites, Payer) -> Skeptic
          (Termites, Refuser) -> Gullible
          (NoTermites, Payer) -> Gullible
          (NoTermites, Refuser) -> Skeptic
      )
    .*. choose
      ( hAsSingle $ \case
          Gullible -> Letter
          Skeptic -> NoLetter
      )
    .*. choose
      ( hAsSingle $ \case
          Payer -> Pay
          Refuser -> Refuse
      )
    .*. choose
      ( hAsTuple $ \case
          (Termites, Pay) -> (Value $ -1001000)
          (Termites, Refuse) -> (Value $ -1000000)
          (NoTermites, Pay) -> (Value $ -1000)
          (NoTermites, Refuse) -> (Value 0)
      )

tests :: IO ()
tests = hspec $
  describe "XOR Blackmail" $ do
    it "XOR Blackmail allows one to pay or refuse" $
      UG.choices "Action" (UG.branches untypedXorBlackmail) `shouldBe` ["Pay", "Refuse"]
    it "Typed graph should compile to the untyped graph" $ do
      TG.compile xorBlackmail `shouldBe` untypedXorBlackmail

-- it "EDT chooses to pay" $ xorBlackmailOf T.edt `shouldBe` [(Pay, -1000.0)]
-- it "CDT chooses to refuse" $ xorBlackmailOf T.cdt `shouldBe` [(Refuse, -1000000.0)]
-- it "FDT chooses to refuse" $ xorBlackmailOf (T.fdt @Predisposition) `shouldBe` [(Refuse, -1000000.0)]
