{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- HLINT ignore "Redundant do" -}

module DeathInDamascus (tests) where
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

  untypedDeathInDamascus :: UG.Graph UG.Stochastic
  untypedDeathInDamascus = UG.Graph [Labeled "Predisposition" predisposition
                                    ,Labeled "Action"         action
                                    ,Labeled "Death"          death
                                    ,Labeled "Outcome"        outcome
                                    ,Labeled "Value"          value
                                    ]
    where predisposition = UG.Distribution ["Fleer"  %= 0.5
                                           ,"Stayer" %= 0.5
                                           ]
          action         = UG.Conditional [UG.Clause [UG.Guard "Predisposition" "Fleer"]  "Flee"
                                          ,UG.Clause [UG.Guard "Predisposition" "Stayer"] "Stay"
                                          ]
          death          = UG.Conditional [UG.Clause [UG.Guard "Predisposition" "Fleer"]  "Aleppo"
                                          ,UG.Clause [UG.Guard "Predisposition" "Stayer"] "Damascus"
                                          ]
          outcome        = UG.Conditional [UG.Clause [UG.Guard "Action" "Stay", UG.Guard "Death" "Damascus"] "StayAndDie"
                                          ,UG.Clause [UG.Guard "Action" "Stay", UG.Guard "Death" "Aleppo"  ] "StayAndLive"
                                          ,UG.Clause [UG.Guard "Action" "Flee", UG.Guard "Death" "Damascus"] "FleeAndLive"
                                          ,UG.Clause [UG.Guard "Action" "Flee", UG.Guard "Death" "Aleppo"  ] "FleeAndDie"
                                          ]
          value          = UG.Conditional [UG.Clause [UG.Guard "Outcome" "StayAndDie" ]    "0"
                                          ,UG.Clause [UG.Guard "Outcome" "StayAndLive"] "1000"
                                          ,UG.Clause [UG.Guard "Outcome" "FleeAndLive"]  "999"
                                          ,UG.Clause [UG.Guard "Outcome" "FleeAndDie" ]   "-1"
                                          ]

  data Predisposition = Fleer      | Stayer      deriving (Eq, Show, Typeable, Data)
  data Action         = Flee       | Stay        deriving (Eq, Show, Typeable, Data)
  data Death          = Aleppo     | Damascus    deriving (Eq, Show, Typeable, Data)
  data Outcome        = StayAndDie | StayAndLive
                      | FleeAndDie | FleeAndLive deriving (Eq, Show, Typeable, Data)
  newtype Value       = Value Int                deriving (Eq, Show, Typeable, Data)

  instance {-# OVERLAPPING #-} TG.Stateable Value where
    toState (Value n) = State $ show n
    ofState (State s) = Value <$> readMaybe s

  utilityFunction :: Value -> U.Utility
  utilityFunction (Value v) = fromIntegral v

  deathInDamascus =
        distribution [ Fleer %= 0.5
                     ,Stayer %= 0.5
                     ]
    .*. choose (when (is Fleer)  Flee
            .|. when (is Stayer) Stay)
    .*. choose (when (is Fleer)  Aleppo
            .|. when (is Stayer) Damascus)
    .*. choose (when (is Stay .&. is Damascus) StayAndDie
            .|. when (is Stay .&. is Aleppo)   StayAndLive
            .|. when (is Flee .&. is Damascus) FleeAndLive
            .|. when (is Flee .&. is Aleppo)   FleeAndDie)
    .*. choose (when (is StayAndDie)  (Value     0)
            .|. when (is StayAndLive) (Value  1000)
            .|. when (is FleeAndLive) (Value   999)
            .|. when (is FleeAndDie)  (Value  $ -1))

  deathInDamascusOf t = t TG.true utilityFunction deathInDamascus

  tests :: IO ()
  tests = hspec $
    describe "Death in Damascus" $ do
      it "Death in Damascus allows one to stay or flee" $
        UG.choices "Action" (UG.branches untypedDeathInDamascus) `shouldBe` ["Flee", "Stay"]
      it "Typed graph should compile to the untyped graph" $
        TG.compile deathInDamascus `shouldBe` untypedDeathInDamascus
      it "CDT's choice alternates between stay and flee" $ do
        U.unstableDT U.intervene [UG.Guard "Action" "Stay"] U.stdSearch untypedDeathInDamascus `shouldBe` ("Flee", 999.0)
        U.unstableDT U.intervene [UG.Guard "Action" "Flee"] U.stdSearch untypedDeathInDamascus `shouldBe` ("Stay", 1000.0)
      it "EDT chooses to stay" $ deathInDamascusOf  T.edt                  `shouldBe` (Stay, 0.0)
      it "FDT chooses to stay" $ deathInDamascusOf (T.fdt @Predisposition) `shouldBe` (Stay, 0.0)
