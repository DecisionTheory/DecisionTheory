{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module DeathInDamascus (tests) where

  import Test.Hspec

  import Data.Data

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as U
  import DecisionTheory.TypedGraph
  import DecisionTheory.DecisionTheory

  deathInDamascus :: U.Graph U.Stochastic
  deathInDamascus = U.Graph [Labeled "Predisposition" predisposition
                            ,Labeled "Action"         action
                            ,Labeled "Death"          death
                            ,Labeled "Outcome"        outcome
                            ,Labeled "Value"          value
                            ]
    where predisposition = U.Distribution [Probability "Fleer"  0.5
                                          ,Probability "Stayer" 0.5
                                          ]
          action         = U.Conditional [U.Clause [U.Guard "Predisposition" "Fleer"]  "Flee"
                                         ,U.Clause [U.Guard "Predisposition" "Stayer"] "Stay"
                                         ]
          death          = U.Conditional [U.Clause [U.Guard "Predisposition" "Fleer"]  "Aleppo"
                                         ,U.Clause [U.Guard "Predisposition" "Stayer"] "Damascus"
                                         ]
          outcome        = U.Conditional [U.Clause [U.Guard "Action" "Stay", U.Guard "Death" "Damascus"] "StayAndDie"
                                         ,U.Clause [U.Guard "Action" "Stay", U.Guard "Death" "Aleppo"  ] "StayAndLive"
                                         ,U.Clause [U.Guard "Action" "Flee", U.Guard "Death" "Damascus"] "FleeAndLive"
                                         ,U.Clause [U.Guard "Action" "Flee", U.Guard "Death" "Aleppo"  ] "FleeAndDie"
                                         ]
          value          = U.Conditional [U.Clause [U.Guard "Outcome" "StayAndDie" ]    "0"
                                         ,U.Clause [U.Guard "Outcome" "StayAndLive"] "1000"
                                         ,U.Clause [U.Guard "Outcome" "FleeAndLive"]  "999"
                                         ,U.Clause [U.Guard "Outcome" "FleeAndDie" ]   "-1"
                                         ]

  data Predisposition = Fleer      | Stayer      deriving (Eq, Show, Typeable, Data)
  data Action         = Flee       | Stay        deriving (Eq, Show, Typeable, Data)
  data Death          = Aleppo     | Damascus    deriving (Eq, Show, Typeable, Data)
  data Outcome        = StayAndDie | StayAndLive
                      | FleeAndDie | FleeAndLive deriving (Eq, Show, Typeable, Data)
  data Value          = Value Int                deriving (Eq, Show, Typeable, Data)

  instance {-# OVERLAPS #-} Stateable Value where
    toState (Value n) = State $ show n

  typedDeathInDamascus =
        Distribution [ Fleer %= 0.5
                     ,Stayer %= 0.5
                     ]
    :*: Case (When (Is Fleer)  Flee
          :|: When (Is Stayer) Stay)
    :*: Case (When (Is Fleer)  Aleppo
          :|: When (Is Stayer) Damascus)
    :*: Case (When (Is Stay :&: Is Damascus) StayAndDie
          :|: When (Is Stay :&: Is Aleppo)   StayAndLive
          :|: When (Is Flee :&: Is Damascus) FleeAndLive
          :|: When (Is Flee :&: Is Aleppo)   FleeAndDie)
    :*: Case (When (Is StayAndDie)  (Value $    0)
          :|: When (Is StayAndLive) (Value $ 1000)
          :|: When (Is FleeAndLive) (Value $  999)
          :|: When (Is FleeAndDie)  (Value $   -1))

  deathInDamascusOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  deathInDamascusOf t = t [] stdSearch deathInDamascus

  tests :: IO ()
  tests = hspec $ do
    describe "Death in Damascus" $ do
      it "Death in Damascus allows one to stay or flee" $ do
        (U.choices "Action" $ U.branches deathInDamascus) `shouldBe` ["Flee", "Stay"]
      it "EDT chooses to stay" $ do
        deathInDamascusOf edt `shouldBe` ("Stay", 0.0)
      it "CDT's choice alternates between stay and flee" $ do
        dt intervene [U.Guard "Action" "Stay"] stdSearch deathInDamascus `shouldBe` ("Flee", 999.0)
        dt intervene [U.Guard "Action" "Flee"] stdSearch deathInDamascus `shouldBe` ("Stay", 1000.0)
      it "FDT chooses to stay" $ do
        deathInDamascusOf (fdt "Predisposition") `shouldBe` ("Stay", 0.0)
      it "Typed graph should compile to the untyped graph" $ do
        compile typedDeathInDamascus `shouldBe` deathInDamascus
