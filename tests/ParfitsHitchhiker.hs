{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}

module ParfitsHitchhiker (tests) where

  import Test.Hspec

  import Data.Data
  import Data.Typeable

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as U
  import DecisionTheory.TypedGraph
  import DecisionTheory.DecisionTheory

  parfitsHitchhiker :: U.Graph U.Stochastic
  parfitsHitchhiker = U.Graph [Labeled "predisposition" predisposition
                              ,Labeled "accuracy"       accuracy
                              ,Labeled "offer"          offer
                              ,Labeled "location"       location
                              ,Labeled "action"         action
                              ,Labeled "value"          value
                              ]
    where predisposition = U.Distribution [Probability "trustworthy" 0.5
                                          ,Probability "untrustworthy" 0.5
                                          ]
          accuracy       = U.Distribution [Probability "accurate"   0.99
                                          ,Probability "inaccurate" 0.01
                                          ]
          offer          = U.Conditional [U.Clause [U.Guard "predisposition" "trustworthy",   U.Guard "accuracy" "accurate"]   "ride"
                                         ,U.Clause [U.Guard "predisposition" "trustworthy",   U.Guard "accuracy" "inaccurate"] "no ride"
                                         ,U.Clause [U.Guard "predisposition" "untrustworthy", U.Guard "accuracy" "accurate"]   "no ride"
                                         ,U.Clause [U.Guard "predisposition" "untrustworthy", U.Guard "accuracy" "inaccurate"] "ride"
                                         ]
          location       = U.Conditional [U.Clause [U.Guard "offer" "ride"]    "city"
                                         ,U.Clause [U.Guard "offer" "no ride"] "desert"
                                         ]
          action         = U.Conditional [U.Clause [U.Guard "predisposition" "trustworthy", U.Guard "location" "city"] "pay"
                                         ,U.Clause [] "no pay"
                                         ]
          value          = U.Conditional [U.Clause [U.Guard "action" "pay",    U.Guard "location" "city"] "-1000"
                                         ,U.Clause [U.Guard "action" "no pay", U.Guard "location" "city"] "0"
                                         ,U.Clause []                                                     "-1000000"
                                         ]
  data Predisposition = Trustworthy
                      | Untrustworthy
    deriving (Eq, Show, Typeable, Data)
  data Accuracy       = Accurate
                      | Inaccurate
    deriving (Eq, Show, Typeable, Data)
  data Location       = City
                      | Desert
    deriving (Eq, Show, Typeable, Data)
  data Action         =   Pay
                      | NoPay
    deriving (Eq, Show, Typeable, Data)
  data Offer          =   Ride
                      | NoRide
    deriving (Eq, Show, Typeable, Data)
  data Value          = Value Int
    deriving (Eq, Show, Typeable, Data)

  typedParfitsHitchhiker = 
        Distribution [  Trustworthy %= 0.5
                     ,Untrustworthy %= 0.5
                     ]
    :*: Distribution [  Accurate %= 0.99
                     ,Inaccurate %= 0.01
                     ]
    :*: Case (When (Is   Trustworthy :&: Is   Accurate)   Ride
          :|: When (Is   Trustworthy :&: Is Inaccurate) NoRide
          :|: When (Is Untrustworthy :&: Is   Accurate) NoRide
          :|: When (Is Untrustworthy :&: Is Inaccurate)   Ride)
    :*: Case (When (Is   Ride) City
          :|: When (Is NoRide) Desert)
    :*: Case (When (Is Trustworthy :&: Is City)   Pay
          :|: Otherwise                         NoPay)
    :*: Case (When (Is   Pay :&: Is City) (Value $    -1000)
          :|: When (Is NoPay :&: Is City) (Value $        0)
          :|: Otherwise                   (Value $ -1000000))

  parfitsHitchhikerOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  parfitsHitchhikerOf t = t [] stdSearch parfitsHitchhiker

  parfitsHitchhikerInTheCityOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  parfitsHitchhikerInTheCityOf t = t [U.Guard "location" "city"] stdSearch parfitsHitchhiker

  tests :: IO ()
  tests = hspec $ do
    describe "Parfit's Hitchhiker" $ do
      it "Parfit's Hitchhiker allows one to pay or no pay" $ do
        (U.choices "action" $ U.branches parfitsHitchhiker) `shouldBe` ["no pay", "pay"]
      it "EDT initially chooses to pay" $ do
        parfitsHitchhikerOf edt `shouldBe` ("pay", -1000.0)
      it "EDT later chooses to no pay" $ do
        parfitsHitchhikerInTheCityOf edt `shouldBe` ("no pay", 0.0)
      it "CDT initially chooses to no pay" $ do
        parfitsHitchhikerOf cdt `shouldBe` ("no pay", -990099.0)
      it "CDT later still chooses to no pay" $ do
        parfitsHitchhikerInTheCityOf cdt `shouldBe` ("no pay", 0.0)
      it "FDT initially chooses to pay" $ do
        parfitsHitchhikerOf (fdt "predisposition") `shouldBe` ("pay", -1000.0)
      it "FDT later still chooses to pay" $ do
        parfitsHitchhikerInTheCityOf (fdt "predisposition") `shouldBe` ("pay", -1000.0)
