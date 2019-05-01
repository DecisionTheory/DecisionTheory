{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module ParfitsHitchhiker (tests) where

  import Test.Hspec

  import Data.Data

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as U
  import DecisionTheory.TypedGraph
  import DecisionTheory.DecisionTheory

  parfitsHitchhiker :: U.Graph U.Stochastic
  parfitsHitchhiker = U.Graph [Labeled "Predisposition" predisposition
                              ,Labeled "Accuracy"       accuracy
                              ,Labeled "Offer"          offer
                              ,Labeled "Location"       location
                              ,Labeled "Action"         action
                              ,Labeled "Value"          value
                              ]
    where predisposition = U.Distribution [Probability "Trustworthy" 0.5
                                          ,Probability "Untrustworthy" 0.5
                                          ]
          accuracy       = U.Distribution [Probability "Accurate"   0.99
                                          ,Probability "Inaccurate" 0.01
                                          ]
          offer          = U.Conditional [U.Clause [U.Guard "Predisposition" "Trustworthy",   U.Guard "Accuracy" "Accurate"]   "Ride"
                                         ,U.Clause [U.Guard "Predisposition" "Trustworthy",   U.Guard "Accuracy" "Inaccurate"] "NoRide"
                                         ,U.Clause [U.Guard "Predisposition" "Untrustworthy", U.Guard "Accuracy" "Accurate"]   "NoRide"
                                         ,U.Clause [U.Guard "Predisposition" "Untrustworthy", U.Guard "Accuracy" "Inaccurate"] "Ride"
                                         ]
          location       = U.Conditional [U.Clause [U.Guard "Offer" "Ride"]   "City"
                                         ,U.Clause [U.Guard "Offer" "NoRide"] "Desert"
                                         ]
          action         = U.Conditional [U.Clause [U.Guard "Predisposition" "Trustworthy", U.Guard "Location" "City"] "Pay"
                                         ,U.Clause [] "NoPay"
                                         ]
          value          = U.Conditional [U.Clause [U.Guard "Action" "Pay",   U.Guard "Location" "City"] "-1000"
                                         ,U.Clause [U.Guard "Action" "NoPay", U.Guard "Location" "City"] "0"
                                         ,U.Clause []                                                    "-1000000"
                                         ]
  data Predisposition = Trustworthy | Untrustworthy deriving (Eq, Show, Typeable, Data)
  data Accuracy       = Accurate    | Inaccurate    deriving (Eq, Show, Typeable, Data)
  data Location       = City        | Desert        deriving (Eq, Show, Typeable, Data)
  data Action         = Pay         | NoPay         deriving (Eq, Show, Typeable, Data)
  data Offer          = Ride        | NoRide        deriving (Eq, Show, Typeable, Data)
  data Value          = Value Int                   deriving (Eq, Show, Typeable, Data)

  instance Unboxed Value where
    unboxed (Value n) = show n

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
    :*: Case (When (Is   Pay :&: Is City) (Box $ Value $    -1000)
          :|: When (Is NoPay :&: Is City) (Box $ Value $        0)
          :|: Otherwise                   (Box $ Value $ -1000000))

  parfitsHitchhikerOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  parfitsHitchhikerOf t = t [] stdSearch parfitsHitchhiker

  parfitsHitchhikerInTheCityOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  parfitsHitchhikerInTheCityOf t = t [U.Guard "Location" "City"] stdSearch parfitsHitchhiker

  tests :: IO ()
  tests = hspec $ do
    describe "Parfit's Hitchhiker" $ do
      it "Parfit's Hitchhiker allows one to pay or no pay" $ do
        (U.choices "Action" $ U.branches parfitsHitchhiker) `shouldBe` ["NoPay", "Pay"]
      it "EDT initially chooses to pay" $ do
        parfitsHitchhikerOf edt `shouldBe` ("Pay", -1000.0)
      it "EDT later chooses to no pay" $ do
        parfitsHitchhikerInTheCityOf edt `shouldBe` ("NoPay", 0.0)
      it "CDT initially chooses to no pay" $ do
        parfitsHitchhikerOf cdt `shouldBe` ("NoPay", -990099.0)
      it "CDT later still chooses to no pay" $ do
        parfitsHitchhikerInTheCityOf cdt `shouldBe` ("NoPay", 0.0)
      it "FDT initially chooses to pay" $ do
        parfitsHitchhikerOf (fdt "Predisposition") `shouldBe` ("Pay", -1000.0)
      it "FDT later still chooses to pay" $ do
        parfitsHitchhikerInTheCityOf (fdt "Predisposition") `shouldBe` ("Pay", -1000.0)
      it "Typed graph should compile to the untyped graph" $ do
        compile typedParfitsHitchhiker `shouldBe` parfitsHitchhiker
