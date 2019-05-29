{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- HLINT ignore "Redundant do" -}

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
  newtype Value       = Value Int                   deriving (Eq, Show, Typeable, Data)

  instance {-# OVERLAPS #-} Stateable Value where
    toState (Value n) = State $ show n

  typedParfitsHitchhiker =
        distribution [  Trustworthy %= 0.5
                     ,Untrustworthy %= 0.5
                     ]
    .*. distribution [  Accurate %= 0.99
                     ,Inaccurate %= 0.01
                     ]
    .*. depends (when (is   Trustworthy .&. is   Accurate)   Ride
             .|. when (is   Trustworthy .&. is Inaccurate) NoRide
             .|. when (is Untrustworthy .&. is   Accurate) NoRide
             .|. when (is Untrustworthy .&. is Inaccurate)   Ride)
    .*. depends (when (is   Ride) City
             .|. when (is NoRide) Desert)
    .*. depends (when (is Trustworthy .&. is City)   Pay
             .|. fallback                          NoPay)
    .*. depends (when (is   Pay .&. is City) (Value $    -1000)
             .|. when (is NoPay .&. is City) (Value          0)
             .|. fallback                    (Value $ -1000000))

  parfitsHitchhikerOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  parfitsHitchhikerOf t = t [] stdSearch parfitsHitchhiker

  parfitsHitchhikerInTheCityOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  parfitsHitchhikerInTheCityOf t = t [U.Guard "Location" "City"] stdSearch parfitsHitchhiker

  tests :: IO ()
  tests = hspec $
    describe "Parfit's Hitchhiker" $ do
      it "Parfit's Hitchhiker allows one to pay or no pay" $
        U.choices "Action" (U.branches parfitsHitchhiker) `shouldBe` ["NoPay", "Pay"]
      it "EDT initially chooses to pay" $
        parfitsHitchhikerOf edt `shouldBe` ("Pay", -1000.0)
      it "EDT later chooses to no pay" $
        parfitsHitchhikerInTheCityOf edt `shouldBe` ("NoPay", 0.0)
      it "CDT initially chooses to no pay" $
        parfitsHitchhikerOf cdt `shouldBe` ("NoPay", -990099.0)
      it "CDT later still chooses to no pay" $
        parfitsHitchhikerInTheCityOf cdt `shouldBe` ("NoPay", 0.0)
      it "FDT initially chooses to pay" $
        parfitsHitchhikerOf (fdt "Predisposition") `shouldBe` ("Pay", -1000.0)
      it "FDT later still chooses to pay" $
        parfitsHitchhikerInTheCityOf (fdt "Predisposition") `shouldBe` ("Pay", -1000.0)
      it "Typed graph should compile to the untyped graph" $
        compile typedParfitsHitchhiker `shouldBe` parfitsHitchhiker
