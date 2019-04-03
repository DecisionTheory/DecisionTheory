{-# LANGUAGE OverloadedStrings #-}

module ParfitsHitchhiker (tests) where

  import Test.Hspec
  import DecisionTheory

  parfitsHitchhiker :: Graph Stochastic
  parfitsHitchhiker = Graph [Labeled "predisposition" predisposition
                            ,Labeled "accuracy"       accuracy
                            ,Labeled "offer"          offer
                            ,Labeled "location"       location
                            ,Labeled "action"         action
                            ,Labeled "value"          value
                            ]
    where predisposition = Distribution [Probability "trustworthy" 0.5
                                        ,Probability "untrustworthy" 0.5
                                        ]
          accuracy       = Distribution [Probability "accurate"   0.99
                                        ,Probability "inaccurate" 0.01
                                        ]
          offer          = Conditional [Clause [Guard "predisposition" "trustworthy",   Guard "accuracy" "accurate"]   "ride"
                                       ,Clause [Guard "predisposition" "trustworthy",   Guard "accuracy" "inaccurate"] "no ride"
                                       ,Clause [Guard "predisposition" "untrustworthy", Guard "accuracy" "accurate"]   "no ride"
                                       ,Clause [Guard "predisposition" "untrustworthy", Guard "accuracy" "inaccurate"] "ride"
                                       ]
          location       = Conditional [Clause [Guard "offer" "ride"]    "city"
                                       ,Clause [Guard "offer" "no ride"] "desert"
                                       ]
          action         = Conditional [Clause [Guard "predisposition" "trustworthy", Guard "location" "city"] "pay"
                                       ,Clause [] "no pay"
                                       ]
          value          = Conditional [Clause [Guard "action" "pay",    Guard "location" "city"] "-1000"
                                       ,Clause [Guard "action" "no pay", Guard "location" "city"] "0"
                                       ,Clause []                                                 "-1000000"
                                       ]

  parfitsHitchhikerOf :: ([Guard] -> Search -> Graph Stochastic -> a) -> a
  parfitsHitchhikerOf t = t [] stdSearch parfitsHitchhiker

  parfitsHitchhikerInTheCityOf :: ([Guard] -> Search -> Graph Stochastic -> a) -> a
  parfitsHitchhikerInTheCityOf t = t [Guard "location" "city"] stdSearch parfitsHitchhiker

  tests :: IO ()
  tests = hspec $ do
    describe "Parfit's Hitchhiker" $ do
      it "Parfit's Hitchhiker allows one to pay or no pay" $ do
        (choices "action" $ branches parfitsHitchhiker) `shouldBe` ["no pay", "pay"]
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
