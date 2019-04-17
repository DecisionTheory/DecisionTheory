{-# LANGUAGE OverloadedStrings #-}

module Newcomb (tests) where

  import Test.Hspec

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import DecisionTheory.Graph
  import DecisionTheory.DecisionTheory

  newcomb :: Graph Stochastic
  newcomb = Graph [Labeled "action"         action
                  ,Labeled "accuracy"       accuracy
                  ,Labeled "prediction"     prediction
                  ,Labeled "predisposition" predisposition
                  ,Labeled "box_b"          box_b
                  ,Labeled "outcome"        outcome
                  ,Labeled "value"          value
                  ]
    where predisposition = Distribution [Probability "oneboxer" 0.5
                                        ,Probability "twoboxer" 0.5
                                        ]
          action         = Conditional [Clause [Guard "predisposition" "oneboxer"] "onebox"
                                       ,Clause [Guard "predisposition" "twoboxer"] "twobox"
                                       ]
          accuracy       = Distribution [Probability "accurate"   0.99
                                        ,Probability "inaccurate" 0.01
                                        ]
          prediction     = Conditional [Clause [Guard "predisposition" "oneboxer", Guard "accuracy"   "accurate"] "p1"
                                       ,Clause [Guard "predisposition" "twoboxer", Guard "accuracy"   "accurate"] "p2"
                                       ,Clause [Guard "predisposition" "oneboxer", Guard "accuracy" "inaccurate"] "p2"
                                       ,Clause [Guard "predisposition" "twoboxer", Guard "accuracy" "inaccurate"] "p1"
                                       ]
          box_b          = Conditional [Clause [Guard "prediction" "p1"] "full"
                                       ,Clause [Guard "prediction" "p2"] "empty"
                                       ]
          outcome        = Conditional [Clause [Guard "action" "onebox", Guard "box_b" "full" ] "1f"
                                       ,Clause [Guard "action" "twobox", Guard "box_b" "full" ] "2f"
                                       ,Clause [Guard "action" "onebox", Guard "box_b" "empty"] "1e"
                                       ,Clause [Guard "action" "twobox", Guard "box_b" "empty"] "2e"
                                       ]
          value          = Conditional [Clause [Guard "outcome" "1f"] "1000000"
                                       ,Clause [Guard "outcome" "2f"] "1001000"
                                       ,Clause [Guard "outcome" "1e"]       "0"
                                       ,Clause [Guard "outcome" "2e"]    "1000"
                                       ]

  newcombOf :: ([Guard] -> Search -> Graph Stochastic -> a) -> a
  newcombOf t = t [] stdSearch newcomb

  unreliableNewcomb :: Graph Stochastic
  unreliableNewcomb = replaceG unreliability newcomb
    where unreliability ln@(Labeled l _) | l == "accuracy" = Labeled l $ Distribution [Probability "accurate"   0.5
                                                                                      ,Probability "inaccurate" 0.5
                                                                                      ]
                                         | otherwise       = ln

  lessUnreliableNewcomb :: Graph Stochastic
  lessUnreliableNewcomb = replaceG lesserUnreliability newcomb
    where lesserUnreliability ln@(Labeled l _) | l == "accuracy" = Labeled l $ Distribution [Probability "accurate"   0.51
                                                                                            ,Probability "inaccurate" 0.49
                                                                                            ]
                                               | otherwise       = ln

  tests :: IO ()
  tests = hspec $ do
    describe "Newcomb" $ do
      it "Newcomb allows one to onebox or twobox" $ do
        (choices "action" $ branches newcomb) `shouldBe` ["onebox", "twobox"]
      it "EDT chooses to onebox" $ do
        newcombOf edt `shouldBe` ("onebox", 990000.0)
      it "CDT chooses to twobox" $ do
        newcombOf cdt `shouldBe` ("twobox", 11000.0)
      it "FDT chooses to onebox" $ do
        newcombOf (fdt "predisposition") `shouldBe` ("onebox", 990000.0)
      it "FDT chooses to onebox even with transparency" $ do
        fdt "predisposition" [Guard "box_b" "full"] stdSearch newcomb `shouldBe` ("onebox", 1000000.0)
      it "FDT chooses to twobox when Omega prediction is unreliable" $ do
        fdt "predisposition" [] stdSearch unreliableNewcomb `shouldBe` ("twobox",501000.0)
      it "FDT chooses to onebox when Omega prediction is less unreliable" $ do
        fdt "predisposition" [] stdSearch lessUnreliableNewcomb `shouldBe` ("onebox",510000.0)
