{-# LANGUAGE OverloadedStrings #-}

module XorBlackmail (tests) where

  import Test.Hspec

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import DecisionTheory.Graph
  import DecisionTheory.DecisionTheory

  xorBlackmail :: Graph Stochastic
  xorBlackmail = Graph [Labeled "infestation"    infestation
                       ,Labeled "predisposition" predisposition
                       ,Labeled "prediction"     prediction
                       ,Labeled "action"         action
                       ,Labeled "value"          value
                       ,Labeled "observation"    observation
                       ]
    where infestation    = Distribution [Probability "termites" 0.5
                                        ,Probability "no termites" 0.5
                                        ]
          predisposition = Distribution [Probability "payer"   0.5
                                        ,Probability "refuser" 0.5
                                        ]
          prediction     = Conditional [Clause [Guard "infestation" "termites",    Guard "predisposition" "payer"  ] "skeptic"
                                       ,Clause [Guard "infestation" "termites",    Guard "predisposition" "refuser"] "gullible"
                                       ,Clause [Guard "infestation" "no termites", Guard "predisposition" "payer"  ] "gullible"
                                       ,Clause [Guard "infestation" "no termites", Guard "predisposition" "refuser"] "skeptic"
                                       ]
          observation = Conditional [Clause [Guard "prediction" "gullible"] "letter"
                                    ,Clause [Guard "prediction" "skeptic"]  "no letter"
                                    ]
          action      = Conditional [Clause [Guard "predisposition" "payer"]   "pay"
                                    ,Clause [Guard "predisposition" "refuser"] "refuse"
                                    ]
          value       = Conditional [Clause [Guard "infestation" "termites",    Guard "action" "pay"   ] "-1001000"
                                    ,Clause [Guard "infestation" "termites",    Guard "action" "refuse"] "-1000000"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "pay"   ] "-1000"
                                    ,Clause [Guard "infestation" "no termites", Guard "action" "refuse"] "-0"
                                    ]


  xorBlackmailOf :: ([Guard] -> Search -> Graph Stochastic -> a) -> a
  xorBlackmailOf t = t [Guard "observation" "letter"] stdSearch xorBlackmail

  tests :: IO ()
  tests = hspec $ do
    describe "XOR Blackmail" $ do
      it "XOR Blackmail allows one to pay or refuse" $ do
        (choices "action" $ branches xorBlackmail) `shouldBe` ["pay", "refuse"]
      it "EDT chooses to pay" $ do
        xorBlackmailOf edt `shouldBe` ("pay", -1000.0)
      it "CDT chooses to refuse" $ do
        xorBlackmailOf cdt `shouldBe` ("refuse", -1000000.0)
      it "FDT chooses to refuse" $ do
        xorBlackmailOf (fdt "predisposition") `shouldBe` ("refuse", -1000000.0)
