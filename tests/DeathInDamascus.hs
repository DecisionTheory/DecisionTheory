{-# LANGUAGE OverloadedStrings #-}

module DeathInDamascus (tests) where

  import Test.Hspec
  import DecisionTheory

  deathInDamascus :: Graph Stochastic
  deathInDamascus = Graph [Labeled "predisposition" predisposition
                          ,Labeled "action"         action
                          ,Labeled "death"          death
                          ,Labeled "outcome"        outcome
                          ,Labeled "value"          value
                          ]
    where predisposition = Distribution [Probability "fleer"  0.5
                                        ,Probability "stayer" 0.5
                                        ]
          action      = Conditional [Clause [Guard "predisposition" "fleer"]  "flee"
                                    ,Clause [Guard "predisposition" "stayer"] "stay"
                                    ]
          death       = Conditional [Clause [Guard "predisposition" "fleer"]  "aleppo"
                                    ,Clause [Guard "predisposition" "stayer"] "damascus"
                                    ]
          outcome        = Conditional [Clause [Guard "action" "stay", Guard "death" "damascus"] "stay and die"
                                       ,Clause [Guard "action" "stay", Guard "death" "aleppo"  ] "stay and live"
                                       ,Clause [Guard "action" "flee", Guard "death" "damascus"] "flee and live"
                                       ,Clause [Guard "action" "flee", Guard "death" "aleppo"  ] "flee and die"
                                       ]
          value          = Conditional [Clause [Guard "outcome" "stay and die" ]    "0"
                                       ,Clause [Guard "outcome" "stay and live"] "1000"
                                       ,Clause [Guard "outcome" "flee and live"]  "999"
                                       ,Clause [Guard "outcome" "flee and die" ]   "-1"
                                       ]

  deathInDamascusOf :: ([Guard] -> Search -> Graph Stochastic -> a) -> a
  deathInDamascusOf t = t [] stdSearch deathInDamascus

  tests :: IO ()
  tests = hspec $ do
    describe "Death in Damascus" $ do
      it "Death in Damascus allows one to stay or flee" $ do
        (choices "action" $ branches deathInDamascus) `shouldBe` ["flee", "stay"]
      it "EDT chooses to stay" $ do
        deathInDamascusOf edt `shouldBe` ("stay", 0.0)
      it "CDT's choice alternates between stay and flee" $ do
        dt intervene [Guard "action" "stay"] stdSearch deathInDamascus `shouldBe` ("flee", 999.0)
        dt intervene [Guard "action" "flee"] stdSearch deathInDamascus `shouldBe` ("stay", 1000.0)
      it "FDT chooses to stay" $ do
        deathInDamascusOf (fdt "predisposition") `shouldBe` ("stay", 0.0)
