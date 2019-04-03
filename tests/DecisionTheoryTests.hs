{-# LANGUAGE OverloadedStrings #-}

module DecisionTheoryTests (tests) where

  import Test.Hspec
  import DecisionTheory

  weird :: Graph Stochastic
  weird = Graph [Labeled "a" a
                ,Labeled "b" b
                ,Labeled "c" c
                ]
    where a = Distribution [Probability "a1" 0.5
                           ,Probability "a2" 0.5
                           ]
          b = Conditional [Clause [Guard "a" "a1"] "b1"
                          ,Clause [Guard "a" "a2"] "b2"
                          ]
          c = Conditional [Clause [Guard "a" "a1", Guard "b" "b1"] "c1"
                          ,Clause [Guard "a" "a1", Guard "b" "b2"] "c2"
                          ,Clause [Guard "a" "a2", Guard "b" "b1"] "c3"
                          ,Clause [Guard "a" "a2", Guard "b" "b2"] "c4"
                          ]
  weirdBranches :: [Probability (Graph Deterministic)]
  weirdBranches = [Probability (Graph [Labeled "a" (Always "a1")
                                         ,Labeled "b" (Conditional [Clause [Guard "a" "a1"] "b1",Clause [Guard "a" "a2"] "b2"])
                                         ,Labeled "c" (Conditional [Clause [Guard "a" "a1",Guard "b" "b1"] "c1",Clause [Guard "a" "a1",Guard "b" "b2"] "c2",Clause [Guard "a" "a2",Guard "b" "b1"] "c3",Clause [Guard "a" "a2",Guard "b" "b2"] "c4"])
                                         ]) 0.5
                     ,Probability (Graph [Labeled "a" (Always "a2")
                                         ,Labeled "b" (Conditional [Clause [Guard "a" "a1"] "b1",Clause [Guard "a" "a2"] "b2"])
                                         ,Labeled "c" (Conditional [Clause [Guard "a" "a1",Guard "b" "b1"] "c1",Clause [Guard "a" "a1",Guard "b" "b2"] "c2",Clause [Guard "a" "a2",Guard "b" "b1"] "c3",Clause [Guard "a" "a2",Guard "b" "b2"] "c4"])
                                         ]) 0.5
                     ]

  simple :: Graph Stochastic
  simple = Graph [Labeled "a" $ Distribution [Probability "a1" 0.1
                                             ,Probability "a2" 0.9
                                             ]
                 ,Labeled "b" $ Distribution [Probability "b1" 0.3
                                             ,Probability "b2" 0.7
                                             ]
                 ]

  simpleBranches :: [Probability (Graph Deterministic)]
  simpleBranches = [Probability (Graph [Labeled "a" (Always "a1"),Labeled "b" (Always "b1")]) 0.03
                   ,Probability (Graph [Labeled "a" (Always "a1"),Labeled "b" (Always "b2")]) 0.07
                   ,Probability (Graph [Labeled "a" (Always "a2"),Labeled "b" (Always "b1")]) 0.27
                   ,Probability (Graph [Labeled "a" (Always "a2"),Labeled "b" (Always "b2")]) 0.63
                   ]

  tests :: IO ()
  tests = hspec $ do
    describe "Probability tests" $ do
      it "Squash merges probabilities" $ do
        squash (when (==)) [Probability ("A" :: String) 0.1, Probability "B" 0.4, Probability "A" 0.2, Probability "B" 0.3] `shouldBe` [Probability "A" 0.3, Probability "B" 0.7]
      it "\"Weird\" branches" $ do
        branches weird `shouldBe` weirdBranches
      it "\"Weird\" probabilities for \"c\"" $ do
        probabilities "c" (branches weird) `shouldBe` [Probability "c1" 0.5, Probability "c4" 0.5]
      it "\"Simple\" branches" $ do
        branches simple `shouldBe` simpleBranches
      it "\"Simple\" branches" $ do
        normalize [Probability ("A" :: String) 0.1, Probability "B" 0.3] `shouldBe` [Probability "A" 0.25,Probability "B" 0.75]
