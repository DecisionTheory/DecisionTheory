module Newcomb (main) where

  import Test.Hspec
  import Test.Hspec.QuickCheck
  import DecisionTheory
  import Test.QuickCheck

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

  newcombOf dt = dt [] stdSearch newcomb

  main :: IO ()
  main = hspec $ do
    describe "Newcomb" $ do
      it "EDT chooses to onebox " $ do
        newcombOf edt `shouldBe` ("onebox", 990000.0)


  testCausalNewcombChoices = test "CausalNewcombChoices" ["onebox", "twobox"] $ choices "action" $ branches newcomb

  cdtChoiceForCausalNewcomb = cdt [] stdSearch causalNewcomb
  testCdtChoiceForCausalNewcomb = test "CdtChoiceForCausalNewcomb" ("twobox", 11000.0) cdtChoiceForCausalNewcomb

  fdtChoiceForCausalNewcomb = fdt (Label "predisposition") [] stdSearch causalNewcomb
  testFdtChoiceForCausalNewcomb = test "FdtChoiceForCausalNewcomb" ("onebox",990000.0) fdtChoiceForCausalNewcomb

  fdtChoiceForTransparentCausalNewcomb = fdt (Label "predisposition") [Guard (Label "box_b") (State "full")] stdSearch causalNewcomb
  testFdtChoiceForTransparentCausalNewcomb = test "FdtChoiceForTransparentCausalNewcomb" ("onebox",1000000.0) fdtChoiceForTransparentCausalNewcomb

  fdtChoiceForCausalUnreliableNewcomb = fdt (Label "predisposition") [] stdSearch $ replaceG unreliability causalNewcomb 
    where unreliability ln@(Labeled l n) | l == Label "accuracy" = Labeled l $ Distribution [Probability (State "accurate")   0.5
                                                                                            ,Probability (State "inaccurate") 0.5
                                                                                            ]
                                         | otherwise             = ln
  testFdtChoiceForCausalUnreliableNewcomb = test "FdtChoiceForCausalUnreliableNewcomb" ("twobox",501000.0) fdtChoiceForCausalUnreliableNewcomb

  fdtChoiceForCausalLessUnreliableNewcomb = fdt (Label "predisposition") [] stdSearch $ replaceG lesserUnreliability causalNewcomb 
    where lesserUnreliability ln@(Labeled l n) | l == Label "accuracy" = Labeled l $ Distribution [Probability (State "accurate")   0.51
                                                                                                  ,Probability (State "inaccurate") 0.49
                                                                                                 ]
                                               | otherwise             = ln
  testFdtChoiceForCausalLessUnreliableNewcomb = test "FdtChoiceForCausalLessUnreliableNewcomb" ("onebox",510000.0) fdtChoiceForCausalLessUnreliableNewcomb
