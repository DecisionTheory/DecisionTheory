{-# LANGUAGE OverloadedStrings, DeriveDataTypeable, TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- HLINT ignore "Redundant do" -}

module ParfitsHitchhiker (tests) where
  import Test.Hspec

  import Data.Data
  import Text.Read

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as UG
  import qualified DecisionTheory.DecisionTheory as U
  import qualified DecisionTheory.TypedGraph as TG
  import qualified DecisionTheory.TypedDecisionTheory as T
  import DecisionTheory.TypedGraph(distribution, choose, when, is, elsewise, (.*.), (.|.), (.&.))

  untypedParfitsHitchhiker :: UG.Graph UG.Stochastic
  untypedParfitsHitchhiker = UG.Graph [Labeled "Predisposition" predisposition
                                      ,Labeled "Accuracy"       accuracy
                                      ,Labeled "Offer"          offer
                                      ,Labeled "Location"       location
                                      ,Labeled "Action"         action
                                      ,Labeled "Value"          value
                                      ]
    where predisposition = UG.Distribution ["Trustworthy"   %= 0.5
                                           ,"Untrustworthy" %= 0.5
                                           ]
          accuracy       = UG.Distribution ["Accurate"   %= 0.99
                                           ,"Inaccurate" %= 0.01
                                           ]
          offer          = UG.Conditional [UG.Clause [UG.Guard "Predisposition" "Trustworthy",   UG.Guard "Accuracy"   "Accurate"]   "Ride"
                                          ,UG.Clause [UG.Guard "Predisposition" "Trustworthy",   UG.Guard "Accuracy" "Inaccurate"] "NoRide"
                                          ,UG.Clause [UG.Guard "Predisposition" "Untrustworthy", UG.Guard "Accuracy"   "Accurate"] "NoRide"
                                          ,UG.Clause [UG.Guard "Predisposition" "Untrustworthy", UG.Guard "Accuracy" "Inaccurate"]   "Ride"
                                          ]
          location       = UG.Conditional [UG.Clause [UG.Guard "Offer"   "Ride"] "City"
                                          ,UG.Clause [UG.Guard "Offer" "NoRide"] "Desert"
                                          ]
          action         = UG.Conditional [UG.Clause [UG.Guard "Predisposition" "Trustworthy", UG.Guard "Location" "City"] "Pay"
                                          ,UG.Clause [] "NoPay"
                                          ]
          value          = UG.Conditional [UG.Clause [UG.Guard "Action"   "Pay", UG.Guard "Location" "City"]    "-1000"
                                          ,UG.Clause [UG.Guard "Action" "NoPay", UG.Guard "Location" "City"]        "0"
                                          ,UG.Clause []                                                      "-1000000"
                                          ]

  data Predisposition = Trustworthy | Untrustworthy deriving (Eq, Show, Typeable, Data)
  data Accuracy       = Accurate    | Inaccurate    deriving (Eq, Show, Typeable, Data)
  data Location       = City        | Desert        deriving (Eq, Show, Typeable, Data)
  data Action         = Pay         | NoPay         deriving (Eq, Show, Typeable, Data)
  data Offer          = Ride        | NoRide        deriving (Eq, Show, Typeable, Data)
  newtype Value       = Value Int                   deriving (Eq, Show, Typeable, Data)

  instance {-# OVERLAPPING #-} TG.Stateable Value where
    toState (Value n) = State $ show n
    ofState (State s) = Value <$> readMaybe s

  utilityFunction :: Value -> U.Utility
  utilityFunction (Value v) = fromIntegral v

  parfitsHitchhiker =
        distribution [  Trustworthy %= 0.5
                     ,Untrustworthy %= 0.5
                     ]
    .*. distribution [  Accurate %= 0.99
                     ,Inaccurate %= 0.01
                     ]
    .*. choose (when (is   Trustworthy .&. is   Accurate)   Ride
            .|. when (is   Trustworthy .&. is Inaccurate) NoRide
            .|. when (is Untrustworthy .&. is   Accurate) NoRide
            .|. when (is Untrustworthy .&. is Inaccurate)   Ride)
    .*. choose (when (is   Ride) City
            .|. when (is NoRide) Desert)
    .*. choose (when (is Trustworthy .&. is City)   Pay
            .|. elsewise                          NoPay)
    .*. choose (when (is   Pay .&. is City) (Value $    -1000)
            .|. when (is NoPay .&. is City) (Value          0)
            .|. elsewise                    (Value $ -1000000))

  parfitsHitchhikerOf t = t TG.true utilityFunction parfitsHitchhiker

  parfitsHitchhikerInTheCityOf t = t (is City) utilityFunction parfitsHitchhiker

  tests :: IO ()
  tests = hspec $
    describe "Parfit's Hitchhiker" $ do
      it "Parfit's Hitchhiker allows one to pay or no pay" $
        UG.choices "Action" (UG.branches untypedParfitsHitchhiker) `shouldBe` ["NoPay", "Pay"]
      it "Typed graph should compile to the untyped graph" $
        TG.compile parfitsHitchhiker `shouldBe` untypedParfitsHitchhiker
      it "EDT initially chooses to pay"      $ parfitsHitchhikerOf           T.edt                  `shouldBe` [(  Pay,   -1000.0)]
      it "EDT later chooses to no pay"       $ parfitsHitchhikerInTheCityOf  T.edt                  `shouldBe` [(NoPay,       0.0)]
      it "CDT initially chooses to no pay"   $ parfitsHitchhikerOf           T.cdt                  `shouldBe` [(NoPay, -990099.0)]
      it "CDT later still chooses to no pay" $ parfitsHitchhikerInTheCityOf  T.cdt                  `shouldBe` [(NoPay,       0.0)]
      it "FDT initially chooses to pay"      $ parfitsHitchhikerOf          (T.fdt @Predisposition) `shouldBe` [(  Pay,   -1000.0)]
      it "FDT later still chooses to pay"    $ parfitsHitchhikerInTheCityOf (T.fdt @Predisposition) `shouldBe` [(  Pay,   -1000.0)]
