{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- HLINT ignore "Redundant do" -}

module XorBlackmail (tests) where
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

  untypedXorBlackmail :: UG.Graph UG.Stochastic
  untypedXorBlackmail = UG.Graph [Labeled "Infestation"    infestation
                                 ,Labeled "Predisposition" predisposition
                                 ,Labeled "Prediction"     prediction
                                 ,Labeled "Observation"    observation
                                 ,Labeled "Action"         action
                                 ,Labeled "Value"          value
                                 ]
    where infestation    = UG.Distribution [  "Termites" %= 0.5
                                           ,"NoTermites" %= 0.5
                                           ]
          predisposition = UG.Distribution [  "Payer" %= 0.5
                                           ,"Refuser" %= 0.5
                                           ]
          prediction     = UG.Conditional [UG.Clause [UG.Guard "Infestation" "Termites",   UG.Guard "Predisposition"   "Payer"]  "Skeptic"
                                          ,UG.Clause [UG.Guard "Infestation" "Termites",   UG.Guard "Predisposition" "Refuser"] "Gullible"
                                          ,UG.Clause [UG.Guard "Infestation" "NoTermites", UG.Guard "Predisposition"   "Payer"] "Gullible"
                                          ,UG.Clause [UG.Guard "Infestation" "NoTermites", UG.Guard "Predisposition" "Refuser"]  "Skeptic"
                                          ]
          observation    = UG.Conditional [UG.Clause [UG.Guard "Prediction" "Gullible"] "Letter"
                                          ,UG.Clause [UG.Guard "Prediction"  "Skeptic"] "NoLetter"
                                          ]
          action         = UG.Conditional [UG.Clause [UG.Guard "Predisposition"   "Payer"]   "Pay"
                                          ,UG.Clause [UG.Guard "Predisposition" "Refuser"] "Refuse"
                                          ]
          value          = UG.Conditional [UG.Clause [UG.Guard "Infestation"   "Termites", UG.Guard "Action"    "Pay"] "-1001000"
                                          ,UG.Clause [UG.Guard "Infestation"   "Termites", UG.Guard "Action" "Refuse"] "-1000000"
                                          ,UG.Clause [UG.Guard "Infestation" "NoTermites", UG.Guard "Action"    "Pay"]    "-1000"
                                          ,UG.Clause [UG.Guard "Infestation" "NoTermites", UG.Guard "Action" "Refuse"]        "0"
                                          ]

  data Infestation    = Termites   | NoTermites  deriving (Eq, Show, Typeable, Data)
  data Predisposition = Payer      | Refuser     deriving (Eq, Show, Typeable, Data)
  data Prediction     = Skeptic    | Gullible    deriving (Eq, Show, Typeable, Data)
  data Observation    = Letter     | NoLetter    deriving (Eq, Show, Typeable, Data)
  data Action         = Pay        | Refuse      deriving (Eq, Show, Typeable, Data)
  newtype Value       = Value Int                deriving (Eq, Show, Typeable, Data)

  instance {-# OVERLAPPING #-} TG.Stateable Value where
    toState (Value n) = State $ show n
    ofState (State s) = Value <$> readMaybe s

  utilityFunction :: Value -> U.Utility
  utilityFunction (Value v) = fromIntegral v

  xorBlackmail =
        distribution [  Termites %= 0.5
                     ,NoTermites %= 0.5
                     ]
    .*. distribution [  Payer %= 0.5
                     ,Refuser %= 0.5
                     ]
    .*. choose (when (is   Termites .&. is   Payer) Skeptic
            .|. when (is   Termites .&. is Refuser) Gullible
            .|. when (is NoTermites .&. is   Payer) Gullible
            .|. when (is NoTermites .&. is Refuser) Skeptic)
    .*. choose (when (is Gullible)   Letter
            .|. when (is Skeptic)  NoLetter)
    .*. choose (when (is   Payer) Pay
            .|. when (is Refuser) Refuse)
    .*. choose (when (is   Termites .&. is Pay)    (Value $ -1001000)
            .|. when (is   Termites .&. is Refuse) (Value $ -1000000)
            .|. when (is NoTermites .&. is Pay)    (Value $    -1000)
            .|. when (is NoTermites .&. is Refuse) (Value          0))

  xorBlackmailOf t = t (is Letter) utilityFunction xorBlackmail

  tests :: IO ()
  tests = hspec $
    describe "XOR Blackmail" $ do
      it "XOR Blackmail allows one to pay or refuse" $
        UG.choices "Action" (UG.branches untypedXorBlackmail) `shouldBe` ["Pay", "Refuse"]
      it "Typed graph should compile to the untyped graph" $ do
        TG.compile xorBlackmail `shouldBe` untypedXorBlackmail
      it "EDT chooses to pay"    $ xorBlackmailOf  T.edt                  `shouldBe` (Pay,       -1000.0)
      it "CDT chooses to refuse" $ xorBlackmailOf  T.cdt                  `shouldBe` (Refuse, -1000000.0)
      it "FDT chooses to refuse" $ xorBlackmailOf (T.fdt @Predisposition) `shouldBe` (Refuse, -1000000.0)
