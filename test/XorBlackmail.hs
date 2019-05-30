{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- HLINT ignore "Redundant do" -}

module XorBlackmail (tests) where

  import Test.Hspec

  import Data.Data

  import DecisionTheory.Base
  import DecisionTheory.Probability
  import qualified DecisionTheory.Graph as U
  import DecisionTheory.TypedGraph
  import DecisionTheory.DecisionTheory

  xorBlackmail :: U.Graph U.Stochastic
  xorBlackmail = U.Graph [Labeled "Infestation"    infestation
                         ,Labeled "Predisposition" predisposition
                         ,Labeled "Prediction"     prediction
                         ,Labeled "Observation"    observation
                         ,Labeled "Action"         action
                         ,Labeled "Value"          value
                         ]
    where infestation    = U.Distribution [Probability   "Termites" 0.5
                                          ,Probability "NoTermites" 0.5
                                          ]
          predisposition = U.Distribution [Probability   "Payer" 0.5
                                          ,Probability "Refuser" 0.5
                                          ]
          prediction     = U.Conditional [U.Clause [U.Guard "Infestation" "Termites",   U.Guard "Predisposition"   "Payer"]  "Skeptic"
                                         ,U.Clause [U.Guard "Infestation" "Termites",   U.Guard "Predisposition" "Refuser"] "Gullible"
                                         ,U.Clause [U.Guard "Infestation" "NoTermites", U.Guard "Predisposition"   "Payer"] "Gullible"
                                         ,U.Clause [U.Guard "Infestation" "NoTermites", U.Guard "Predisposition" "Refuser"]  "Skeptic"
                                         ]
          observation    = U.Conditional [U.Clause [U.Guard "Prediction" "Gullible"] "Letter"
                                         ,U.Clause [U.Guard "Prediction"  "Skeptic"] "NoLetter"
                                         ]
          action         = U.Conditional [U.Clause [U.Guard "Predisposition"   "Payer"]   "Pay"
                                         ,U.Clause [U.Guard "Predisposition" "Refuser"] "Refuse"
                                         ]
          value          = U.Conditional [U.Clause [U.Guard "Infestation"   "Termites", U.Guard "Action"    "Pay"] "-1001000"
                                         ,U.Clause [U.Guard "Infestation"   "Termites", U.Guard "Action" "Refuse"] "-1000000"
                                         ,U.Clause [U.Guard "Infestation" "NoTermites", U.Guard "Action"    "Pay"]    "-1000"
                                         ,U.Clause [U.Guard "Infestation" "NoTermites", U.Guard "Action" "Refuse"]        "0"
                                         ]


  data Infestation    = Termites   | NoTermites  deriving (Eq, Show, Typeable, Data)
  data Predisposition = Payer      | Refuser     deriving (Eq, Show, Typeable, Data)
  data Prediction     = Skeptic    | Gullible    deriving (Eq, Show, Typeable, Data)
  data Observation    = Letter     | NoLetter    deriving (Eq, Show, Typeable, Data)
  data Action         = Pay        | Refuse      deriving (Eq, Show, Typeable, Data)
  newtype Value       = Value Int                deriving (Eq, Show, Typeable, Data)

  instance {-# OVERLAPS #-} Stateable Value where
    toState (Value n) = State $ show n

  typedXorBlackmail =
        Distribution [  Termites %= 0.5
                     ,NoTermites %= 0.5
                     ]
    :*: Distribution [  Payer %= 0.5
                     ,Refuser %= 0.5
                     ]
    :*: Case (When (Is   Termites :&: Is   Payer) Skeptic
          :|: When (Is   Termites :&: Is Refuser) Gullible
          :|: When (Is NoTermites :&: Is   Payer) Gullible
          :|: When (Is NoTermites :&: Is Refuser) Skeptic)
    :*: Case (When (Is Gullible)   Letter
          :|: When (Is Skeptic)  NoLetter)
    :*: Case (When (Is   Payer) Pay
          :|: When (Is Refuser) Refuse)
    :*: Case (When (Is   Termites :&: Is Pay)    (Value $ -1001000)
          :|: When (Is   Termites :&: Is Refuse) (Value $ -1000000)
          :|: When (Is NoTermites :&: Is Pay)    (Value $    -1000)
          :|: When (Is NoTermites :&: Is Refuse) (Value          0))

  xorBlackmailOf :: ([U.Guard] -> Search -> U.Graph U.Stochastic -> a) -> a
  xorBlackmailOf t = t [U.Guard "Observation" "Letter"] stdSearch xorBlackmail

  tests :: IO ()
  tests = hspec $ do
    describe "XOR Blackmail" $ do
      it "XOR Blackmail allows one to pay or refuse" $ do
        U.choices "Action" (U.branches xorBlackmail) `shouldBe` ["Pay", "Refuse"]
      it "EDT chooses to pay" $ do
        xorBlackmailOf edt `shouldBe` ("Pay", -1000.0)
      it "CDT chooses to refuse" $ do
        xorBlackmailOf cdt `shouldBe` ("Refuse", -1000000.0)
      it "FDT chooses to refuse" $ do
        xorBlackmailOf (fdt "Predisposition") `shouldBe` ("Refuse", -1000000.0)
      it "Typed graph should compile to the untyped graph" $ do
        compile typedXorBlackmail `shouldBe` xorBlackmail
