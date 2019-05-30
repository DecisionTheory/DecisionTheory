import qualified DecisionTheoryTests as DT
import qualified Newcomb as NP
import qualified XorBlackmail as XB
import qualified DeathInDamascus as DiD
import qualified ParfitsHitchhiker as PH

main :: IO ()
main = do DT.tests
          NP.tests
          XB.tests
          DiD.tests
          PH.tests
