import qualified DecisionTheoryTests as DT
import qualified Newcomb as NP
import qualified V2.Newcomb as V2.NP
import qualified XorBlackmail as XB
import qualified V2.XorBlackmail as V2.XB
import qualified DeathInDamascus as DiD
import qualified ParfitsHitchhiker as PH

main :: IO ()
main = do DT.tests
          NP.tests
          XB.tests
          DiD.tests
          PH.tests
          V2.NP.tests
          V2.XB.tests
