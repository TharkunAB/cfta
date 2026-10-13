import Control.Exception (evaluate)
import Control.Monad (void)
import Data.CFTA.Gen.Internal.Automaton (automatonIndex)
import Data.CFTA.Index (Cardinality (..), ClassRank (..))
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Size (countAtSize, sizeClassSelect)
import System.Environment (getArgs)

-- | Run separate processes with tie-a and tie-b to compare colliding-key ranks.
main :: IO ()
main = do
    [first] <- getArgs
    let leaf name = Common.Node [Common.Edge name []] :: Common.Node String
    void $ evaluate $ Common.nodeCount $ leaf first
    let root = Common.createMu $ \self -> Common.Node [Common.Edge "tie-a" [], Common.Edge "tie-b" [], Common.Edge "tie-s" [self]]
        index = either (error . show) id $ automatonIndex (const ()) root
        Cardinality count = countAtSize index 1
    print [rankedValue $ sizeClassSelect index 1 $ ClassRank rank | rank <- [0 .. count - 1]]
