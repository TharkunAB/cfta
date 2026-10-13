import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Gen.Internal.Automaton (automatonIndex)
import Data.CFTA.Index (Cardinality (..), ClassRank (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Size (countAtSize, sizeClassSelect)
import Data.CFTA.Sized

-- | Compare the former interned dispatch with the repaired original-row queries.
main :: IO ()
main = do
    let edge label children = FTA.Transition (label :: String) children noConstraint
        graph =
            either (error . show) id $
                FTA.mkFTA
                    ("s" :: String)
                    [ ("s", [edge "f" ["p"], edge "f" ["q"]])
                    , ("p", [edge "a" ["dead"], edge "z" ["leaf"]])
                    , ("q", [edge "m" ["leaf"]])
                    , ("leaf", [edge "k" []])
                    , ("dead", [])
                    ]
        fast = either (error . show) id $ sized graph
        reference = either (error . show) id $ sizedReference graph
        old = either (error . show) id $ automatonIndex id $ fromFTA graph
        Cardinality total = countAtSize old 3
        oldTerms = [rankedValue $ sizeClassSelect old 3 $ ClassRank rank | rank <- [0 .. total - 1]]
    print oldTerms
    print $ oldTerms == termsOfSize reference 3
    print $ termsOfSize fast 3
    print $ termsOfSize reference 3
    print $ termsOfSize fast 3 == termsOfSize reference 3
