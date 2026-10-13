import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Gen.Internal.Automaton (automatonIndex)
import Data.CFTA.Index (Cardinality (..), ClassRank (..))
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Size (countAtSize, sizeClassSelect)
import Data.CFTA.Sized

-- | Compare duplicate-edge canonical order before and after the former import.
main :: IO ()
main = do
    let edge label children = FTA.Transition (label :: String) children noConstraint
        graph =
            either (error . show) id $
                FTA.mkFTA
                    ("s" :: String)
                    [ ("s", [edge "f" ["p", "r"], edge "f" ["q", "t"]])
                    , ("p", [edge "a" [], edge "a" [], edge "z" []])
                    , ("q", [edge "a" [], edge "m" []])
                    , ("r", [edge "r" []])
                    , ("t", [edge "t" []])
                    ]
        fast = either (error . show) id $ sized graph
        reference = either (error . show) id $ sizedReference graph
        old = either (error . show) id $ automatonIndex id $ fromFTA graph
        Cardinality total = countAtSize old 3
        oldTerms = [rankedValue $ sizeClassSelect old 3 $ ClassRank rank | rank <- [0 .. total - 1]]
    print $ graph == FTA.trim graph
    print oldTerms
    print $ oldTerms == termsOfSize reference 3
    print $ termsOfSize fast 3
    print $ termsOfSize reference 3
    print $ termsOfSize fast 3 == termsOfSize reference 3
