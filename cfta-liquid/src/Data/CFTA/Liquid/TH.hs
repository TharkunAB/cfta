{-# LANGUAGE TemplateHaskell #-}

{- | Read the Liquid Haskell specifications of the current module at compile
time.

@
sortedLists = deriveLTAFromLiquid \@(IncList Integer) 8 (atom \@Integer every) $(liquidSpecifications) "IncListBounded"
@

The splice reads the source file of the module, and it gives the text of its
@{\-\@ \@-\}@ comments as 'Data.CFTA.Liquid.Specifications'. It parses the text
when the module compiles, so a parse error stops the compilation with the
message of Liquid Haskell. The translation runs when the program builds the
generator, because it needs the 'Data.CFTA.Generic.HasFTA' instance of the
datatype, which the module itself defines.
-}
module Data.CFTA.Liquid.TH (liquidSpecifications) where

import Language.Haskell.TH (Exp, Q, loc_filename, location, runIO)
import Language.Haskell.TH.Syntax (addDependentFile, lift)

import Data.CFTA.Liquid (LiquidError (ParseErrors), parseSpecifications, specificationComments, specificationsOf)
import qualified Data.CFTA.Liquid as Liquid

-- | The specifications of the current module, as an expression of type 'Data.CFTA.Liquid.Specifications'.
liquidSpecifications :: Q Exp
liquidSpecifications = do
    file <- loc_filename <$> location
    addDependentFile file
    source <- runIO $ readFile file
    let specs = specificationsOf file source
    case parseSpecifications specs of
        Left (ParseErrors errors) -> fail $ unlines errors
        Left err -> fail $ show err
        Right _ -> [|Liquid.specifications $(lift $ specificationComments specs)|]
