{-# LANGUAGE OverloadedStrings #-}

{- | A tower of language versions, and the expansion of a language.

A 'Tower' is a base language L0 and a list of extensions. Each extension makes
the next version of the language from the one before it, and has one of two
kinds:

* A definitional extension ('Definitional') adds constructors. Each new
  constructor is a production and a template in the language below
  ("Data.CFTA.Lowering"). "Data.CFTA.Extension" checks it.
* An abstraction extension ('Abstraction') splits a production into variants
  with other refinements, for example by a new predicate. The variants have the
  facts of the production. "Data.CFTA.Abstraction" checks it with a solver.

Each extension is checked when it is added, and a bad extension is refused with
the reports of the checks and the term that changes meaning.

__The meaning of a term.__ A term of version k has a meaning in L0. Each level
has a step from a term of its version to a term of the version below. The step
of a definitional extension is its lowering. The step of an abstraction
extension relaxes each variant symbol to the symbol of the production that it
was split from. The meaning is the steps in sequence, from the newest to the
oldest. 'composedLowering' composes the lowerings of the definitional levels
into one lowering to L0.

__Earlier terms.__ A definitional extension keeps the earlier productions.
An abstraction extension can replace a production with variants. 'keptMeaning'
compares the translation of terms from the version below through both
versions, up to the size bound of the tower. 'previewExpand' reports the
first term that changes its translation.

__Expansion.__ 'previewExpand' and 'expand' take the version the caller
expects. They report 'StaleVersion' when the tower has a different version.
A preview contains the next language, the edit, and the new constructors or
variants. 'commit' checks the parent before adding the new level. It reports
'PreviewParentMismatch' if the parent differs at the expected version.

Existing productions and their variants keep their facts. New constructors
start without facts. The extension checks read the source graph with its
facts combined. Exclusions carry forward separately. A constrained
transition returns 'UnsupportedLanguage' during a definitional check.

Use 'predicateSplit' to split a named production by a predicate and its
negation. The variants keep the production's facts.
-}
module Data.CFTA.Tower (
    Tower,
    Extension (..),
    Definition (..),
    Split (..),
    Step (..),
    Level (..),
    Preview,
    previewVersion,
    previewLevel,
    previewUpdate,
    previewConstructors,
    previewVariants,
    TowerError (..),
    MeaningChange (..),
    LevelReport (..),
    tower,
    version,
    languageAt,
    current,
    levels,
    predicateSplit,
    meaning,
    composedLowering,
    keptMeaning,
    previewExpand,
    commit,
    expand,
) where

import Control.Exception (handle)
import Control.Monad (foldM)
import Control.Monad.Except (ExceptT (..), runExceptT)
import Data.List (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Data.Text (Text)

import qualified Data.CFTA as FTA
import Data.CFTA.Abstraction (AbstractionError, checkAbstraction)
import Data.CFTA.Extension (ExtensionError, checkExtension)
import qualified Data.CFTA.Formula as F
import Data.CFTA.Index (Size (..))
import Data.CFTA.Language (Language, ProductionName (..))
import qualified Data.CFTA.Language as L
import qualified Data.CFTA.Language.Source as D
import Data.CFTA.Lowering (Expansion, ExpansionError, Lowering, LoweringError)
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..))
import Data.CFTA.Refinement.Verdict (Entailment (entails), Verdict (..))
import Data.CFTA.Sized (sized, termsOfSize)
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol), symbolRefinement, symbolText)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A new constructor: a production at a state, and its expansion in the language below.
data Definition state = Definition
    { definedState :: !state
    , definedName :: !ProductionName
    , definedSymbol :: !Symbol
    , definedChildren :: ![state]
    , definedExpansion :: !(Expansion Symbol)
    }
    deriving (Eq, Show)

-- | The split of a production into variants with other refinements. A variant has the facts of the production. The production itself stays only if a variant has its name.
data Split state = Split
    { splitState :: !state
    , splitProduction :: !ProductionName
    , splitVariants :: ![(ProductionName, F.Formula)]
    -- ^ The name and the refinement of each variant. The first variant may have the name of the production.
    }
    deriving (Eq, Show)

-- | An extension of a language.
data Extension state
    = -- | New constructors with their expansions.
      Definitional ![Definition state]
    | -- | Productions split into variants.
      Abstraction ![Split state]
    deriving (Eq, Show)

-- | From a term of a version to a term of the version below.
data Step
    = -- | The lowering of the new constructors.
      Lowered !(Lowering Symbol)
    | -- | Each variant symbol is the symbol of the production that it was split from.
      Relaxed !(Map Symbol Symbol)
    deriving (Eq, Show)

-- | A version of the language, with the extension that made it and its step.
data Level state = Level
    { levelExtension :: !(Extension state)
    , levelLanguage :: !(Language state)
    , levelStep :: !Step
    }
    deriving (Eq, Show)

-- | A base language and the levels above it, with the size bound of the tests of meaning.
data Tower state = Tower
    { towerBound :: !Size
    , towerBase :: !(Language state)
    , towerLevels :: ![Level state]
    }
    deriving (Eq, Show)

-- | A term of version k that changes meaning at a level: its meaning before the level and after it.
data MeaningChange = MeaningChange
    { changeLevel :: !Int
    , changeTerm :: !(Term Symbol)
    , changeBefore :: !(Maybe (Term Symbol))
    , changeAfter :: !(Maybe (Term Symbol))
    }
    deriving (Eq, Show)

-- | Why an expansion is refused.
data TowerError state
    = -- | The expected version and the version of the tower.
      StaleVersion !Int !Int
    | -- | The tower at that version differs from the one used to check the preview.
      PreviewParentMismatch
    | -- | An update that the language does not accept.
      InvalidUpdate !(L.UpdateError state)
    | -- | A production to split that the language does not have.
      MissingProduction !state !ProductionName
    | -- | The named variants fail to cover their parent at this state.
      UncoveredSplit !state !ProductionName !Verdict
    | -- | The named variant fails to entail its parent at this state.
      UnsoundSplitVariant !state !ProductionName !ProductionName !Verdict
    | {- | Two splits give one variant symbol from two productions with different
      symbols: the variant symbol and the two parent symbols. The meaning of the
      variant would be one of them, so the extension is refused.
      -}
      AmbiguousVariant !Symbol !Symbol !Symbol
    | -- | Two expansions for one constructor, or an expansion that uses a missing child.
      InvalidLowering !(ExpansionError Symbol)
    | -- | A language that the checks do not handle: a fact with a constraint.
      UnsupportedLanguage !(LoweringError state Symbol)
    | {- | The new level, the reasons why it is not a definitional extension, and the
      first term that changes meaning.
      -}
      NotDefinitional !Int ![ExtensionError state] !(Maybe MeaningChange)
    | -- | The new level, the reasons why it is not an abstraction extension, and the first term that changes meaning.
      NotAbstraction !Int ![AbstractionError state] !(Maybe MeaningChange)
    | -- | The new level and a term that changes meaning, when the checks of the extension find no fault.
      MeaningChanged !Int !MeaningChange
    deriving (Eq, Show)

{- Note [A preview belongs to its parent tower]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The meaning check uses the size bound and the steps down to the base.
Two towers at the same version can have the same current language and
different lowerings. Store the parent tower so commit can compare its
bound, base and levels with the tower supplied by the caller.

Keep the constructor private. Use ordinary functions for the public
accessors. An exported record field would let a caller replace a checked
level with a record update.
-}

-- | A checked expansion of one parent tower.
data Preview state
    = Preview !(Tower state) !(Level state) !(L.Update state) ![Symbol] ![(state, ProductionName, [ProductionName])]
    deriving (Eq, Show)

-- | The version that the new level will have.
previewVersion :: Preview state -> Int
previewVersion (Preview parent _ _ _ _) = version parent + 1

-- | The checked level.
previewLevel :: Preview state -> Level state
previewLevel (Preview _ level _ _ _) = level

-- | The update from the parent language to the new language.
previewUpdate :: Preview state -> L.Update state
previewUpdate (Preview _ _ update _ _) = update

-- | The new constructors of a definitional extension.
previewConstructors :: Preview state -> [Symbol]
previewConstructors (Preview _ _ _ constructors _) = constructors

-- | The split productions with their variants.
previewVariants :: Preview state -> [(state, ProductionName, [ProductionName])]
previewVariants (Preview _ _ _ _ variants) = variants

-- | A tower of the base language, and the size bound of the tests of meaning.
tower :: Size -> Language state -> Tower state
tower bound base = Tower bound base []

-- | The number of levels above the base: the base is version 0.
version :: Tower state -> Int
version = length . towerLevels

-- | The levels above the base, the oldest first.
levels :: Tower state -> [Level state]
levels = towerLevels

-- | The language of a version. 'Nothing' for a version that the tower does not have.
languageAt :: Tower state -> Int -> Maybe (Language state)
languageAt t k
    | k == 0 = Just (towerBase t)
    | k > 0 && k <= version t = Just (levelLanguage $ towerLevels t !! (k - 1))
    | otherwise = Nothing

-- | The language of the newest version.
current :: Tower state -> Language state
current t = maybe (towerBase t) levelLanguage $ listToMaybe $ reverse $ towerLevels t

-- | The split of a production that has a refinement by a predicate: the variants where the predicate holds and where it does not.
predicateSplit :: Text -> state -> ProductionName -> F.Formula -> F.Formula -> Split state
predicateSplit suffix state production refinement predicate =
    Split
        state
        production
        [ (ProductionName (productionNameText production <> "." <> suffix), F.conjunction [refinement, predicate])
        , (ProductionName (productionNameText production <> ".not-" <> suffix), F.conjunction [refinement, F.Not predicate])
        ]

-- | The steps that give the meaning of a term of a version, the newest first.
stepsTo :: Int -> Tower state -> [Step]
stepsTo k t = reverse $ map levelStep $ take k $ towerLevels t

-- | Apply a step to a term.
applyStep :: Step -> Term Symbol -> Maybe (Term Symbol)
applyStep step term = case step of
    Lowered lowering -> Lowering.lower lowering term
    Relaxed relaxed -> Just $ go relaxed term
  where
    go relaxed (Term.Node symbol children) = Term.Node (Map.findWithDefault symbol symbol relaxed) (map (go relaxed) children)

-- | The meaning of a term through steps, the newest first.
throughSteps :: [Step] -> Term Symbol -> Maybe (Term Symbol)
throughSteps steps term = foldM (flip applyStep) term steps

{- | Translate a term of version k to L0. Check membership separately if the
term comes from outside the tower. The result is 'Nothing' for an invalid
version or a constructor with a different arity from its expansion.
-}
meaning :: Tower state -> Int -> Term Symbol -> Maybe (Term Symbol)
meaning t k term
    | k < 0 || k > version t = Nothing
    | otherwise = throughSteps (stepsTo k t) term

{- | The lowering of the definitional levels up to a version, composed into
one lowering to L0. The abstraction levels do not change a constructor that
a lowering expands, so they are not in it.
-}
composedLowering :: Tower state -> Int -> Either (ExpansionError Symbol) (Lowering Symbol)
composedLowering t k =
    foldM (flip Lowering.compose) Lowering.identity [lowering | Lowered lowering <- map levelStep $ take k $ towerLevels t]

-- | The source of a language with its facts combined.
graphOf :: Language state -> FTA.PlainFTA state Symbol
graphOf = D.compileGraph . L.source

-- | The terms of a language with at most the given number of nodes.
termsUpTo :: (Ord state) => Size -> Language state -> [Term Symbol]
termsUpTo (Size bound) language = case sized (graphOf language) of
    Left _ -> []
    Right classes -> [term | size <- [1 .. bound], term <- termsOfSize classes (Size size)]

-- | The terms of the version below a level that change meaning when the level is added, with the steps of the version below and the new step.
changesAt :: (Ord state) => Size -> Int -> Language state -> [Step] -> Step -> [MeaningChange]
changesAt bound level below older new =
    [ MeaningChange level term before after
    | term <- termsUpTo bound below
    , let before = throughSteps older term
    , let after = throughSteps (new : older) term
    , before /= after
    ]

-- | The result of the test of the meaning of the old terms at one level.
data LevelReport = LevelReport
    { reportLevel :: !Int
    , reportChecked :: !Int
    -- ^ The terms of the version below that were tested.
    , reportChanges :: ![MeaningChange]
    }
    deriving (Eq, Show)

{- | For each level, compare the translations of terms of the previous level
up to the size bound. If size enumeration cannot handle that level's guards,
the report counts zero terms.
-}
keptMeaning :: (Ord state) => Tower state -> [LevelReport]
keptMeaning t =
    [ LevelReport
        k
        (length $ termsUpTo (towerBound t) below)
        (changesAt (towerBound t) k below (stepsTo (k - 1) t) (levelStep level))
    | (k, level) <- zip [1 ..] (towerLevels t)
    , Just below <- [languageAt t (k - 1)]
    ]

{- | What an extension would do to a tower that the caller expects at a
version. The tower is not changed. The result is a 'TowerError' when the tower
is at another version, the update does not apply, or the checks of the
extension or the test of meaning find a fault.
-}
previewExpand ::
    (Ord state) => Entailment -> Int -> Extension state -> Tower state -> IO (Either (TowerError state) (Preview state))
previewExpand entailment expected extension t
    | expected /= version t = pure $ Left $ StaleVersion expected (version t)
    | otherwise = case built of
        Left failure -> pure $ Left failure
        Right (preview, parts) -> do
            let Level _ language step = previewLevel preview
                changes = changesAt (towerBound t) level top (stepsTo (version t) t) step
            reported <- case (extension, step) of
                (Definitional _, Lowered lowering) -> pure $ case checkExtension lowering (graphOf top) (graphOf language) of
                    Left failure -> Left $ UnsupportedLanguage failure
                    Right [] -> Right []
                    Right faults -> Left $ NotDefinitional level faults (listToMaybe changes)
                _ -> do
                    faults <- checkAbstraction entailment (graphOf top) (graphOf language)
                    pure $ if null faults then Right [] else Left $ NotAbstraction level faults (listToMaybe changes)
            case (reported, changes) of
                (Left failure, _) -> pure $ Left failure
                (Right _, change : _) -> pure $ Left $ MeaningChanged level change
                (Right _, []) -> fmap (preview <$) $ runExceptT $ mapM_ checkNamed parts
  where
    level = version t + 1
    top = current t
    prepared update language step = Preview t (Level extension language step) update
    built = case extension of
        Definitional definitions -> do
            lowering <-
                first' InvalidLowering $
                    Lowering.mkLowering [(definedSymbol d, length (definedChildren d), definedExpansion d) | d <- definitions]
            let update = mconcat [L.define (L.at (definedState d) (definedName d)) (definedSymbol d) (definedChildren d) | d <- definitions]
            language <- first' InvalidUpdate $ L.update top update
            Right (prepared update language (Lowered lowering) (map definedSymbol definitions) [], [])
        Abstraction splits -> do
            parts <- traverse splitOf splits
            relaxed <-
                relaxedOf
                    [(FTA.transitionSymbol variant, FTA.transitionSymbol original) | (_, variants, original) <- parts, variant <- variants]
            let update =
                    mconcat
                        ( [ L.editSource $ D.DeleteProduction (splitState s) (splitProduction s)
                          | (s, _, _) <- parts
                          , productionNameText (splitProduction s) `notElem` map (productionNameText . fst) (splitVariants s)
                          ]
                            <> [L.editSource $ D.PutProduction (splitState s) variant | (s, variants, _) <- parts, variant <- variants]
                        )
            language <- first' InvalidUpdate $ L.update top update
            let variants = [(splitState s, splitProduction s, map fst $ splitVariants s) | s <- splits]
            Right (prepared update language (Relaxed relaxed) [] variants, parts)
    first' f = either (Left . f) Right
    -- See Note [The parent of a named split].
    checkNamed (Split state name variants, _, original) = do
        let parent = symbolRefinement $ FTA.transitionSymbol original
        require (UncoveredSplit state name) parent (F.disjunction $ map snd variants)
        mapM_ (\(variant, refinement) -> require (UnsoundSplitVariant state name variant) refinement parent) variants
    require failure antecedent consequent = ExceptT $ do
        verdict <- handle (\(TimeLimitReached _) -> pure Unknown) $ entails entailment antecedent consequent
        pure $ if verdict == Yes then Right () else Left $ failure verdict
    -- The parent of each variant symbol. Two parents for one variant symbol are refused.
    relaxedOf = foldM addVariant Map.empty
    addVariant seen (variant, parent) = case Map.lookup variant seen of
        Just other | other /= parent -> Left $ AmbiguousVariant variant other parent
        _ -> Right $ Map.insert variant parent seen
    -- The variants of a split, with the production that is split.
    splitOf split = do
        original <-
            maybe (Left $ MissingProduction (splitState split) (splitProduction split)) Right $
                find
                    ((== splitProduction split) . D.annotationName . FTA.transitionConstraint)
                    (FTA.transitionsFrom (D.sourceGraph $ L.source top) (splitState split))
        let variant (name, refinement) =
                original
                    { FTA.transitionSymbol = RefinedSymbol (Symbol $ symbolText $ FTA.transitionSymbol original) refinement
                    , FTA.transitionConstraint = (FTA.transitionConstraint original){D.annotationName = name}
                    }
        Right (split, map variant (splitVariants split), original)

{- Note [The parent of a named split]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
checkAbstraction compares all productions with the same state, symbol text,
children and constraint. A sibling at that key can cover a missing value or
admit a variant that exceeds its named parent's refinement. The Relaxed step
maps each variant to that specific parent. Check both implications for the
named split as well as the graph-wide obligations.
-}

-- | Add the checked level to its parent. See Note [A preview belongs to its parent tower].
commit :: (Eq state) => Tower state -> Preview state -> Either (TowerError state) (Tower state)
commit t (Preview parent level _ _ _)
    | expected /= actual = Left $ StaleVersion expected actual
    | parent /= t = Left PreviewParentMismatch
    | otherwise = Right t{towerLevels = towerLevels t <> [level]}
  where
    expected = version parent
    actual = version t

-- | Add an extension to a tower that the caller expects at a version: a preview and its commit.
expand ::
    (Ord state) => Entailment -> Int -> Extension state -> Tower state -> IO (Either (TowerError state) (Tower state))
expand entailment expected extension t = fmap (>>= commit t) (previewExpand entailment expected extension t)
