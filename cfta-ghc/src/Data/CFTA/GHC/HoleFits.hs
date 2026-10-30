{-# LANGUAGE OverloadedStrings #-}

{- | A typed-hole plugin: after GHC's own valid hole fits, fits of several
components, which Hectare proposes and GHC's typechecker checks
("Data.CFTA.GHC.Fits").

> ghc -fplugin=Data.CFTA.GHC.HoleFits Holes.hs

For each hole, the plugin takes the candidates that GHC checks for its own
fits, all the names in scope (GHC checks only the locals when the hole's
type is a type variable), and the hole's type, implications, and relevant
constraints (the 'TypedHole'). A hole of a function type gets its fits as lambdas: each
argument of the type is a variable that the fit uses once, as in a Hoogle+
query. The plugin prints such a fit eta reduced, as @h b@ for
@\\x1 -> h b x1@. The plugin drops the fits that GHC finds itself (one identifier
applied to the arguments in order, or @id@ as @\\x1 -> x1@). A fit can call
a definition that holds the hole, as a recursive call, with two exceptions,
because such a call loops: no call when the hole is the whole right-hand
side of the definition's only equation (@count = _@), and no call with the
parameters of the equation that holds the hole (@sizeOf m@ in
@sizeOf m = case m of Just ys -> _@). When the module does not parse with
GHC's parser (it uses CPP), a fit does not call a top-level definition that
holds the hole.
Hectare's rule 'hectareAvoid' applies: a list function is not applied to
@[]@. A fit with the normal form of an earlier fit is skipped
('optionNormalForms'), and a fit that ignores part of itself or drops an
argument ('comesLast') comes after the others.

The plugin's fits come after GHC's. GHC keeps the first
@-fmax-valid-hole-fits@ fits after the plugin, so the plugin's driver hook
raises that limit by the plugin's number of fits, and the plugin puts its
fits after as many of GHC's fits as the limit was without the plugin. So GHC
shows as many of its own fits as without the plugin, then the plugin's, and
says as before when it suppressed some of its own. When the search fails,
the plugin gives GHC's fits unchanged.

The options apply to each hole:

> -fplugin-opt=Data.CFTA.GHC.HoleFits:size=4       the largest fit, in leaves
> -fplugin-opt=Data.CFTA.GHC.HoleFits:fits=5       the number of fits
> -fplugin-opt=Data.CFTA.GHC.HoleFits:seconds=1    the time of the search
> -fplugin-opt=Data.CFTA.GHC.HoleFits:programs=N   the number of Hectare's programs
> -fplugin-opt=Data.CFTA.GHC.HoleFits:normal-forms=off   keep the fits with equal normal forms
> -fplugin-opt=Data.CFTA.GHC.HoleFits:rank            order the fits with a decision model
> -fplugin-opt=Data.CFTA.GHC.HoleFits:rank-pool=50    the number of fits that the model orders
> -fplugin-opt=Data.CFTA.GHC.HoleFits:rank-seconds=60 the time limit of a question
> -fplugin-opt=Data.CFTA.GHC.HoleFits:rank-model=NAME the model on the server
> -fplugin-opt=Data.CFTA.GHC.HoleFits:rank-keep-alive=0   how long the server keeps the model loaded

> -fplugin-opt=Data.CFTA.GHC.HoleFits:model=base.cfta   order the fits with a fit model
> -fplugin-opt=Data.CFTA.GHC.HoleFits:model-module=K    add the counts of the module K times
> -fplugin-opt=Data.CFTA.GHC.HoleFits:hole-context=off  score the root of each fit as a right-hand side
> -fplugin-opt=Data.CFTA.GHC.HoleFits:model-search=best-first  search the typed space in the model's order

With @model@, the plugin reads a fit model ("Data.CFTA.GHC.Model", the text
form @fit-model 1;@ in a @.cfta@ file, which @cfta-fit-model@ builds from
Haskell sources) once for each module, and orders the fits by the model's
score. By default the search keeps its own mode: the plugin takes a pool of
at least 50 fits, and the model orders them, the fits that use every part
first. With @model-search=best-first@, the search is mode (b) ('States') and
lists the programs of all sizes in the order of the model's score, best
first ('optionScore'); it finds more fits, but needs a few seconds for each
hole. The plugin also reads the module of the first hole with GHC's parser
("Data.CFTA.GHC.Corpus"): the probability of @var@ (a name outside the
library) goes to the module's own names in proportion to their uses in the
module ('tokenScoreShared'), so the model knows which of the names in scope
the module calls. With @model-module@, it also adds the counts of that
module, multiplied by K, to the model, for all the holes of the module.
@model-module@ needs @model@. A model that the plugin cannot read gives a
warning, and the fits keep their order. The root of each fit has the context
of its hole: in @foldr f _ xs@, the second argument of @foldr@ ('scorerFor').
With @hole-context=off@, it has the context of a right-hand side.

With @rank@, a decision model orders the plugin's fits
("Data.CFTA.GHC.Rank"). It needs a running Ollama
(@http://localhost:11434@) with a model that has the capability
"decision": by default the model of 'Decision.Ollama.defaultOllama'
(Nimble v3, an external model under its own license), or another with
@rank-model@. The plugin searches for @rank-pool@ fits that use every part,
the model orders them in one question, and the plugin shows the best @fits@.
The other @rank-@ options need @rank@. A question that gets no answer in
@rank-seconds@ (60 by default) counts as no answer. By default the server loads the model for each ranked hole
(@rank-keep-alive=0@), about 4 s for each hole, so that a module gets the
same fits each time. With @rank-keep-alive=5m@, the model stays loaded
between the holes, which is faster, but the order of a hole can then depend
on the holes before it; the plugin unloads the model at the end of the
module. When the model does not answer, the fits keep the plugin's order.
-}
module Data.CFTA.GHC.HoleFits (
    plugin,
    PluginOptions (..),
    readOptions,
) where

import Control.Exception (IOException, SomeAsyncException, fromException, throwIO, try)
import Control.Monad (filterM, foldM, join, void)
import Control.Monad.IO.Class (liftIO)
import Data.List (sortBy, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, listToMaybe)
import Data.Ord (Down (..))
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.IO (hPutStrLn, stderr)
import Text.Read (readMaybe)

import Data.CFTA.GHC.Corpus (holeContext, holeEquations, moduleNames, moduleTerms, parserOf)
import Data.CFTA.GHC.Fits
import Data.CFTA.GHC.Model (FitModel (..), fromTerms, merge, parseFitModel, scale, tokenScoreShared)
import Data.CFTA.GHC.Rank (Ranking (..), defaultRanking, holeState, rankedFits, rankingModel)
import Data.CFTA.Gen.Synthesis (Program (..))
import Data.CFTA.Gen.Synthesis.States (EdgeOrder (..), Walking (..))
import Decision.Ollama (Ollama (..), unload)
import GHC.Builtin.Names (gHC_INTERNAL_BASE, gHC_INTERNAL_ERR, gHC_INTERNAL_UNSAFE_COERCE)
import GHC.Builtin.Types (consDataCon, nilDataCon, tupleDataCon)
import GHC.Core.ConLike (ConLike (RealDataCon))
import GHC.Core.DataCon (dataConName, dataConNonlinearType, dataConWrapId)
import GHC.Core.Multiplicity (scaledMult, scaledThing)
import GHC.Core.TyCo.FVs (tyCoVarsOfTypesList)
import GHC.Core.Type (Type, getTyVar_maybe, isManyTy)
import GHC.Data.FastString (unpackFS)
import GHC.Data.IOEnv (getEnv, runIOEnv)
import GHC.Driver.DynFlags (
    DynFlags (maxValidHoleFits),
    GeneralFlag (Opt_IgnoreInterfacePragmas),
    HasDynFlags (getDynFlags),
    gopt_unset,
 )
import GHC.Driver.Env (HscEnv, hscUpdateFlags, hsc_logger)
import GHC.Driver.Plugins (CommandLineOption, Plugin (..), defaultPlugin, purePlugin)
import GHC.Driver.Ppr (showSDoc)
import GHC.Tc.Errors.Hole.FitTypes (HoleFit (RawHoleFit), HoleFitCandidate (..))
import GHC.Tc.Errors.Hole.Plugin (HoleFitPlugin (..), HoleFitPluginR (..))
import GHC.Tc.Types (env_top)
import GHC.Tc.Types.BasicTypes (TcBinder (..), TcTyThing (AGlobal, ATcId, tct_id))
import GHC.Tc.Types.Constraint (Hole (..))
import GHC.Tc.Types.CtLoc (CtLoc, ctLocEnv, ctLocSpan, ctl_bndrs)
import GHC.Tc.Utils.Env (tcLookup)
import GHC.Tc.Utils.Monad (
    TcM,
    TcRef,
    getGlobalRdrEnv,
    liftZonkM,
    newTcRef,
    readTcRef,
    tryTc,
    updTcRef,
    writeTcRef,
 )
import GHC.Tc.Utils.TcMType (readMetaTyVar)
import GHC.Tc.Utils.TcType (MetaDetails (Flexi), isFlexi, isMetaTyVar, metaTyVarRef, tcSplitFunTys, tcSplitSigmaTy)
import GHC.Tc.Zonk.TcType (zonkTcType, zonkTcTypes)
import GHC.Types.Basic (Boxity (Boxed), isTopLevel)
import GHC.Types.Id (Id, idMult, idName, idType)
import GHC.Types.Name (
    Name,
    getName,
    getOccName,
    getOccString,
    isSymOcc,
    nameModule_maybe,
    pprPrefixName,
    stableNameCmp,
 )
import GHC.Types.Name.Reader (GlobalRdrElt, globalRdrEnvElts, greName, gre_lcl)
import GHC.Types.Name.Set (elemNameSet, emptyNameSet, extendNameSet)
import GHC.Types.SrcLoc (srcSpanFile, srcSpanStartCol, srcSpanStartLine)
import GHC.Types.TyThing (TyThing (AConLike, AnId))
import GHC.Types.Var (isTcTyVar)
import GHC.Utils.Outputable (SDoc, char, hcat, hsep, parens, ppr, text, (<+>))
import GHC.Utils.Panic (GhcException (CmdLineError), throwGhcExceptionIO)

-- | The plugin: enable it with @-fplugin=Data.CFTA.GHC.HoleFits@.
plugin :: Plugin
plugin =
    defaultPlugin
        { holeFitPlugin = either (const Nothing) (Just . holeFits) . readOptions
        , driverPlugin = raiseLimit
        , pluginRecompile = purePlugin
        }

-- | The options of the plugin: those of the search, and the ranking by a decision model, if any.
data PluginOptions = PluginOptions
    { pluginSearch :: Options
    , pluginRanking :: Maybe Ranking
    , pluginModel :: Maybe FilePath
    -- ^ The file of a fit model.
    , pluginModuleWeight :: Maybe Integer
    -- ^ The factor of the counts of the module, which the model gets.
    , pluginHoleContext :: Bool
    -- ^ Whether the root of a fit has the context of the hole, or always @top@.
    , pluginRerank :: Bool
    {- ^ Whether the model orders the fits of the search (a pool of at least
    50, the default), or the search itself (@model-search=best-first@).
    -}
    }

{- | The options of the plugin, from its @-fplugin-opt@ arguments
(@NAME=VALUE@, or @NAME@ for a switch). Without them: fits of up to four
leaves, five fits, one second for each hole, Hectare's curried types, and no
ranking.
-}
readOptions :: [CommandLineOption] -> Either String PluginOptions
readOptions arguments = do
    (options, ranking, ranked, settings) <- foldM set (search0, defaultRanking, False, []) arguments
    let model = lastValue "model"
    weight <-
        traverse
            (\value -> maybe (Left ("not a number in model-module=" <> value)) Right (readMaybe value))
            (lastValue "model-module")
    case settings of
        setting : _
            | not ranked -> Left (setting <> " needs the option rank: the ranking is on only with rank")
        _
            | Just _ <- weight, Nothing <- model -> Left "model-module needs the option model"
            | otherwise ->
                Right
                    ( PluginOptions
                        options
                        (if ranked then Just ranking else Nothing)
                        model
                        weight
                        (lastValue "hole-context" /= Just "off")
                        (lastValue "model-search" /= Just "best-first")
                    )
  where
    search0 = defaultOptions{optionMaximumSize = 4, optionFits = 5, optionSeconds = Just 1, optionAvoid = hectareAvoid}
    set (options, ranking, ranked, settings) argument = case break (== '=') argument of
        ("size", '=' : value) -> (\size -> search (\o -> o{optionMaximumSize = size})) <$> number value
        ("fits", '=' : value) -> (\fits -> search (\o -> o{optionFits = fits})) <$> number value
        ("seconds", '=' : value) -> (\seconds -> search (\o -> o{optionSeconds = Just seconds})) <$> number value
        ("programs", '=' : value) -> (\programs -> search (\o -> o{optionMaximumPrograms = Just programs})) <$> number value
        ("first-order", "") -> Right (search (\o -> o{optionCurried = False}))
        ("only-defaulted", "") -> Right (search (\o -> o{optionCurried = True, optionOnlyDefaulted = True}))
        ("no-type-domains", "") -> Right (search (\o -> o{optionTypeDomains = False}))
        ("normal-forms", '=' : "on") -> Right (search (\o -> o{optionNormalForms = True}))
        ("normal-forms", '=' : "off") -> Right (search (\o -> o{optionNormalForms = False}))
        ("rank", "") -> Right (options, ranking, True, settings)
        ("model", '=' : _) -> Right (options, ranking, ranked, settings)
        ("model-module", '=' : _) -> Right (options, ranking, ranked, settings)
        ("hole-context", '=' : "on") -> Right (options, ranking, ranked, settings)
        ("hole-context", '=' : "off") -> Right (options, ranking, ranked, settings)
        ("model-search", '=' : "best-first") -> Right (options, ranking, ranked, settings)
        ("model-search", '=' : "rerank") -> Right (options, ranking, ranked, settings)
        ("rank-pool", '=' : value) -> (\pool -> setting (\r -> r{rankingPool = pool})) <$> number value
        ("rank-seconds", '=' : value) -> (\seconds -> setting (\r -> r{rankingSeconds = seconds})) <$> number value
        ("rank-model", '=' : value) -> Right (setting (server (\o -> o{ollamaModel = Text.pack value})))
        ("rank-keep-alive", '=' : value) -> Right (setting (server (\o -> o{ollamaKeepAlive = Text.pack value})))
        _ ->
            Left
                ( "unknown option "
                    <> argument
                    <> "; the options are size, fits, seconds, programs, first-order, only-defaulted, no-type-domains, normal-forms, model, model-module, hole-context, model-search, rank, rank-pool, rank-seconds, rank-model, and rank-keep-alive"
                )
      where
        search change = (change options, ranking, ranked, settings)
        -- A setting of the ranking, which needs the option rank.
        setting change = (options, change ranking, ranked, settings <> [takeWhile (/= '=') argument])
        server change current = current{rankingServer = change (rankingServer current)}
        number :: (Read a) => String -> Either String a
        number value = maybe (Left ("not a number in " <> argument)) Right (readMaybe value)
    -- The value of the last argument NAME=VALUE with a name.
    lastValue name = case [value | argument <- arguments, (found, '=' : value) <- [break (== '=') argument], found == name] of
        [] -> Nothing
        values -> Just (last values)

{- | Raise @-fmax-valid-hole-fits@ by the plugin's number of fits, because
GHC cuts the list of fits after the plugin, and read the unfoldings of the
interfaces (no @-fignore-interface-pragmas@, which @-O0@ implies), for the
normal forms of "Data.CFTA.GHC.NormalForm". Stop at a wrong option.
-}
raiseLimit :: [CommandLineOption] -> HscEnv -> IO HscEnv
raiseLimit arguments environment = case readOptions arguments of
    Left problem -> throwGhcExceptionIO (CmdLineError ("Data.CFTA.GHC.HoleFits: " <> problem))
    Right options -> pure (hscUpdateFlags (raise (optionFits (pluginSearch options))) environment)
  where
    raise fits flags = (flags{maxValidHoleFits = (+ fits) <$> maxValidHoleFits flags}) `gopt_unset` Opt_IgnoreInterfacePragmas

{- | The plugin's hooks. GHC calls the candidate hook once for each hole, and
the fit hook twice: for the valid fits, and for the refinement fits. The
candidate hook keeps the candidates and marks the hole open; the fit hook
searches only for an open hole, and closes it. The state also says whether
a model ranked a hole: then the stop hook, at the end of the module, unloads
a model that the server keeps loaded.
-}
holeFits :: PluginOptions -> HoleFitPluginR
holeFits options =
    HoleFitPluginR
        { hfPluginInit = do
            model <- join <$> traverse readModel (pluginModel options)
            modelReference <- newTcRef (model, Map.empty, False)
            reference <- newTcRef (Nothing, False)
            newTcRef (reference, modelReference)
        , hfPluginRun = \references ->
            HoleFitPlugin
                { candPlugin = \_ scope -> do
                    (reference, _) <- readTcRef references
                    scope <$ updTcRef reference (\(_, ranked') -> (Just scope, ranked'))
                , fitPlugin = \hole fits -> do
                    (reference, modelReference) <- readTcRef references
                    (open, ranked') <- readTcRef reference
                    writeTcRef reference (Nothing, ranked')
                    case open of
                        Just scope -> do
                            (model, uses) <- modelFor options modelReference hole
                            scorer <-
                                traverse
                                    (\found -> if pluginHoleContext options then scorerFor hole uses found else pure (tokenScoreShared found uses ("top", 0)))
                                    model
                            (ours, asked) <- fitsFor options scorer hole scope
                            updTcRef reference (\(open', _) -> (open', ranked' || asked))
                            -- The limit without the plugin: see 'raiseLimit'.
                            limit <- maxValidHoleFits <$> getDynFlags
                            let kept = maybe (length fits) (\raised -> max 0 (raised - optionFits (pluginSearch options))) limit
                            pure (take kept fits <> ours <> drop kept fits)
                        Nothing -> pure fits
                }
        , hfPluginStop = \references -> do
            (reference, _) <- readTcRef references
            (_, ranked') <- readTcRef reference
            case pluginRanking options of
                Just ranking
                    | ranked' && ollamaKeepAlive (rankingServer ranking) /= "0" ->
                        liftIO (void (unload (rankingServer ranking)))
                _ -> pure ()
        }

{- | Read a fit model. A model that the plugin cannot read gives a warning
and no model.
-}
readModel :: FilePath -> TcM (Maybe FitModel)
readModel path = liftIO $ do
    found <- try (Text.readFile path)
    case either (Left . show) parseFitModel (found :: Either IOException Text) of
        Right model -> pure (Just model)
        Left problem -> do
            hPutStrLn
                stderr
                ("Data.CFTA.GHC.HoleFits: the model " <> path <> " is not read, so the fits keep their order: " <> problem)
            pure Nothing

{- | The model of a hole, and how often the module uses each name that is
@var@ for the model: the model of the file, with the counts of the module of
the hole added once for the module, with @model-module@. The plugin reads
the module once, at its first hole.
-}
modelFor ::
    PluginOptions -> TcRef (Maybe FitModel, Map.Map Text Int, Bool) -> TypedHole -> TcM (Maybe FitModel, Map.Map Text Int)
modelFor options reference hole = do
    (loaded, uses, read') <- readTcRef reference
    case (loaded, th_hole hole) of
        (Just model, Just Hole{hole_loc = location}) | not read' -> do
            flags <- getDynFlags
            logger <- hsc_logger . env_top <$> getEnv
            let file = unpackFS (srcSpanFile (ctLocSpan location))
                parser = parserOf flags logger
            -- How often the module uses each name that is var for the model.
            names <- liftIO (moduleNames parser file)
            merged <- case pluginModuleWeight options of
                Just weight -> do
                    terms <- liftIO (moduleTerms parser (modelModules model) (Map.keysSet (modelCandidates model)) file)
                    let own = [kept | kept@(_, term) <- fromMaybe [] terms, length (foldr (:) [] term) >= 2]
                    pure (merge model (scale weight (fromTerms (modelModules model) (modelCandidates model) own)))
                Nothing -> pure model
            let uses' = Map.filterWithKey (\name _ -> Map.notMember name (modelCandidates model)) names
            writeTcRef reference (Just merged, uses', True)
            pure (Just merged, uses')
        (found, _) -> pure (found, uses)

{- | The score of the tokens of the fits of a hole under a model. The root of
a fit has the context of the hole ("Data.CFTA.GHC.Corpus.holeContext"): the
symbol of the node whose child the hole is and the hole's position, as
@foldr/3@ and 1 for @foldr f _ xs@, or @top@ for the body of a right-hand
side. A hole of a function type gets its fits as lambdas: when such a hole
is the child of another node, the root of a fit's body has the context of a
lambda's body, @lambda/1@ and 0.
-}
scorerFor ::
    TypedHole -> Map.Map Text Int -> FitModel -> TcM (Set.Set Text -> Maybe (Text, Int) -> Int -> (Text, Int) -> Double)
scorerFor hole uses model = case th_hole hole of
    Just Hole{hole_ty = holeType, hole_loc = location} -> do
        typ <- liftZonkM (zonkTcType holeType)
        flags <- getDynFlags
        logger <- hsc_logger . env_top <$> getEnv
        let (parameters, _) = tcSplitFunTys typ
            span' = ctLocSpan location
            start = (srcSpanStartLine span', srcSpanStartCol span')
            parser = parserOf flags logger
        context <-
            liftIO
                (holeContext parser (modelModules model) (Map.keysSet (modelCandidates model)) (unpackFS (srcSpanFile span')) start)
        pure . tokenScoreShared model uses $ case context of
            Just found
                | null parameters -> found
                | fst found `notElem` ["top", "expr"] -> ("lambda/1", 0)
            _ -> ("top", 0)
    Nothing -> pure (tokenScoreShared model uses ("top", 0))

{- | The plugin's fits for a hole, best first: none when the hole has no
type, when its type has a @forall@ or a class context at the top, when a
multiplicity is neither @Many@ nor an open multiplicity variable (which GHC
defaults to @Many@), or when the search fails. The flag says whether
a model was asked.
-}
fitsFor ::
    PluginOptions ->
    Maybe (Set.Set Text -> Maybe (Text, Int) -> Int -> (Text, Int) -> Double) ->
    TypedHole ->
    [HoleFitCandidate] ->
    TcM ([HoleFit], Bool)
fitsFor (PluginOptions options' ranking _ _ _ rerank) scorer hole scope = case th_hole hole of
    Nothing -> pure ([], False)
    Just Hole{hole_ty = holeType, hole_loc = location} -> do
        elements <- globalRdrEnvElts <$> getGlobalRdrEnv
        parser <- parserOf <$> getDynFlags <*> (hsc_logger . env_top <$> getEnv)
        let span' = ctLocSpan location
        equations <-
            liftIO (holeEquations parser (unpackFS (srcSpanFile span')) (srcSpanStartLine span', srcSpanStartCol span'))
        let definitions = moduleLocals scope elements
            -- The definitions of the module that hold the hole.
            holding = Set.intersection (binderNames location) definitions
            localNames = Set.fromList [idName identifier | IdHFCand identifier <- scope]
            -- A definition that holds the hole is not a fit when the hole is the
            -- whole right-hand side of its only equation, because a call of it
            -- loops. When the module does not parse, no top-level definition
            -- that holds the hole is a fit.
            looping = maybe holding (\found' -> Set.fromList [Text.unpack name | (name, _, True) <- found']) equations
            -- A definition that holds the hole is a local and a name of the
            -- module: the plugin keeps the local.
            elsewhere element = not (gre_lcl element && getOccString (greName element) `Set.member` definitions)
            everything =
                withoutRepeats (scope <> map GreHFCand (filter elsewhere elements) <> map (NameHFCand . dataConName) syntax)
            syntax = [nilDataCon, consDataCon, tupleDataCon Boxed 2]
            -- The scope in an order that does not depend on uniques.
            byName (name, _, _) (name', _, _) = stableNameCmp name name'
        found <- sortBy byName . catMaybes <$> mapM lookupCandidate everything
        typ <- liftZonkM (zonkTcType holeType)
        types <- liftZonkM (zonkTcTypes [typ' | (_, _, typ') <- found])
        let (variables, context, _) = tcSplitSigmaTy typ
            (parameters, result) = tcSplitFunTys typ
            named =
                uniqueNames
                    [ (name, typ')
                    | ((name, _, _), typ') <- zip found types
                    , not (name `Set.member` localNames && getOccString name `Set.member` looping)
                    ]
            used = Set.fromList (map fst named)
            arguments =
                take
                    (length parameters)
                    [name | index <- [1 :: Int ..], let name = "x" <> Text.pack (show index), name `Set.notMember` used]
            candidates =
                [Candidate label typ' (heads name) False (Just name) | (label, (name, typ')) <- named]
                    <> [Candidate argument (scaledThing parameter) True True Nothing | (argument, parameter) <- zip arguments parameters]
            names = Map.fromList [(label, pprPrefixName name) | (label, (name, _)) <- named]
        -- A binder of a case alternative has a multiplicity variable that GHC
        -- defaults to Many later, so an open variable counts as Many.
        multiplicities <-
            liftZonkM (zonkTcTypes (map scaledMult parameters <> [idMult identifier | (_, identifier, _) <- found]))
        let unrestricted multiplicity =
                isManyTy multiplicity
                    || maybe False (\variable -> isTcTyVar variable && isMetaTyVar variable) (getTyVar_maybe multiplicity)
        if not (null variables && null context) || not (all unrestricted multiplicities)
            then pure ([], False)
            else do
                flexible <-
                    filterM (fmap isFlexi . readMetaTyVar) (filter (\v -> isTcTyVar v && isMetaTyVar v) (tyCoVarsOfTypesList (typ : types)))
                -- The locals of the hole and the arguments of its lambdas are @arg@ for the model.
                -- A definition of the module is @var@, as in the corpus.
                let argumentNames =
                        Set.fromList
                            ( [ label
                              | (label, (name, _)) <- named
                              , name `Set.member` localNames
                              , getOccString name `Set.notMember` definitions
                              ]
                                <> arguments
                            )
                -- A call of the definition of an equation that holds the hole,
                -- with the parameters of the equation, loops at once.
                let labelOf = Map.fromList [(Text.pack (getOccString name), label) | (label, (name, _)) <- named, name `Set.member` localNames]
                    loops =
                        Set.fromList
                            [ foldl App (Var function') (map Var labels)
                            | (function, equationParameters, _) <- fromMaybe [] equations
                            , Just function' <- [Map.lookup function labelOf]
                            , Just labels <- [traverse (>>= (`Map.lookup` labelOf)) equationParameters]
                            ]
                    dropped program = foundByGhc arguments program || program `Set.member` loops
                outcome <- attempt (search (withScorer argumentNames) candidates dropped result)
                -- As 'GHC.Tc.Errors.Hole.withoutUnification', also when the
                -- search stops part way.
                mapM_ (\variable -> writeTcRef (metaTyVarRef variable) Flexi) flexible
                flags <- getDynFlags
                let shown fit = render names arguments (fitProgram fit)
                    plain = Text.pack . showSDoc flags
                    definition = [identifier | IdHFCand identifier <- scope, getOccString identifier `Set.member` holding]
                    locals = [identifier | IdHFCand identifier <- scope, getOccString identifier `Set.notMember` definitions]
                    state =
                        holeState
                            ( (\identifier -> (plain (ppr identifier), plain (ppr (idType identifier)), ["..."]))
                                <$> listToMaybe definition
                            )
                            (plain (ppr typ))
                            [(plain (ppr local), plain (ppr (idType local))) | local <- locals]
                let found' = concat outcome
                    -- With model-search=rerank, the model orders the fits of the search,
                    -- those that use every part first.
                    fits = case scorer of
                        Just score
                            | rerank ->
                                let byScore = sortOn (Down . programScore (score argumentNames) . fitProgram)
                                 in byScore (filter (not . comesLast) found') <> byScore (filter comesLast found')
                        _ -> found'
                    -- 'rankedFits' asks a question for two fits or more that use every part.
                    asks pool = length (take pool (filter (not . comesLast) fits)) >= 2
                (ordered, asked) <- case ranking of
                    Just ranking' -> liftIO $ do
                        model <- rankingModel ranking'
                        (\(order, _) -> (order, asks (rankingPool ranking'))) <$> rankedFits model ranking' state (plain . shown) fits
                    Nothing -> pure (fits, False)
                pure ([RawHoleFit (shown fit) | fit <- take (optionFits options') ordered], asked)
  where
    -- With a fit model, mode (b) checks the programs in the order of the model's score.
    withScorer argumentNames = case scorer of
        Just score | not rerank -> options'{optionMode = States (Enumerated HostOrder), optionScore = Just (score argumentNames)}
        _ -> options'
    -- With a ranking, the model orders more fits than the plugin shows.
    wanted =
        maybe (optionFits options') (max (optionFits options') . rankingPool) ranking
            `max` (if rerank && isJust scorer then 50 else 0)
    search options candidates dropped result = do
        kept <- newTcRef []
        let accept fit
                | dropped (fitProgram fit) = pure True
                | otherwise = do
                    updTcRef kept (fit :)
                    fits <- readTcRef kept
                    pure (length (filter (not . comesLast) fits) < wanted)
        _ <- streamFits options hole candidates result accept
        fits <- reverse <$> readTcRef kept
        pure (filter (not . comesLast) fits <> filter comesLast fits)
    -- As in Hectare's library, @($)@ and @id@ only appear as arguments; so
    -- does @($!)@, which applies a function as @($)@ does.
    heads name = getOccString name `notElem` ["$", "$!", "id"] || nameModule_maybe name /= Just gHC_INTERNAL_BASE

-- | The score of a program: the sum of the scores of its tokens, each given its parent's token and its position.
programScore :: (Maybe (Text, Int) -> Int -> (Text, Int) -> Double) -> Program -> Double
programScore score = go Nothing 0
  where
    go parent position program =
        let (name, arguments) = spine program
            token = (name, length arguments)
         in score parent position token + sum [go (Just token) index argument | (index, argument) <- zip [0 ..] arguments]
    spine (Var name) = (name, [])
    spine (App function argument) = let (name, arguments) = spine function in (name, arguments <> [argument])

{- | The identifier of a candidate, with its name and type, as
'GHC.Tc.Errors.Hole.tcFilterHoleFits' looks it up: a data constructor has
its wrapper and its type with unrestricted arrows. 'Nothing' for a type
constructor, a class, a pattern synonym, and the identifiers of
"GHC.Internal.Err" and "Unsafe.Coerce", which GHC drops too.
-}
lookupCandidate :: HoleFitCandidate -> TcM (Maybe (Name, Id, Type))
lookupCandidate candidate = case candidate of
    IdHFCand identifier -> pure (trivial (idName identifier, identifier, idType identifier))
    GreHFCand element -> byName (greName element)
    NameHFCand name -> byName name
  where
    byName name = do
        (thing, _) <- tryTc (tcLookup name)
        pure $ case thing of
            Just ATcId{tct_id = identifier} -> trivial (name, identifier, idType identifier)
            Just (AGlobal (AnId identifier)) -> trivial (name, identifier, idType identifier)
            Just (AGlobal (AConLike (RealDataCon constructor))) ->
                trivial (name, dataConWrapId constructor, dataConNonlinearType constructor)
            _ -> Nothing
    trivial found@(name, _, _)
        | nameModule_maybe name `elem` [Just gHC_INTERNAL_ERR, Just gHC_INTERNAL_UNSAFE_COERCE] = Nothing
        | otherwise = Just found

{- | The names of the definitions of the module that GHC gives as locals in
the scope of a hole: the definitions that hold the hole, and the definitions
with a type signature that GHC checks after the hole.
-}
moduleLocals :: [HoleFitCandidate] -> [GlobalRdrElt] -> Set.Set String
moduleLocals scope elements =
    Set.intersection
        (Set.fromList [getOccString identifier | IdHFCand identifier <- scope])
        (Set.fromList [getOccString (greName element) | element <- elements, gre_lcl element])

{- | The names of the binders that hold a hole, from GHC's binder stack. The
stack also has the definitions with a type signature that GHC checks after
the hole, as top-level binders; they do not hold the hole, so they are not
in the result.
-}
binderNames :: CtLoc -> Set.Set String
binderNames location = Set.fromList (concatMap name (ctl_bndrs (ctLocEnv location)))
  where
    name binder = case binder of
        TcIdBndr identifier flag | not (isTopLevel flag) -> [getOccString identifier]
        TcIdBndr_ExpType name' _ flag | not (isTopLevel flag) -> [getOccString name']
        _ -> []

-- | The candidates without a second candidate of the same name.
withoutRepeats :: [HoleFitCandidate] -> [HoleFitCandidate]
withoutRepeats = go emptyNameSet
  where
    go _ [] = []
    go seen (candidate : rest)
        | getName candidate `elemNameSet` seen = go seen rest
        | otherwise = candidate : go (extendNameSet seen (getName candidate)) rest

{- | A text for each candidate that no other candidate has: the name (an
operator in parentheses, as in 'hectareAvoid'), and a number after it for a
second candidate of the same name.
-}
uniqueNames :: [(Name, Type)] -> [(Text, (Name, Type))]
uniqueNames = go Map.empty
  where
    go _ [] = []
    go seen ((name, typ) : rest) =
        let base = Text.pack (if isSymOcc (getOccName name) then "(" <> getOccString name <> ")" else getOccString name)
            count = Map.findWithDefault (0 :: Int) base seen
            text' = if count == 0 then base else base <> "'" <> Text.pack (show count)
         in (text', (name, typ)) : go (Map.insert base (count + 1) seen) rest

{- | Whether GHC finds a program itself: one identifier applied to the
arguments in order, or the only argument, which is @id@.
-}
foundByGhc :: [Text] -> Program -> Bool
foundByGhc arguments program = case spine program [] of
    (Var name, []) | [name] == arguments -> True
    (Var _, applied) -> applied == map Var arguments
    _ -> False
  where
    spine (App function argument) rest = spine function (argument : rest)
    spine other rest = (other, rest)

{- | A program as an expression: each candidate's name in prefix form, as
GHC qualifies it, and the arguments as a lambda, eta reduced ('etaReduced').
-}
render :: Map.Map Text SDoc -> [Text] -> Program -> SDoc
render names arguments program
    | null arguments' = expression False program'
    | otherwise = hcat [char '\\', hsep (map (text . Text.unpack) arguments')] <+> text "->" <+> expression False program'
  where
    (arguments', program') = etaReduced arguments program
    expression nested term = case term of
        Var name -> Map.findWithDefault (text (Text.unpack name)) name names
        App function argument -> (if nested then parens else id) (expression False function <+> expression True argument)

{- | A lambda without the last arguments that its body applies last and
does not use elsewhere: @\\x1 x2 -> f x1 a x2@ is @\\x1 -> f x1 a@, and
@\\x1 -> h b x1@ is @h b@.
-}
etaReduced :: [Text] -> Program -> ([Text], Program)
etaReduced arguments program = case (reverse arguments, program) of
    (lastArgument : earlier, App function (Var name))
        | name == lastArgument && not (uses lastArgument function) -> etaReduced (reverse earlier) function
    _ -> (arguments, program)
  where
    uses name term = case term of
        Var name' -> name == name'
        App function argument -> uses name function || uses name argument

{- | Run an action, and give 'Nothing' when it throws an exception that is
not asynchronous, so that a failed search leaves GHC's fits as they are.
-}
attempt :: TcM a -> TcM (Maybe a)
attempt action = do
    environment <- getEnv
    result <- liftIO (try (runIOEnv environment action))
    case result of
        Right value -> pure (Just value)
        Left exception -> case fromException exception of
            Just asynchronous -> liftIO (throwIO (asynchronous :: SomeAsyncException))
            Nothing -> pure Nothing
