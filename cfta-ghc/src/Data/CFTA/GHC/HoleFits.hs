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
query. The plugin drops the fits that GHC finds itself (one identifier
applied to the arguments in order), and the fits that call a definition
that holds the hole, because such a fit can loop. Hectare's rule
'hectareAvoid' applies: a list function is not applied to @[]@. A fit with
the normal form of an earlier fit is skipped ('optionNormalForms'), and a fit
that ignores part of itself or drops an argument ('comesLast') comes after
the others.

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
> -fplugin-opt=Data.CFTA.GHC.HoleFits:rank-model=NAME the model on the server
> -fplugin-opt=Data.CFTA.GHC.HoleFits:rank-keep-alive=0   how long the server keeps the model loaded

With @rank@, a decision model orders the plugin's fits
("Data.CFTA.GHC.Rank"). It needs a running Ollama
(@http://localhost:11434@) with a model that has the capability
"decision": by default the model of 'Decision.Ollama.defaultOllama'
(Nimble v3, an external model under its own license), or another with
@rank-model@. The plugin searches for @rank-pool@ fits that use every part,
the model orders them in one question, and the plugin shows the best @fits@.
The options @rank-pool@, @rank-model@, and @rank-keep-alive@ also turn the
ranking on. By default the server loads the model for each ranked hole
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

import Control.Exception (SomeAsyncException, fromException, throwIO, try)
import Control.Monad (filterM, foldM, void)
import Control.Monad.IO.Class (liftIO)
import Data.List (sortBy)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Read (readMaybe)

import Data.CFTA.GHC.Fits
import Data.CFTA.GHC.Rank (Ranking (..), defaultRanking, holeState, rankedFits)
import Data.CFTA.Gen.Synthesis (Program (..))
import Decision.Ollama (Ollama (..), ollama, unload)
import GHC.Builtin.Names (gHC_INTERNAL_BASE, gHC_INTERNAL_ERR, gHC_INTERNAL_UNSAFE_COERCE)
import GHC.Builtin.Types (consDataCon, nilDataCon, tupleDataCon)
import GHC.Core.ConLike (ConLike (RealDataCon))
import GHC.Core.DataCon (dataConName, dataConNonlinearType, dataConWrapId)
import GHC.Core.Multiplicity (scaledMult, scaledThing)
import GHC.Core.TyCo.FVs (tyCoVarsOfTypesList)
import GHC.Core.Type (Type, isManyTy)
import GHC.Data.IOEnv (getEnv, runIOEnv)
import GHC.Driver.DynFlags (
    DynFlags (maxValidHoleFits),
    GeneralFlag (Opt_IgnoreInterfacePragmas),
    HasDynFlags (getDynFlags),
    gopt_unset,
 )
import GHC.Driver.Env (HscEnv, hscUpdateFlags)
import GHC.Driver.Plugins (CommandLineOption, Plugin (..), defaultPlugin, purePlugin)
import GHC.Driver.Ppr (showSDoc)
import GHC.Tc.Errors.Hole.FitTypes (HoleFit (RawHoleFit), HoleFitCandidate (..))
import GHC.Tc.Errors.Hole.Plugin (HoleFitPlugin (..), HoleFitPluginR (..))
import GHC.Tc.Types.BasicTypes (TcTyThing (AGlobal, ATcId, tct_id))
import GHC.Tc.Types.Constraint (Hole (..))
import GHC.Tc.Utils.Env (tcLookup)
import GHC.Tc.Utils.Monad (
    TcM,
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
import GHC.Types.Basic (Boxity (Boxed))
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
    }

{- | The options of the plugin, from its @-fplugin-opt@ arguments
(@NAME=VALUE@, or @NAME@ for a switch). Without them: fits of up to four
leaves, five fits, one second for each hole, Hectare's curried types, and no
ranking.
-}
readOptions :: [CommandLineOption] -> Either String PluginOptions
readOptions =
    foldM
        set
        ( PluginOptions
            defaultOptions{optionMaximumSize = 4, optionFits = 5, optionSeconds = Just 1, optionAvoid = hectareAvoid}
            Nothing
        )
  where
    set options argument = case break (== '=') argument of
        ("size", '=' : value) -> (\size -> search options (\o -> o{optionMaximumSize = size})) <$> number value
        ("fits", '=' : value) -> (\fits -> search options (\o -> o{optionFits = fits})) <$> number value
        ("seconds", '=' : value) -> (\seconds -> search options (\o -> o{optionSeconds = Just seconds})) <$> number value
        ("programs", '=' : value) -> (\programs -> search options (\o -> o{optionMaximumPrograms = Just programs})) <$> number value
        ("first-order", "") -> Right (search options (\o -> o{optionCurried = False}))
        ("only-defaulted", "") -> Right (search options (\o -> o{optionCurried = True, optionOnlyDefaulted = True}))
        ("type-domains", "") -> Right (search options (\o -> o{optionCurried = True, optionTypeDomains = True}))
        ("normal-forms", '=' : "on") -> Right (search options (\o -> o{optionNormalForms = True}))
        ("normal-forms", '=' : "off") -> Right (search options (\o -> o{optionNormalForms = False}))
        ("rank", "") -> Right (rank options id)
        ("rank-pool", '=' : value) -> (\pool -> rank options (\r -> r{rankingPool = pool})) <$> number value
        ("rank-model", '=' : value) -> Right (rank options (server (\o -> o{ollamaModel = Text.pack value})))
        ("rank-keep-alive", '=' : value) -> Right (rank options (server (\o -> o{ollamaKeepAlive = Text.pack value})))
        _ ->
            Left
                ( "unknown option "
                    <> argument
                    <> "; the options are size, fits, seconds, programs, first-order, only-defaulted, type-domains, normal-forms, rank, rank-pool, rank-model, and rank-keep-alive"
                )
      where
        search current change = current{pluginSearch = change (pluginSearch current)}
        rank current change = current{pluginRanking = Just (change (fromMaybe defaultRanking (pluginRanking current)))}
        server change ranking = ranking{rankingServer = change (rankingServer ranking)}
        number :: (Read a) => String -> Either String a
        number value = maybe (Left ("not a number in " <> argument)) Right (readMaybe value)

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
        { hfPluginInit = newTcRef (Nothing, False)
        , hfPluginRun = \reference ->
            HoleFitPlugin
                { candPlugin = \_ scope -> scope <$ updTcRef reference (\(_, ranked') -> (Just scope, ranked'))
                , fitPlugin = \hole fits -> do
                    (open, ranked') <- readTcRef reference
                    writeTcRef reference (Nothing, ranked')
                    case open of
                        Just scope -> do
                            (ours, asked) <- fitsFor options hole scope
                            updTcRef reference (\(open', _) -> (open', ranked' || asked))
                            -- The limit without the plugin: see 'raiseLimit'.
                            limit <- maxValidHoleFits <$> getDynFlags
                            let kept = maybe (length fits) (\raised -> max 0 (raised - optionFits (pluginSearch options))) limit
                            pure (take kept fits <> ours <> drop kept fits)
                        Nothing -> pure fits
                }
        , hfPluginStop = \reference -> do
            (_, ranked') <- readTcRef reference
            case pluginRanking options of
                Just ranking
                    | ranked' && ollamaKeepAlive (rankingServer ranking) /= "0" ->
                        liftIO (void (unload (rankingServer ranking)))
                _ -> pure ()
        }

{- | The plugin's fits for a hole, best first: none when the hole has no
type, when its type has a @forall@ or a class context at the top, when a
multiplicity is not @Many@, or when the search fails. The flag says whether
a model was asked.
-}
fitsFor :: PluginOptions -> TypedHole -> [HoleFitCandidate] -> TcM ([HoleFit], Bool)
fitsFor (PluginOptions options ranking) hole scope = case th_hole hole of
    Nothing -> pure ([], False)
    Just Hole{hole_ty = holeType} -> do
        elements <- globalRdrEnvElts <$> getGlobalRdrEnv
        let everything = withoutRepeats (scope <> map GreHFCand elements <> map (NameHFCand . dataConName) syntax)
            syntax = [nilDataCon, consDataCon, tupleDataCon Boxed 2]
            -- The scope in an order that does not depend on uniques.
            byName (name, _, _) (name', _, _) = stableNameCmp name name'
        found <- sortBy byName . catMaybes <$> mapM lookupCandidate everything
        typ <- liftZonkM (zonkTcType holeType)
        types <- liftZonkM (zonkTcTypes [typ' | (_, _, typ') <- found])
        let (variables, context, _) = tcSplitSigmaTy typ
            (parameters, result) = tcSplitFunTys typ
            enclosing = definitionsHolding scope elements
            named = uniqueNames [(name, typ') | ((name, _, _), typ') <- zip found types, getOccString name `Set.notMember` enclosing]
            used = Set.fromList (map fst named)
            arguments =
                take
                    (length parameters)
                    [name | index <- [1 :: Int ..], let name = "x" <> Text.pack (show index), name `Set.notMember` used]
            candidates =
                [Candidate label typ' (heads name) False (Just name) | (label, (name, typ')) <- named]
                    <> [Candidate argument (scaledThing parameter) True True Nothing | (argument, parameter) <- zip arguments parameters]
            names = Map.fromList [(label, pprPrefixName name) | (label, (name, _)) <- named]
        if not (null variables && null context)
            || not (all (isManyTy . scaledMult) parameters)
            || not (all (\(_, identifier, _) -> isManyTy (idMult identifier)) found)
            then pure ([], False)
            else do
                flexible <-
                    filterM (fmap isFlexi . readMetaTyVar) (filter (\v -> isTcTyVar v && isMetaTyVar v) (tyCoVarsOfTypesList (typ : types)))
                outcome <- attempt (search candidates arguments result)
                -- As 'GHC.Tc.Errors.Hole.withoutUnification', also when the
                -- search stops part way.
                mapM_ (\variable -> writeTcRef (metaTyVarRef variable) Flexi) flexible
                flags <- getDynFlags
                let shown fit = render names arguments (fitProgram fit)
                    plain = Text.pack . showSDoc flags
                    definition = [identifier | IdHFCand identifier <- scope, getOccString identifier `Set.member` enclosing]
                    locals = [identifier | IdHFCand identifier <- scope, getOccString identifier `Set.notMember` enclosing]
                    state =
                        holeState
                            ( (\identifier -> (plain (ppr identifier), plain (ppr (idType identifier)), ["..."]))
                                <$> listToMaybe definition
                            )
                            (plain (ppr typ))
                            [(plain (ppr local), plain (ppr (idType local))) | local <- locals]
                let fits = concat outcome
                    -- 'rankedFits' asks a question for two fits or more that use every part.
                    asks pool = length (take pool (filter (not . comesLast) fits)) >= 2
                (ordered, asked) <- case ranking of
                    Just (Ranking pool server) -> liftIO $ do
                        model <- ollama server
                        (\(order, _) -> (order, asks pool)) <$> rankedFits model state pool (plain . shown) fits
                    Nothing -> pure (fits, False)
                pure ([RawHoleFit (shown fit) | fit <- take (optionFits options) ordered], asked)
  where
    -- With a ranking, the model orders more fits than the plugin shows.
    wanted = maybe (optionFits options) (max (optionFits options) . rankingPool) ranking
    search candidates arguments result = do
        kept <- newTcRef []
        let accept fit
                | foundByGhc arguments (fitProgram fit) = pure True
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

{- | The names of the definitions that hold the hole. GHC gives such a
definition as a local, with the name of a definition of the module.
-}
definitionsHolding :: [HoleFitCandidate] -> [GlobalRdrElt] -> Set.Set String
definitionsHolding scope elements =
    Set.intersection
        (Set.fromList [getOccString identifier | IdHFCand identifier <- scope])
        (Set.fromList [getOccString (greName element) | element <- elements, gre_lcl element])

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

-- | Whether GHC finds a program itself: one identifier applied to the arguments in order.
foundByGhc :: [Text] -> Program -> Bool
foundByGhc arguments program = case spine program [] of
    (Var _, applied) -> applied == map Var arguments
    _ -> False
  where
    spine (App function argument) rest = spine function (argument : rest)
    spine other rest = (other, rest)

{- | A program as an expression: each candidate's name in prefix form, as
GHC qualifies it, and the arguments as a lambda.
-}
render :: Map.Map Text SDoc -> [Text] -> Program -> SDoc
render names arguments program
    | null arguments = expression False program
    | otherwise = hcat [char '\\', hsep (map (text . Text.unpack) arguments)] <+> text "->" <+> expression False program
  where
    expression nested term = case term of
        Var name -> Map.findWithDefault (text (Text.unpack name)) name names
        App function argument -> (if nested then parens else id) (expression False function <+> expression True argument)

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
