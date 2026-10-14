{- | A Z3-backed 'Entailment' implemented with Liquid Fixpoint's SMT API.

The entailment translates each 'Formula' to a Liquid Fixpoint expression. A
name is an integer unless a declaration gives it another 'Sort'.
-}
module Data.CFTA.Refinement.LiquidFixpoint (
    withZ3,
    withZ3Assuming,
    withZ3Timeout,
    defaultTimeLimit,
    TimeLimitReached (..),
) where

import Control.Concurrent.MVar (modifyMVar, newMVar, withMVar)
import Control.Exception (Exception (..), SomeException, bracket, throwIO, try, uninterruptibleMask_)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Lazy (runStateT)
import Data.Char (isAlphaNum, isAscii, ord)
import qualified Data.HashSet as HashSet
import Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime)

import Data.CFTA.Formula (Formula (..), Name (..), Relation (..), Sort (..), Term (..))
import Data.CFTA.Refinement (Entailment, Verdict (..), entailmentWithBindings)
import Data.CFTA.Symbol (valueName)
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Smt.Types as SMTTypes
import qualified Language.Fixpoint.Types as Fixpoint
import Language.Fixpoint.Types.Config (SMTSolver (Z3), defConfig, smtTimeout, solver)

{- | Run actions using one reusable Z3 process and a fixed declaration set.
Each query has the time limit 'defaultTimeLimit', as in 'withZ3Assuming'.
-}
withZ3 :: [(Name, Sort)] -> (Entailment -> IO a) -> IO a
withZ3 declarations = withZ3Assuming declarations []

{- | Run entailment queries under a fixed collection of ambient assumptions.

This models the surrounding Liquid typing environment. For example, an input
named @bufferLength@ may be declared as an integer and assumed equal to three;
position substitution can then prove that an index lies below that particular
buffer length. Each query declares as an integer every free name that the
declarations do not give a sort, including 'valueName' and term symbols that
become actual values in a position substitution. Declare a name to give it
another sort, such as a 'FunctionSort' for an uninterpreted function. A fresh
value name of a binding gets the sort of the name that it stands for. It must
not be a declared name or a free name in an ambient assumption; otherwise
the query gives 'Unknown'.

Each query has the time limit 'defaultTimeLimit'. A query that reaches the
limit raises 'TimeLimitReached'. 'withZ3Timeout' sets another limit.
-}
withZ3Assuming ::
    [(Name, Sort)] ->
    [Formula] ->
    (Entailment -> IO a) ->
    IO a
withZ3Assuming = withZ3Timeout defaultTimeLimit

-- | The time limit of each query of 'withZ3' and 'withZ3Assuming': ten seconds.
defaultTimeLimit :: Int
defaultTimeLimit = 10000

{- | 'withZ3Assuming' with a time limit for each query, in milliseconds.

Z3 has no time limit of its own, so a query that it cannot decide, for
example about non-linear integer arithmetic, can run without end. At the
limit, Z3 stops the query and answers @unknown@, as it does when it gives up
before the limit. The entailment measures the time of the check. When the
answer is @unknown@ and the check took the whole limit, it raises
'TimeLimitReached' instead of giving 'Unknown'. The next query runs normally.
-}
withZ3Timeout ::
    Int ->
    [(Name, Sort)] ->
    [Formula] ->
    (Entailment -> IO a) ->
    IO a
withZ3Timeout milliseconds sorted assumptions action =
    bracket acquire release $ \contextVar ->
        action (entailmentWithBindings $ query contextVar)
  where
    valueSymbol = nameSymbol (Name $ Text.pack valueName)
    given = [(nameSymbol name, sortToFixpoint sort) | (name, sort) <- sorted]
    declarations
        | valueSymbol `elem` map fst given = given
        | otherwise = (valueSymbol, Fixpoint.FInt) : given
    known = HashSet.fromList $ map fst declarations
    solverAssumptions = map toFixpoint assumptions
    reserved = HashSet.union known $ foldMap Fixpoint.exprSymbolsSet solverAssumptions

    config = defConfig{solver = Z3, smtTimeout = Just milliseconds}

    acquire = newMVar =<< SMT.makeContextNoLog config
    release contextVar = withMVar contextVar SMT.cleanupContext

    query contextVar bindings antecedentFormula consequentFormula =
        case traverse freshDeclaration bindings of
            Nothing -> pure Unknown
            Just freshDeclarations -> do
                outcome <- modifyMVar contextVar $ \context -> do
                    let mentioned = foldMap Fixpoint.exprSymbolsSet (antecedent : consequent : solverAssumptions)
                        declared = HashSet.union known $ HashSet.fromList $ map fst freshDeclarations
                        undeclared =
                            [(name, Fixpoint.FInt) | name <- HashSet.toList $ HashSet.difference mentioned declared]
                    attempt <- try $ runStateT (check (freshDeclarations <> undeclared)) context
                    case attempt of
                        -- An exception during the query, such as a time limit
                        -- of the caller, can leave an open scope and an unread
                        -- answer in the process. The next query would read that
                        -- answer, so a new process replaces the old one.
                        Left err -> do
                            fresh <- replaceContext context
                            pure (fresh, Left (err :: SomeException))
                        Right (answer@(response, _), nextContext) -> case response of
                            -- Z3 answers the rejected command and then the check-sat.
                            -- Liquid Fixpoint reads only the first answer, so the next
                            -- query would read the second. A new process replaces the
                            -- old one. Each query sends its own declarations. The test
                            -- "answers correctly after the solver rejects a query"
                            -- gets shifted answers without the new process (checked
                            -- with Z3 4.15.3 and Liquid Fixpoint 0.9.6.3.7).
                            SMTTypes.Error _ -> do
                                fresh <- replaceContext nextContext
                                pure (fresh, Right answer)
                            _ -> pure (nextContext, Right answer)
                either throwIO responseVerdict outcome
      where
        antecedent = toFixpoint antecedentFormula
        consequent = toFixpoint consequentFormula

        check freshDeclarations = SMT.smtBracket "cfta entailment" $ do
            SMT.smtDecls $ declarations <> freshDeclarations
            SMT.smtAssertDecl $
                Fixpoint.pAnd (solverAssumptions <> [antecedent, Fixpoint.PNot consequent])
            start <- liftIO getMonotonicTime
            response <- SMT.command SMTTypes.CheckSat
            end <- liftIO getMonotonicTime
            pure (response, end - start)

        -- Another interruption must not leave the old process in the variable.
        replaceContext context = uninterruptibleMask_ $ do
            _ <- try (SMT.cleanupContext context) :: IO (Either SomeException ())
            SMT.makeContextNoLog config

        freshDeclaration (fresh, original)
            | HashSet.member (nameSymbol fresh) reserved = Nothing
            | otherwise = Just (nameSymbol fresh, fromMaybe Fixpoint.FInt $ lookup (nameSymbol original) declarations)

        responseVerdict (SMTTypes.Unsat, _) = pure Yes
        responseVerdict (SMTTypes.Sat, _) = pure No
        responseVerdict (SMTTypes.Unknown, seconds)
            | seconds * 1000 >= fromIntegral milliseconds = throwIO $ TimeLimitReached milliseconds
            | otherwise = pure Unknown
        responseVerdict (SMTTypes.Error message, _) =
            ioError . userError $ "Z3 rejected a cfta query: " <> Text.unpack message
        responseVerdict (response, _) =
            ioError . userError $ "Unexpected Z3 response: " <> show response

-- | The Liquid Fixpoint expression of a formula.
toFixpoint :: Formula -> Fixpoint.Expr
toFixpoint formula = case formula of
    Top -> Fixpoint.PTrue
    And parts -> Fixpoint.PAnd $ map toFixpoint parts
    Bottom -> Fixpoint.PFalse
    Or parts -> Fixpoint.POr $ map toFixpoint parts
    Not inner -> Fixpoint.PNot $ toFixpoint inner
    Atom relation left right -> Fixpoint.PAtom (brel relation) (termToFixpoint left) (termToFixpoint right)
    Forall bound inner -> Fixpoint.PAll (map binder bound) (toFixpoint inner)
    Exists bound inner -> Fixpoint.PExist (map binder bound) (toFixpoint inner)
  where
    binder (name, sort) = (nameSymbol name, sortToFixpoint sort)
    brel relation = case relation of
        Eq -> Fixpoint.Eq
        Ne -> Fixpoint.Ne
        Gt -> Fixpoint.Gt
        Ge -> Fixpoint.Ge
        Lt -> Fixpoint.Lt
        Le -> Fixpoint.Le

-- | The Liquid Fixpoint expression of a term.
termToFixpoint :: Term -> Fixpoint.Expr
termToFixpoint term = case term of
    Lit value -> Fixpoint.ECon $ Fixpoint.I value
    Var name -> Fixpoint.EVar $ nameSymbol name
    Neg inner -> Fixpoint.ENeg $ termToFixpoint inner
    Add left right -> Fixpoint.EBin Fixpoint.Plus (termToFixpoint left) (termToFixpoint right)
    Sub left right -> Fixpoint.EBin Fixpoint.Minus (termToFixpoint left) (termToFixpoint right)
    Mul left right -> Fixpoint.EBin Fixpoint.Times (termToFixpoint left) (termToFixpoint right)
    Div left right -> Fixpoint.EBin Fixpoint.Div (termToFixpoint left) (termToFixpoint right)
    Mod left right -> Fixpoint.EBin Fixpoint.Mod (termToFixpoint left) (termToFixpoint right)
    App function arguments -> Fixpoint.eApps (Fixpoint.EVar $ nameSymbol function) (map termToFixpoint arguments)
    Ite condition yes no -> Fixpoint.EIte (toFixpoint condition) (termToFixpoint yes) (termToFixpoint no)
    Cast inner sort -> Fixpoint.ECst (termToFixpoint inner) (sortToFixpoint sort)

-- | The Liquid Fixpoint sort of a sort.
sortToFixpoint :: Sort -> Fixpoint.Sort
sortToFixpoint sort = case sort of
    IntSort -> Fixpoint.FInt
    RealSort -> Fixpoint.FReal
    BoolSort -> Fixpoint.boolSort
    FunctionSort arguments result -> Fixpoint.mkFFunc 0 $ map sortToFixpoint arguments <> [sortToFixpoint result]

{- | The Liquid Fixpoint symbol of a name.

Liquid Fixpoint can write two distinct raw names as one SMT name, so each name
gets an injective encoding into characters that it writes unchanged. A name of
ASCII letters, digits, and underscores keeps its text behind the prefix @m_@.
Any other name becomes the decimal codes of its characters, each ended by an
underscore, behind the prefix @mx@. The second character of the two forms
differs, so no name of one form equals a name of the other.
-}
nameSymbol :: Name -> Fixpoint.Symbol
nameSymbol (Name text)
    | Text.all plain text = Fixpoint.symbol $ Text.append (Text.pack "m_") text
    | otherwise = Fixpoint.symbol $ Text.append (Text.pack "mx") $ Text.concatMap encodeChar text
  where
    plain character = isAscii character && isAlphaNum character || character == '_'
    encodeChar character = Text.pack (show $ ord character) <> Text.singleton '_'

{- | Z3 stopped a query at the time limit, in milliseconds, before it decided
the query.
-}
newtype TimeLimitReached = TimeLimitReached Int
    deriving (Eq, Show)

instance Exception TimeLimitReached where
    displayException (TimeLimitReached milliseconds) =
        "Z3 stopped a query at the time limit of "
            <> show milliseconds
            <> " milliseconds. Run it again with a higher limit through withZ3Timeout,"
            <> " or simplify the refinements, for example remove non-linear arithmetic."
