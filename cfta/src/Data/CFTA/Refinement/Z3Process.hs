{-# LANGUAGE OverloadedStrings #-}

{- | An 'Entailment' that decides the queries of a theory with a Z3 process.

'withZ3Theory' starts one @z3@ process from @PATH@ and sends it the
commands of the theory once ("Data.CFTA.Refinement.SmtLib"). Each query
then runs between @push@ and @pop@: the constants and assertions of the
query ('entailmentCommands'), and @check-sat@. @unsat@ gives 'Yes', @sat@
gives 'No', and @unknown@ gives 'Unknown'. The definitions of a theory
terminate, so a model of the commands satisfies them, and @sat@ is a
countermodel.

The time limit follows 'Data.CFTA.Refinement.LiquidFixpoint.withZ3Timeout':
Z3 stops a query at the limit and answers @unknown@. When the check took
the whole limit, the query raises 'TimeLimitReached' instead of giving
'Unknown'. The process stays usable for the next query.

A query that the SMT-LIB text rejects, for example one that fails the sort
check, gives 'Unknown' and does not reach the process. A theory with a
datatype without values has no SMT-LIB text, so each query gives 'Unknown'
and no process starts. An error from Z3 raises an exception, and a new
process replaces the old one, as does any other exception during a query.
Without @z3@ on @PATH@, 'withZ3Theory' raises the exception of
"System.Process" when it starts the process.
-}
module Data.CFTA.Refinement.Z3Process (
    withZ3Theory,
    withZ3TheoryTimeout,
) where

import Control.Concurrent.MVar (modifyMVar, newMVar, withMVar)
import Control.Exception (SomeException, bracket, onException, throwIO, try, uninterruptibleMask_)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import GHC.Clock (getMonotonicTime)
import System.IO (Handle, hFlush)
import System.Process (CreateProcess (..), ProcessHandle, StdStream (..), cleanupProcess, createProcess, proc)

import Data.CFTA.Formula (Formula, Name, Sort)
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..), defaultTimeLimit)
import Data.CFTA.Refinement.SmtLib (entailmentCommands, theoryCommands)
import Data.CFTA.Refinement.Theory (Theory)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..), entailmentWithBindings)

-- | A running @z3@ process: its input, its output, and its handle.
data Solver = Solver !Handle !Handle !ProcessHandle

{- | Decide the entailments of a theory under fixed declarations and ambient
assumptions, with one Z3 process. Each query has the time limit
'defaultTimeLimit'. The arguments are those of
'Data.CFTA.Refinement.Ground.groundEntailment', without the predicate
definitions.
-}
withZ3Theory :: Theory -> [(Name, Sort)] -> [Formula] -> (Entailment -> IO a) -> IO a
withZ3Theory = withZ3TheoryTimeout defaultTimeLimit

-- | 'withZ3Theory' with a time limit for each query, in milliseconds.
withZ3TheoryTimeout :: Int -> Theory -> [(Name, Sort)] -> [Formula] -> (Entailment -> IO a) -> IO a
withZ3TheoryTimeout milliseconds current declarations assumptions action =
    case theoryCommands current of
        Left _ -> action (entailmentWithBindings (\_ _ _ -> pure Unknown))
        Right commands -> bracket (newMVar =<< start commands) stop $ \solverVar ->
            action (entailmentWithBindings (query commands solverVar))
  where
    query commands solverVar bindings antecedent consequent =
        case entailmentCommands current Map.empty declarations assumptions bindings antecedent consequent of
            Left _ -> pure Unknown
            Right queryCommands -> do
                outcome <- modifyMVar solverVar $ \solver -> do
                    attempt <- try (check solver queryCommands)
                    case attempt of
                        -- The process can hold an unread answer, so a new one replaces it.
                        Left failure -> do
                            fresh <- uninterruptibleMask_ (stopSolver solver >> start commands)
                            pure (fresh, Left (failure :: SomeException))
                        Right reply -> pure (solver, Right reply)
                either throwIO verdict outcome

    -- Start a process, set the time limit, and send the theory. An echo marks the end of the answers.
    start commands = do
        (input, output, process) <- open
        let solver = Solver input output process
        flip onException (stopSolver solver) $ do
            Text.hPutStr input $
                "(set-option :timeout " <> Text.pack (show milliseconds) <> ")\n" <> commands <> "(echo \"cfta-ready\")\n"
            hFlush input
            _ <- answer output ["cfta-ready"]
            pure solver

    check (Solver input output _) queryCommands = do
        Text.hPutStr input (Text.unlines (["(push 1)"] <> queryCommands <> ["(check-sat)", "(pop 1)"]))
        hFlush input
        begin <- getMonotonicTime
        reply <- answer output ["sat", "unsat", "unknown"]
        end <- getMonotonicTime
        pure (reply, end - begin)

    verdict (reply, seconds) = case reply of
        "unsat" -> pure Yes
        "sat" -> pure No
        _
            | seconds * 1000 >= fromIntegral milliseconds -> throwIO (TimeLimitReached milliseconds)
            | otherwise -> pure Unknown

    stop solverVar = withMVar solverVar stopSolver

-- | Start @z3@ with pipes for its input and output.
open :: IO (Handle, Handle, ProcessHandle)
open = do
    created <- createProcess (proc "z3" ["-in"]){std_in = CreatePipe, std_out = CreatePipe, std_err = NoStream}
    case created of
        (Just input, Just output, _, process) -> pure (input, output, process)
        (_, _, _, process) -> do
            cleanupProcess (Nothing, Nothing, Nothing, process)
            ioError (userError "z3 started without pipes")

{- | Read lines until one of the expected answers. An error line of Z3
raises an exception.
-}
answer :: Handle -> [Text.Text] -> IO Text.Text
answer output expected = do
    line <- Text.strip <$> Text.hGetLine output
    if
        | line `elem` expected -> pure line
        | "(error" `Text.isPrefixOf` line -> ioError (userError ("Z3 rejected a cfta command: " <> Text.unpack line))
        | otherwise -> answer output expected

-- | End a process. A failure to end it does not hide the reason for the stop.
stopSolver :: Solver -> IO ()
stopSolver (Solver input output process) = do
    _ <- try (cleanupProcess (Just input, Just output, Nothing, process)) :: IO (Either SomeException ())
    pure ()
