import Lean.Elab.Command
import MicroCFTA.SourcePruningEnumerationIsolatedPending
open Lean Elab Command
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "IsolatedPending" then
      logInfo m!"{name}"
