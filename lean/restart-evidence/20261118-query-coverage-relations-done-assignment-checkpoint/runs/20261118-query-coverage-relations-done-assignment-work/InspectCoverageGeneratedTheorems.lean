import Lean
import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (privateToUserName name).toString.startsWith "MicroCFTA.SourcePruningEnumerationSharedEagerReservation.ActualFull" && info.isTheorem then
      logInfo m!"GENERATED_COVERAGE_THEOREM {name}"
      count := count + 1
  logInfo m!"GENERATED_COVERAGE_THEOREM_COUNT {count}"
