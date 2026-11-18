import Lean
import MicroCFTA.SourceCurrentNativeNoMuInventory

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if info.isTheorem &&
        ((privateToUserName name).toString.startsWith "MicroCFTA.SourceCurrentNativeNoMuInventory." ||
          name.toString.startsWith "_private.MicroCFTA.SourceCurrentNativeNoMuInventory.") then
      logInfo m!"NO_MU_INVENTORY_THEOREM {name}"
      count := count + 1
  logInfo m!"NO_MU_INVENTORY_THEOREM_COUNT {count}"
