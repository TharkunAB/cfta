import Oracle

/-!
# lean-oracle

The oracle of `cfta-lean`: it imports the modules named on the command
line (`Init` when there are none), writes `ready <milliseconds>` with the time
of the import, and serves the line protocol of `Oracle.Session` on its
standard input and output.
-/

open Lean

/-- Import the modules and serve one session. -/
def main (arguments : List String) : IO UInt32 := do
  let modules := if arguments.isEmpty then [`Init] else arguments.map String.toName
  initSearchPath (← findSysroot)
  -- The import runs the initializers of the environment extensions.
  unsafe enableInitializersExecution
  let start ← IO.monoNanosNow
  let env ← importModules (modules.toArray.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
  let stop ← IO.monoNanosNow
  Oracle.reply ["ready", toString ((stop - start) / 1000000)]
  -- The terms print as applications, as Hectare's programs do: `List.length xs`, not `xs.length`.
  let options := ({} : Options).setBool `pp.fieldNotation false
  let context : Core.Context := { fileName := "<oracle>", fileMap := default, maxHeartbeats := 0, options }
  let state : Core.State := { env }
  match ← (Oracle.session.run' {} {} |>.run' context state).toBaseIO with
  | .ok () => return 0
  | .error e =>
    IO.eprintln s!"oracle: {← e.toMessageData.toString}"
    return 1
