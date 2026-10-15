import Lean
import Oracle.Erase
import Oracle.Walk
import Oracle.States
import Oracle.Features
import Oracle.Suggest

/-!
# The oracle's line protocol

The oracle reads one request per line on its standard input and writes the
reply on its standard output, then flushes it. The fields of a line are
separated by tabs, because Lean names contain dots and can contain spaces.

* `ping` replies `pong`.
* `library` with items: each item is a constant, or `N.*` for every constant
  of the namespace `N` that is a definition or a constructor. The reply has a
  line `component <index> <name> <type>` for each component with a Hectare
  type, a line `skipped <name> <reason>` for each other item, and `end <n>`.
  The search over states uses every constant of the library, also the
  skipped ones that are in the environment.
* `goal` with a type in Lean syntax, as `∀ {α : Type} [BEq α] (x : α)
  (xs : List α), Bool`. The oracle elaborates it and enters its binders: a
  type binder becomes a rigid type, an instance binder a local instance, and
  an explicit binder an argument of the query. The reply has a line
  `argument <index> <name> <type>` for each argument, `goal <type>`, and
  `end`. After `goal`, these requests are valid:
  * `extend <k> <leaf>:<children>...`: keep the first `k` frames, step the
    tokens, and check the complete program. The reply is `died <n>` when the
    token at index `n` failed (the oracle then holds `n` frames), or `done 1`
    or `done 0` when every token stepped, by whether the program fits.
  * `term` replies `term <text>` with the last program that fit, as Lean
    prints it.
  * `checks <check>...` sets the optional levels of a step's cascade: `head`
    compares the heads of the two types before `isDefEq`, `synthEnd` leaves
    `synthInstance?` to the complete program, and `index` makes a new state of
    the search over states look up its leaves in a discrimination tree. The reply is `checks`
    with the levels that are on.
  * `stats` replies `stats` with `key=value` fields.
  * `search <using>`: `exact?` on the goal, with every argument required when
    `<using>` is `1`. The reply is `search <milliseconds> <found> <term>`.
  * `snapshots <n>`: `n` pairs of `saveState` and `restore`, for their cost.
    The reply is `snapshots <nanoseconds per pair>`.
  * `features <bound>`: the features of the query that predict which mode
    solves it ("Oracle.Features"). The reply is `features` with `key=value`
    fields.
  * `suggest <size> <count> <seconds> <useAll> <budget> <name>:<children>...`:
    the portfolio of `hectare?` ("Oracle.Suggest") on the goal, with its own
    leaves, until it reaches the expected tokens, the count of fits, or the
    seconds. The reply is `suggest` with `key=value` fields: the rank of the
    expected program among the fits (`0` when the portfolio did not reach
    it), the mode that found it, the fits, the outcome and time of each run,
    and the first fit.
  * `states <bound> <seconds> <name>:<children>...`: the search over states
    built from the goals ("Oracle.States"), size by size up to the bound, until
    it finds the expected tokens or the seconds pass. The reply is `states`
    with `key=value` fields.
  * `goals <bound>`: start the generic search over states (the end of
    "Oracle.States"). The reply has a line `leaf <index> <name> <required>`
    for each leaf of the protocol (the components, the arguments, which are
    required, then the other constants of the library), and `end <key>` with
    the key of the goal. With the check `index`, it builds the
    discrimination trees of the leaves for up to `bound - 1` children.
  * `transitions <milliseconds> <key> <k>...`: the refinements of the goal
    of a key for the numbers of children. The reply is `transitions` with a
    field `<leaf>:<k>:<key>,<key>...` for each leaf that fits, with the keys
    of its child goals, or `timeout` when the milliseconds pass first.
* `quit` ends the session.

A failed request replies `error <message>`.
-/

namespace Oracle

open Lean Meta Elab

/-- Write a reply line and flush it. -/
def reply (fields : List String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn ("\t".intercalate fields)
  out.flush

/-- Read a request line as its fields; `none` at the end of the input. -/
def request : IO (Option (List String)) := do
  let line ← (← IO.getStdin).getLine
  if line.isEmpty then return none
  return some ((line.replace "\n" "").splitOn "\t")

/-- The constants of a library item: a constant, or the sweep of a namespace. -/
def itemConstants (item : String) : MetaM (Array Name) := do
  let env ← getEnv
  if item.endsWith ".*" then
    let space := ((item.splitOn ".*").headD "").toName
    let mut found := #[]
    for (name, info) in env.constants.toList do
      if name.getPrefix == space && (← sweepCandidate name info) then
        found := found.push name
    return found.qsort Name.lt
  else
    return #[item.toName]

/-- Erase the constants of a library, write the reply, and give the
components and every constant of the library. -/
def library (items : List String) : MetaM (Array Name × Array Name) := do
  let mut components := #[]
  let mut everything := #[]
  let mut seen : NameSet := {}
  for item in items do
    for name in ← itemConstants item do
      if seen.contains name then continue
      seen := seen.insert name
      match (← getEnv).find? name with
      | none => reply ["skipped", name.toString, "not in the environment"]
      | some info =>
        everything := everything.push name
        match ← eraseConstantType info.type with
        | .error reason => reply ["skipped", name.toString, reason]
        | .ok erased =>
          if erased.anyResult then
            reply ["skipped", name.toString, "a result of any type"]
          else
            reply ["component", toString components.size, name.toString, erased.render]
            components := components.push name
  reply ["end", toString components.size]
  return (components, everything)

/-- Elaborate a type in Lean syntax. -/
def elaborateType (text : String) : MetaM Expr := do
  let syntaxTree ← match Parser.runParserCategory (← getEnv) `term text with
    | .ok tree => pure tree
    | .error message => throwError message
  Term.TermElabM.run' do
    let type ← Term.elabType syntaxTree
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars type

/-- Parse a token `<name>:<children>` with the index of the named leaf. -/
def parseNamedToken (leaves : Array Leaf) (text : String) : Option (Nat × Nat) :=
  match text.splitOn ":" with
  | [name, children] => do
    let index ← leaves.findIdx? (·.name.toString == name)
    return (index, ← children.toNat?)
  | _ => none

/-- `exact?` on a fresh goal of the walk's type, as the tactic does: the
library search with `solveByElim` for the side goals, and with the required
locals. The reply has the time in milliseconds, whether a term was found, and
the term. No assignment stays. -/
def search (required : List Expr) : WalkM Unit := do
  let saved ← Meta.saveState
  let goal ← mkFreshExprMVar (← get).goalType
  let tactic : List MVarId → MetaM (List MVarId) := fun goals =>
    LibrarySearch.solveByElim required (exfalso := false) goals (maxDepth := 6)
  let allowFailure : MVarId → MetaM Bool := fun g => do
    let g ← g.withContext (instantiateMVars (.mvar g))
    return required.all fun e => e.occurs g
  let start ← now
  let attempt : MetaM (Option String) := do
    let found ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 200000 * 1000 }) <|
      withCurrHeartbeats <| LibrarySearch.librarySearch goal.mvarId! tactic allowFailure
    match found with
    | none => return some (toString (← ppExpr (← instantiateMVars goal)))
    | some _ => return none
  let result ← tryCatch attempt fun e => return some s!"error: {← e.toMessageData.toString}"
  let stop ← now
  saved.restore
  let milliseconds := (stop - start) / 1000000
  match result with
  | some term => reply ["search", toString milliseconds, "1", term]
  | none => reply ["search", toString milliseconds, "0"]

/-- Serve the requests of a walk until `quit` or the end of the input. -/
partial def serveWalk (required : List Expr) : WalkM Unit := do
  let some fields ← request | return
  match fields with
  | ["quit"] => return
  | ["ping"] =>
    reply ["pong"]
    serveWalk required
  | "extend" :: kept :: tokens =>
    match kept.toNat?, tokens.mapM parseToken with
    | some k, some parsed =>
      let start ← now
      truncate k
      let outcome ← extend parsed.toArray
      let stop ← now
      count fun c => { c with extensions := c.extensions + 1, extendNanos := c.extendNanos + (stop - start) }
      match outcome with
      | .died index => reply ["died", toString index]
      | .done true => reply ["done", "1"]
      | .done false => reply ["done", "0"]
    | _, _ => reply ["error", "bad extend request"]
    serveWalk required
  | "checks" :: names =>
    let checks : Checks :=
      { head := names.contains "head", synthAtEnd := names.contains "synthEnd", index := names.contains "index" }
    modify fun w => { w with checks }
    reply ["checks", s!"head={checks.head}", s!"synthEnd={checks.synthAtEnd}", s!"index={checks.index}"]
    serveWalk required
  | ["term"] =>
    match (← get).lastFit with
    | some term => reply ["term", toString (← ppExpr term)]
    | none => reply ["term"]
    serveWalk required
  | ["stats"] =>
    reply ("stats" :: (← get).counters.fields)
    serveWalk required
  | ["search", useArguments] =>
    search (if useArguments == "1" then required else [])
    serveWalk required
  | "states" :: bound :: seconds :: tokens =>
    let leaves := (← get).stateLeaves
    match bound.toNat?, seconds.toNat?, tokens.mapM (parseNamedToken leaves) with
    | some bound, some seconds, some expected =>
      let start ← now
      let required := (List.range leaves.size).filter fun index =>
        match leaves[index]! with
        | .fvar .. => true
        | .const _ => false
      let steps := (← get).counters.steps
      let synthCalls := (← get).counters.synthCalls
      let (_, s) ← (searchSizes bound expected.toArray required).run { deadline := start + seconds * 1000000000 }
      let stop ← now
      let counters := (← get).counters
      let transitions := s.table.fold (fun total _ found => total + found.size) 0
      reply ([ "states", s!"found={s.found.getD 0}", s!"programs={s.programs}", s!"fits={s.fits}"
            , s!"relevant={s.relevant}", s!"states={s.table.size}", s!"transitions={transitions}"
            , s!"buildSteps={s.buildSteps}", s!"searchSteps={s.searchSteps}"
            , s!"steps={counters.steps - steps}", s!"synthCalls={counters.synthCalls - synthCalls}"
            , s!"milliseconds={(stop - start) / 1000000}", s!"timedOut={s.timedOut}"
            , s!"budgetPrunes={s.budgetPrunes}", s!"memoLookups={s.memoLookups}", s!"memoHits={s.memoHits}"
            , s!"memoNanos={s.memoNanos}", s!"splitPrunes={s.splitPrunes}", s!"splitPasses={s.splitPasses}"
            , s!"indexSkips={s.indexSkips}", s!"indexPasses={s.indexPasses}", s!"indexLookups={s.indexLookups}"
            , s!"indexNanos={s.indexNanos}", s!"indexEntries={s.indexEntries}", s!"indexBuildNanos={s.indexBuildNanos}" ]
            ++ counters.fields)
    | _, _, _ => reply ["error", "bad states request"]
    serveWalk required
  | ["goals", bound] =>
    match bound.toNat? with
    | some bound =>
      let root ← goalKey (← get).goalType
      let leaves ← protocolLeaves
      if (← get).checks.index then
        let (trees, _) ← buildIndex leaves bound
        modify fun w => { w with goalIndex := trees }
      for (leaf, index) in leaves.toList.zipIdx do
        let flag := match leaf with
          | .fvar .. => "1"
          | .const _ => "0"
        reply ["leaf", toString index, leaf.name.toString, flag]
      reply ["end", toString root]
    | none => reply ["error", "bad goals request"]
    serveWalk required
  | "transitions" :: milliseconds :: key :: counts =>
    match milliseconds.toNat?, key.toNat?, counts.mapM String.toNat? with
    | some milliseconds, some key, some counts =>
      match ← transitionsOf key counts ((← now) + milliseconds * 1000000) with
      | none => reply ["timeout"]
      | some found =>
        reply ("transitions" :: found.toList.map fun (leaf, children, keys) =>
          s!"{leaf}:{children}:{",".intercalate (keys.toList.map toString)}")
    | _, _, _ => reply ["error", "bad transitions request"]
    serveWalk required
  | ["features", bound] =>
    match bound.toNat? with
    | some bound =>
      let start ← now
      let f ← features bound
      let stop ← now
      reply [ "features", s!"higherKinded={f.higherKinded}", s!"classOverConstructor={f.classOverConstructor}"
            , s!"openChildren={f.openChildren}", s!"fitting={f.fitting}", s!"withoutErasure={f.withoutErasure}"
            , s!"milliseconds={(stop - start) / 1000000}" ]
    | none => reply ["error", "bad features request"]
    serveWalk required
  | "suggest" :: size :: count :: seconds :: useAll :: budget :: tokens =>
    match size.toNat?, count.toNat?, seconds.toNat?, budget.toNat? with
    | some size, some count, some seconds, some budget =>
      let expected := tokens.filterMap fun text =>
        match text.splitOn ":" with
        | [name, children] => children.toNat?.map (name, ·)
        | _ => none
      let config : HectareConfig := { size, suggestions := count, useAll := useAll == "1", seconds, budget }
      let start ← now
      let p ← hectarePortfolio (← get).root config expected.toArray
      let stop ← now
      let first ← match p.fits[0]? with
        | some term => pure ((toString (← ppExpr term)).replace "\n" " ")
        | none => pure ""
      reply [ "suggest", s!"rank={p.rank.getD 0}", s!"foundBy={p.foundBy}", s!"fits={p.fitTokens.size}"
            , s!"milliseconds={(stop - start) / 1000000}", s!"hectare={p.hectare.name}"
            , s!"hectareFits={p.hectareFits}", s!"hectareMilliseconds={p.hectareNanos / 1000000}"
            , s!"states={p.states.name}", s!"statesMilliseconds={p.statesNanos / 1000000}"
            , s!"leaves={p.leaves}", s!"first={first}" ]
    | _, _, _, _ => reply ["error", "bad suggest request"]
    serveWalk required
  | ["snapshots", n] =>
    let n := n.toNat?.getD 0
    let start ← now
    for _ in [0:n] do
      let saved ← Meta.saveState
      saved.restore
    let stop ← now
    reply ["snapshots", toString ((stop - start) / max n 1)]
    serveWalk required
  | _ =>
    reply ["error", s!"unknown request {fields}"]
    serveWalk required

/-- Enter the binders of the goal, write the reply, and serve the walk. -/
def goal (components everything : Array Name) (text : String) : MetaM Unit := do
  let type ← elaborateType text
  forallTelescope type fun binders body => do
    let mut rigid : FVarIdMap String := {}
    let mut arguments := #[]
    for binder in binders do
      let decl ← binder.fvarId!.getDecl
      if ← isUniverse decl.type then
        rigid := rigid.insert binder.fvarId! s!"@T{rigid.size}"
      else if decl.binderInfo.isExplicit then
        arguments := arguments.push (binder, decl.userName)
    for ((binder, name), index) in arguments.toList.zipIdx do
      match ← eraseType {} rigid (← inferType binder) with
      | .ok erased => reply ["argument", toString (components.size + index), name.toString, erased.render]
      | .error reason => reply ["error", s!"argument {name}: {reason}"]
    match ← eraseType {} rigid body with
    | .ok erased => reply ["goal", erased.render]
    | .error reason => reply ["error", s!"goal: {reason}"]
    reply ["end"]
    let root ← mkFreshExprMVar body
    let locals := arguments.map fun (binder, name) => Leaf.fvar binder name
    let erased : NameSet := components.foldl (·.insert ·) {}
    let walk : Walk :=
      { root := root.mvarId!, goalType := body, leaves := components.map Leaf.const ++ locals
        others := (everything.filter (!erased.contains ·)).map Leaf.const
        stateLeaves := everything.map Leaf.const ++ locals }
    discard <| (serveWalk (arguments.toList.map (·.1))).run walk

/-- Serve the requests of a session until `quit` or the end of the input. -/
partial def session (components everything : Array Name := #[]) : MetaM Unit := do
  let some fields ← request | return
  match fields with
  | ["quit"] => return
  | ["ping"] =>
    reply ["pong"]
    session components everything
  | "library" :: items =>
    let (components, everything) ← library items
    session components everything
  | ["goal", text] =>
    tryCatch (goal components everything text) fun e => do reply ["error", ← e.toMessageData.toString]
  | _ =>
    reply ["error", s!"unknown request {fields}"]
    session components everything

end Oracle
