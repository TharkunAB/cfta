import Lean
import Oracle.Erase
import Oracle.Walk
import Oracle.States

/-!
# Programs for a goal from its context

The portfolio of `hectare?` (`Oracle.Tactic`) and of the oracle's `suggest`
request: mode (a), Hectare's programs from the `hectare-propose` process
checked by the walk, then the search over states of `Oracle.States` with the
index of the leaves; both over the locals of the goal's context, the
definitions and constructors of the namespaces of the goal's types, and a few
general functions and class methods. The module also has the filter of a namespace's
constants that the oracle's library requests use.
-/

namespace Oracle

open Lean Meta

/-- The suffixes of the names of generated declarations that are never
components. -/
def generatedSuffixes : List String :=
  [ "below", "ibelow", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "noConfusionType"
  , "sizeOf_spec", "inj", "injEq", "eq_def", "brecOn", "binductionOn", "rec", "recOn", "casesOn" ]

/-- Whether a constant of a namespace sweep is a candidate component: a
definition or a constructor, not generated, not internal, not an instance, not
deprecated, and not unsafe. -/
def sweepCandidate (name : Name) (info : ConstantInfo) : MetaM Bool := do
  let env ← getEnv
  let kind := match info with
    | .defnInfo _ | .opaqueInfo _ | .ctorInfo _ => true
    | _ => false
  if !kind || info.isUnsafe || name.isInternal || isPrivateName name then return false
  if isAuxRecursor env name || isNoConfusion env name || Linter.isDeprecated env name then return false
  if let .str _ last := name then
    if generatedSuffixes.contains last then return false
  return !(← isInstance name)

/-- The options of `hectare?`. -/
structure HectareConfig where
  /-- The largest program, in leaves. -/
  size : Nat := 5
  /-- The number of programs to suggest. -/
  suggestions : Nat := 3
  /-- Whether every local of the goal's context must occur in a program. -/
  useAll : Bool := true
  /-- The seconds after which the search stops. -/
  seconds : Nat := 10
  /-- The seconds of mode (a), Hectare's programs checked by the walk, before
  the search over states; `0` for the search over states alone. -/
  budget : Nat := 2

/-- Parse a token `<leaf>:<children>`. -/
def parseToken (text : String) : Option (Nat × Nat) :=
  match text.splitOn ":" with
  | [leaf, children] => do return (← leaf.toNat?, ← children.toNat?)
  | _ => none

/-- The general functions and class methods that `hectare?` always uses. -/
def generalLeaves : List Name :=
  [ ``id, ``Function.const, ``BEq.beq, ``Add.add, ``HAdd.hAdd, ``Mul.mul, ``Max.max, ``Min.min
  , ``Ord.compare, ``Functor.map, ``Pure.pure, ``Bind.bind, ``not, ``and, ``or ]

/-- The locals of the context that can be leaves: values, not types or type
formers (as `m : Type → Type`), not proofs, and not instances. -/
def localLeaves : MetaM (Array (Expr × Name)) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if ← forallTelescopeReducing type fun _ body => isUniverse body then continue
    if ← isProp type then continue
    if (← isClass? type).isSome then continue
    found := found.push (decl.toExpr, decl.userName)
  return found

/-- The inductive types whose constants occur in the types. -/
def typeNamespaces (types : Array Expr) : MetaM NameSet := do
  let env ← getEnv
  let mut spaces : NameSet := {}
  for type in types do
    for name in (← instantiateMVars type).getUsedConstants do
      if let some (.inductInfo _) := env.find? name then
        spaces := spaces.insert name
  return spaces

/-- The inductive types whose constants occur in the result types of the
constants, after their arguments: the types that a program can reach in one
application, as `Option` from `List.lookup`. -/
def resultNamespaces (names : Array Name) : MetaM NameSet := do
  let env ← getEnv
  let mut spaces : NameSet := {}
  for name in names do
    let some info := env.find? name | continue
    let result ← forallTelescopeReducing info.type fun _ body => pure body
    for used in result.getUsedConstants do
      if let some (.inductInfo _) := env.find? used then
        spaces := spaces.insert used
  return spaces

/-- The definitions and constructors of the namespaces, in one pass over the
environment, ordered by name, and then the general leaves. -/
def namespaceConstants (spaces : NameSet) : MetaM (Array Name) := do
  let env ← getEnv
  let mut found := #[]
  for (name, info) in env.constants.toList do
    if spaces.contains name.getPrefix && (← sweepCandidate name info) then
      found := found.push name
  let general := generalLeaves.filter fun name => env.contains name && !found.contains name
  return found.qsort Name.lt ++ general.toArray

/-- The leaves of `hectare?` for a goal type in the current local context:
the constants of the namespaces of the types (and of the types that their
constants return), then the locals; with the number of the constants. -/
def searchLeaves (goalType : Expr) : MetaM (Array Leaf × Nat) := do
  let locals ← localLeaves
  let localTypes ← locals.mapM fun (fvar, _) => inferType fvar
  -- The namespaces of the goal's types, and of the types that their
  -- constants give.
  let spaces ← typeNamespaces (localTypes.push goalType)
  let mut all := spaces
  for space in ← resultNamespaces (← namespaceConstants spaces) do
    all := all.insert space
  let constants ← namespaceConstants all
  return (constants.map Leaf.const ++ locals.map fun (fvar, name) => Leaf.fvar fvar name, constants.size)

/-- How a run of the portfolio ended. -/
inductive RunOutcome where
  /-- The run found the fits that the search wants. -/
  | solved
  /-- The run looked at every program up to the size. -/
  | exhausted
  /-- The run stopped at its time. -/
  | outOfTime
  /-- The run did not take place. -/
  | skipped
  deriving BEq, Inhabited

/-- The name of an outcome. -/
def RunOutcome.name : RunOutcome → String
  | .solved => "solved"
  | .exhausted => "exhausted"
  | .outOfTime => "outOfTime"
  | .skipped => "skipped"

/-- The result of the portfolio: the fits in order (mode (a)'s first), with
their tokens; the outcome, the fits, and the time of each run; and the rank of
the expected program among the fits, with the mode that found it. -/
structure Portfolio where
  /-- The fits, each once, in the order of the runs. -/
  fits : Array Expr := #[]
  /-- The tokens of the fits. -/
  fitTokens : Array (Array (Nat × Nat)) := #[]
  /-- How mode (a) ended. -/
  hectare : RunOutcome := .skipped
  /-- The fits of mode (a). -/
  hectareFits : Nat := 0
  /-- The time of mode (a). -/
  hectareNanos : Nat := 0
  /-- How the search over states ended. -/
  states : RunOutcome := .skipped
  /-- The time of the search over states. -/
  statesNanos : Nat := 0
  /-- The rank of the expected program among the fits. -/
  rank : Option Nat := none
  /-- The mode that found the expected program: `a` or `b`. -/
  foundBy : String := ""
  /-- The leaves of the search. -/
  leaves : Nat := 0

/-- The lines of the erased library and goal for the proposer of mode (a)
(`hectare-propose`): the constants with a Hectare type, the locals (as
arguments when every local must occur, else as components), and the goal, in
the syntax of the oracle's replies, with the leaves' indices. `none` when
the goal or a required local has no Hectare type. -/
def proposerInput (leaves : Array Leaf) (goalType : Expr) (useAll : Bool) : MetaM (Option (Array String)) := do
  let mut rigid : FVarIdMap String := {}
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isUniverse decl.type then rigid := rigid.insert decl.fvarId s!"@T{rigid.size}"
  let mut library := #[]
  let mut arguments := #[]
  for index in [0:leaves.size] do
    match leaves[index]! with
    | .const name =>
      let some info := (← getEnv).find? name | continue
      if let .ok erased ← eraseConstantType info.type then
        if !erased.anyResult then
          library := library.push s!"component\t{index}\t{name}\t{erased.render}"
    | .fvar fvar name =>
      match ← eraseType {} rigid (← inferType fvar) with
      | .ok erased =>
        if useAll then arguments := arguments.push s!"argument\t{index}\t{name}\t{erased.render}"
        else library := library.push s!"component\t{index}\t{name}\t{erased.render}"
      | .error _ => if useAll then return none
  match ← eraseType {} rigid goalType with
  | .ok erased => return some ((library.push "end" ++ arguments).push s!"goal\t{erased.render}" |>.push "end")
  | .error _ => return none

/-- The child process of the proposer, with pipes. -/
abbrev Proposer := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .null }

/-- Answer the proposer's `extend` requests with the walk, and keep the fits,
until it ends, the deadline passes, the expected tokens fit, or there are
enough fits. -/
partial def serveProposer (child : Proposer) (deadline want : Nat) (expected : Array (Nat × Nat))
    (held : Array (Nat × Nat)) (fits : Array (Expr × Array (Nat × Nat))) :
    WalkM (RunOutcome × Array (Expr × Array (Nat × Nat))) := do
  if (← now) > deadline then return (.outOfTime, fits)
  let line ← child.stdout.getLine
  match (line.replace "\n" "").splitOn "\t" with
  | ["end", reason] => return (if reason == "outOfTime" then .outOfTime else .exhausted, fits)
  | "extend" :: kept :: tokens =>
    let some kept := kept.toNat? | return (.exhausted, fits)
    let parsed := (tokens.filterMap parseToken).toArray
    truncate kept
    let outcome ← extend parsed
    let program := held.extract 0 kept ++ parsed
    match outcome with
    | .died index =>
      child.stdin.putStrLn s!"died\t{index}"
      child.stdin.flush
      serveProposer child deadline want expected (program.extract 0 index) fits
    | .done ok =>
      child.stdin.putStrLn s!"done\t{if ok then 1 else 0}"
      child.stdin.flush
      let mut fits := fits
      if ok then
        if let some term := (← get).lastFit then
          if !fits.any (·.1 == term) then fits := fits.push (term, program)
      if (!expected.isEmpty && program == expected && ok) || fits.size ≥ want then return (.solved, fits)
      serveProposer child deadline want expected program fits
  | _ => return (.exhausted, fits)

/-- The portfolio of `hectare?` for a goal: mode (a), Hectare's programs over
the erased leaves (with the proposer of the variable `HECTARE_PROPOSER`)
checked by the walk, for `budget` seconds; then, when it did not find enough
fits (it exhausted its bound or ran out of time), the search over states for
the rest of the `seconds`. The expected tokens (a leaf's name and its number
of children), when there are some, stop the portfolio when a run reaches
them. No assignment stays. -/
def hectarePortfolio (goal : MVarId) (config : HectareConfig) (expected : Array (String × Nat) := #[]) :
    MetaM Portfolio :=
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let (leaves, constants) ← searchLeaves goalType
    -- An expected leaf that is not a leaf here can never be reached.
    let expectedTokens := expected.map fun (name, children) =>
      ((leaves.findIdx? (·.name.toString == name)).getD leaves.size, children)
    let required := if config.useAll then (List.range (leaves.size - constants)).map (· + constants) else []
    let start ← now
    let deadline := start + config.seconds * 1000000000
    let mut result : Portfolio := { leaves := leaves.size }
    let mut fits : Array (Expr × Array (Nat × Nat)) := #[]
    let mut solved := false
    -- Mode (a).
    let proposer ← IO.getEnv "HECTARE_PROPOSER"
    if let some path := proposer.filter (fun _ => config.budget > 0) then
      if let some input ← proposerInput leaves goalType config.useAll then
        let argumentOnly := if leaves.any (·.name == ``id) then #["id"] else #[]
        let child ← IO.Process.spawn
          { cmd := path, args := #[toString config.size, toString config.budget] ++ argumentOnly,
            stdin := .piped, stdout := .piped, stderr := .null }
        for line in input do child.stdin.putStrLn line
        child.stdin.flush
        let saved ← Meta.saveState
        let root ← mkFreshExprMVar goalType
        let walk : Walk := { root := root.mvarId!, goalType, leaves, stateLeaves := leaves }
        let ((outcome, found), _) ←
          (serveProposer child (min deadline (start + config.budget * 1000000000)) config.suggestions expectedTokens #[] #[]).run walk
        saved.restore
        child.kill
        discard child.wait
        fits := found
        solved := outcome == .solved
        result := { result with hectare := outcome, hectareFits := found.size, hectareNanos := (← now) - start }
    -- The search over states, for the rest of the time.
    let middle ← now
    if !solved && middle < deadline then
      let walk : Walk := { root := goal, goalType, leaves := #[], stateLeaves := leaves, checks := { index := true } }
      let initial : States := { deadline, collect := config.suggestions + fits.size }
      let saved ← Meta.saveState
      let ((_, states), _) ← ((searchSizes config.size expectedTokens required).run initial).run walk
      saved.restore
      for (term, tokens) in states.collected.zip states.collectedTokens do
        if !fits.any (·.1 == term) then fits := fits.push (term, tokens)
      let outcome := if states.found.isSome || fits.size ≥ config.suggestions then RunOutcome.solved
        else if states.timedOut then .outOfTime else .exhausted
      result := { result with states := outcome, statesNanos := (← now) - middle }
    let rank := if expectedTokens.isEmpty then none else (fits.findIdx? (·.2 == expectedTokens)).map (· + 1)
    let foundBy := match rank with
      | some r => if r ≤ result.hectareFits then "a" else "b"
      | none => ""
    return { result with
      fits := (fits.map (·.1)).extract 0 (max config.suggestions (rank.getD 0)),
      fitTokens := fits.map (·.2), rank, foundBy }

end Oracle
