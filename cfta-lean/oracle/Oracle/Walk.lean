import Lean
import Std.Data.HashMap

/-!
# The checks of a program walk inside Lean's elaborator

A walk builds a program in preorder: each step gives the leftmost open goal a
leaf (a constant or a local of the query) with so many children. The step is
a refinement: the leaf, applied to fresh metavariables for its implicit,
instance-implicit, and `k` explicit arguments, must have the goal's type. The
explicit metavariables are the children's goals.

* The leaf's type is instantiated binder by binder. An implicit binder gets a
  natural metavariable and an instance-implicit binder a synthetic one, a
  pending instance problem. The implicit and instance-implicit binders after
  the `k`-th explicit one are instantiated too, as Lean's application
  elaborator does.
* `isDefEq` unifies the instantiated result type with the goal's type, with
  the first-order approximations of `approxDefEq`, as Lean's application
  elaborator does.
* A pending instance problem goes to `synthInstance?` when its type has no
  metavariable outside the class's out-parameters. A problem that fails kills
  the step. A problem with metavariables stays pending: a later step can fix
  them. This is the counterpart of the GHC side's rule that a prefix dies only
  when a wanted without a unification variable fails.
* A program is complete when no goal is open and no instance problem is
  pending. Its term, with the metavariables instantiated, must have no
  metavariable left, and must pass `Meta.check`.

The checks of a step form a cascade, cheapest first: the arity of the leaf,
an optional comparison of the heads of the two types (`Checks.head`), `isDefEq`,
and `synthInstance?`, which can also wait until the program is complete
(`Checks.synthAtEnd`). Each level counts its rejections, its passes, and its
time, so that a hybrid of cheap and expensive checks is a configuration.

A step assigns metavariables and does not undo itself. The walk keeps a stack
of frames: frame `i` holds the `MetaM` state before step `i` (`saveState`) and
the walker after it. Lean's metavariable context is a persistent map, so a
snapshot keeps a pointer, and a restore writes it back: no walk over the
variables, as GHC's mutable unification variables need.
-/

namespace Oracle

open Lean Meta

/-- A leaf of a program: a constant, with fresh universe levels at each use,
or a local of the query's context. -/
inductive Leaf where
  /-- A constant of the environment. -/
  | const (name : Name)
  /-- A local of the query: an explicit argument of the goal. -/
  | fvar (local_ : Expr) (name : Name)
  deriving Inhabited

/-- The name of a leaf. -/
def Leaf.name : Leaf → Name
  | .const name => name
  | .fvar _ name => name

/-- The expression of a leaf, with fresh universe level metavariables for a
universe-polymorphic constant. -/
def Leaf.instantiate : Leaf → MetaM Expr
  | .const name => mkConstWithFreshMVarLevels name
  | .fvar local_ _ => pure local_

/-- The counters of a walk. A time is in nanoseconds. -/
structure Counters where
  /-- The steps tried. -/
  steps : Nat := 0
  /-- The steps whose leaf has fewer explicit arguments than the step needs. -/
  arityRejects : Nat := 0
  /-- The time of the instantiation of the leaves' binders. -/
  arityNanos : Nat := 0
  /-- The comparisons of the heads of the leaf's result type and the goal type. -/
  headChecks : Nat := 0
  /-- The comparisons of the heads that killed a step. -/
  headRejects : Nat := 0
  /-- The time of the comparisons of the heads. -/
  headNanos : Nat := 0
  /-- The steps that `isDefEq` killed. -/
  unifyRejects : Nat := 0
  /-- The time in `isDefEq`. -/
  unifyNanos : Nat := 0
  /-- The steps that called `synthInstance?` on no problem. -/
  synthSkips : Nat := 0
  /-- The calls of `synthInstance?`. -/
  synthCalls : Nat := 0
  /-- The calls of `synthInstance?` that killed a step. -/
  synthPrunes : Nat := 0
  /-- The time in `synthInstance?`. -/
  synthNanos : Nat := 0
  /-- The snapshots before the steps. -/
  saves : Nat := 0
  /-- The time of the snapshots. -/
  saveNanos : Nat := 0
  /-- The restores of a snapshot. -/
  restores : Nat := 0
  /-- The time of the restores. -/
  restoreNanos : Nat := 0
  /-- The complete programs checked. -/
  completes : Nat := 0
  /-- The complete programs that fit. -/
  fits : Nat := 0
  /-- The time of the checks of complete programs, with `Meta.check`. -/
  completeNanos : Nat := 0
  /-- The steps that threw an exception. -/
  errors : Nat := 0
  /-- The requests to extend the current prefix. -/
  extensions : Nat := 0
  /-- The time inside the requests to extend, without the reading and writing of lines. -/
  extendNanos : Nat := 0
  deriving Inhabited

/-- The counters as `key=value` fields. -/
def Counters.fields (c : Counters) : List String :=
  [ s!"steps={c.steps}", s!"arityRejects={c.arityRejects}", s!"arityNanos={c.arityNanos}"
  , s!"headChecks={c.headChecks}", s!"headRejects={c.headRejects}", s!"headNanos={c.headNanos}"
  , s!"unifyRejects={c.unifyRejects}"
  , s!"unifyNanos={c.unifyNanos}", s!"synthSkips={c.synthSkips}", s!"synthCalls={c.synthCalls}"
  , s!"synthPrunes={c.synthPrunes}", s!"synthNanos={c.synthNanos}", s!"saves={c.saves}"
  , s!"saveNanos={c.saveNanos}", s!"restores={c.restores}", s!"restoreNanos={c.restoreNanos}"
  , s!"completes={c.completes}", s!"fits={c.fits}", s!"completeNanos={c.completeNanos}"
  , s!"errors={c.errors}", s!"extensions={c.extensions}", s!"extendNanos={c.extendNanos}" ]

/-- The optional levels of the cascade of a step. -/
structure Checks where
  /-- Compare the heads of the leaf's result type and the goal type before `isDefEq`. -/
  head : Bool := false
  /-- Call `synthInstance?` only on the complete program, not at each step. -/
  synthAtEnd : Bool := false
  /-- Look up the leaves of a new state in a discrimination tree of their result
  types, as `exact?` does, and step only those (the search over states). -/
  index : Bool := false

/-- The state of a program walk: the goals still open, leftmost first, and the
instance problems still pending. -/
structure Walker where
  /-- The open goals, leftmost first. -/
  goals : List MVarId
  /-- The instance problems that still have metavariables. -/
  pending : List MVarId

/-- A checked step: the state before it, and the walker after it. -/
structure Frame where
  /-- The `MetaM` state before the step. -/
  saved : Meta.SavedState
  /-- The walker after the step. -/
  walker : Walker

/-- A walk for one goal: the root metavariable, the leaves, the frames of the
current prefix, and the counters. -/
structure Walk where
  /-- The metavariable of the whole program. -/
  root : MVarId
  /-- The goal type. -/
  goalType : Expr
  /-- The leaves with a Hectare type, by their index in the protocol: the
  components, then the locals. -/
  leaves : Array Leaf
  /-- The constants of the library without a Hectare type: in the protocol,
  the leaf of the index `leaves.size + i` is `others[i]`. -/
  others : Array Leaf := #[]
  /-- The leaves of the search over states: every constant of the library,
  also the ones without a Hectare type, and the locals. -/
  stateLeaves : Array Leaf := #[]
  /-- The goal types of the requests `goals` and `transitions`, by their
  key: abstracted, as `abstractMVars` gives them. -/
  goalKeys : Array AbstractMVarsResult := #[]
  /-- The key of each abstracted goal type. -/
  goalIds : Std.HashMap Expr Nat := {}
  /-- The discrimination trees of the leaves of the protocol for the requests
  `transitions`, one for each number of children. -/
  goalIndex : Array (DiscrTree Nat) := #[]
  /-- The frames of the current prefix, outermost first. -/
  frames : Array Frame := #[]
  /-- The counters. -/
  counters : Counters := {}
  /-- The term of the last program that fits. -/
  lastFit : Option Expr := none
  /-- The optional levels of the cascade. -/
  checks : Checks := {}

/-- The monad of a walk. -/
abbrev WalkM := StateRefT Walk MetaM

/-- The leaf of an index of the protocol: one of `leaves`, then one of `others`. -/
def Walk.leafAt (w : Walk) (index : Nat) : Option Leaf :=
  w.leaves[index]? <|> w.others[index - w.leaves.size]?

/-- Change the counters. -/
def count (f : Counters → Counters) : WalkM Unit :=
  modify fun w => { w with counters := f w.counters }

/-- The nanoseconds since some fixed time. -/
def now : IO Nat := IO.monoNanosNow

/-- Instantiate the binders of a leaf's type for `k` explicit arguments: the
arguments, the explicit ones (the children's goals), the instance problems,
and the result type. `none` when the type has fewer explicit binders, also
after `whnf`. -/
partial def instantiateBinders (type : Expr) (k : Nat) :
    MetaM (Option (Array Expr × Array MVarId × Array MVarId × Expr)) :=
  go type k #[] #[] #[]
where
  /-- Instantiate the next binder, with `left` explicit binders still to go. -/
  go (type : Expr) (left : Nat) (arguments : Array Expr) (children instances : Array MVarId) :
      MetaM (Option (Array Expr × Array MVarId × Array MVarId × Expr)) := do
    match type with
    | .forallE _ domain body info =>
      if info.isExplicit then
        if left == 0 then return some (arguments, children, instances, type)
        let m ← mkFreshExprMVar domain
        go (body.instantiate1 m) (left - 1) (arguments.push m) (children.push m.mvarId!) instances
      else if info.isInstImplicit then
        let m ← mkFreshExprMVar domain .synthetic
        go (body.instantiate1 m) left (arguments.push m) children (instances.push m.mvarId!)
      else if info.isStrictImplicit && left == 0 then
        return some (arguments, children, instances, type)
      else
        let m ← mkFreshExprMVar domain
        go (body.instantiate1 m) left (arguments.push m) children instances
    | _ =>
      if left == 0 then return some (arguments, children, instances, type)
      let reduced ← whnf type
      if reduced.isForall then go reduced left arguments children instances else return none

/-- The rigid head of a type after `whnf`: an inductive type, a constructor, an
axiom, or an opaque constant; a free variable; a universe; or a function type.
`none` when a metavariable, a definition that `whnf` cannot unfold, or anything
else heads it, because then `isDefEq` may still succeed. -/
def rigidHead (type : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  match type.getAppFn with
  | .const name _ =>
    match (← getEnv).find? name with
    | some (.inductInfo _) | some (.ctorInfo _) | some (.axiomInfo _) | some (.opaqueInfo _) =>
      return some (.const name [])
    | _ => return none
  | .fvar id => return some (.fvar id)
  | .sort _ => return some (.sort Level.zero)
  | .forallE .. => return some (.sort Level.one)
  | _ => return none

/-- Whether the rigid heads of two types differ, so that they cannot unify. -/
def headsClash (left right : Expr) : MetaM Bool := do
  match ← rigidHead left, ← rigidHead right with
  | some a, some b => return a != b
  | _, _ => return false

/-- Whether an instance problem must wait: its type has a metavariable outside
the class's out-parameters. -/
def blocked (type : Expr) : MetaM Bool := do
  if !type.hasExprMVar then return false
  match type.getAppFn with
  | .const name _ =>
    match getOutParamPositions? (← getEnv) name with
    | some positions =>
      let arguments := type.getAppArgs
      return (List.range arguments.size).any fun i => !positions.contains i && arguments[i]!.hasExprMVar
    | none => return true
  | _ => return true

/-- Solve the instance problems that no longer wait, and keep the others.
`none` when a problem has no instance. -/
def solvePending (pending : List MVarId) : WalkM (Option (List MVarId)) := do
  let mut kept := #[]
  let mut called := false
  for problem in pending do
    if ← problem.isAssigned then continue
    let type ← instantiateMVars (← problem.getType)
    if ← blocked type then
      kept := kept.push problem
      continue
    called := true
    let start ← now
    let solution ← tryCatch (synthInstance? type) fun _ => pure none
    let ok ← match solution with
      | some value => isDefEq (.mvar problem) value
      | none => pure false
    let stop ← now
    count fun c => { c with synthCalls := c.synthCalls + 1, synthNanos := c.synthNanos + (stop - start) }
    unless ok do
      count fun c => { c with synthPrunes := c.synthPrunes + 1 }
      return none
  unless called do count fun c => { c with synthSkips := c.synthSkips + 1 }
  return some kept.toList

/-- Give the leftmost open goal a leaf with so many children. `none` when the
leaf does not fit, or when an instance problem has no instance. The step
assigns metavariables; take a snapshot before it to undo it. -/
def step (walker : Walker) (leaf : Leaf) (children : Nat) : WalkM (Option Walker) := do
  match walker.goals with
  | [] => return none
  | goal :: rest =>
    count fun c => { c with steps := c.steps + 1 }
    if ← goal.isAssigned then return none
    let function ← leaf.instantiate
    let start ← now
    let instantiated ← instantiateBinders (← inferType function) children
    let stop ← now
    count fun c => { c with arityNanos := c.arityNanos + (stop - start) }
    let some (arguments, childGoals, instances, result) := instantiated
      | do
        count fun c => { c with arityRejects := c.arityRejects + 1 }
        return none
    let goalType ← goal.getType
    let checks := (← get).checks
    if checks.head then
      let start ← now
      let clash ← headsClash result goalType
      let stop ← now
      count fun c => { c with
        headChecks := c.headChecks + 1, headNanos := c.headNanos + (stop - start),
        headRejects := c.headRejects + (if clash then 1 else 0) }
      if clash then return none
    let start ← now
    -- First-order approximation, as Lean's application elaborator unifies:
    -- `?f ?β =?= Option β` gives `?f := Option`.
    let ok ← approxDefEq <| isDefEq result goalType
    let stop ← now
    count fun c => { c with unifyNanos := c.unifyNanos + (stop - start) }
    unless ok do
      count fun c => { c with unifyRejects := c.unifyRejects + 1 }
      return none
    goal.assign (mkAppN function arguments)
    if checks.synthAtEnd then
      return some { goals := childGoals.toList ++ rest, pending := instances.toList ++ walker.pending }
    match ← solvePending (instances.toList ++ walker.pending) with
    | some pending => return some { goals := childGoals.toList ++ rest, pending }
    | none => return none

/-- The walker of the current prefix: the last frame's, or the start. -/
def current : WalkM Walker := do
  let w ← get
  match w.frames.back? with
  | some frame => return frame.walker
  | none => return { goals := [w.root], pending := [] }

/-- The instantiated program of a walk, when it has no metavariable left,
passes `Meta.check`, and has the goal type. -/
def checkProgram (root : MVarId) (goalType : Expr) : MetaM (Option Expr) := do
  let term ← instantiateMVars (.mvar root)
  if term.hasExprMVar then return none
  Meta.check term
  if ← isDefEq (← inferType term) goalType then
    return some term
  return none

/-- Whether a walker's program is complete and fits, for the root
metavariable and the goal type. The term of a fit is kept as the walk's last
fit. A pending problem that still has metavariables is ambiguous, and the
program does not fit: there is no defaulting. The check leaves no assignment
behind. -/
def completeWalker (root : MVarId) (goalType : Expr) (walker : Walker) : WalkM Bool := do
  unless walker.goals.isEmpty do return false
  count fun c => { c with completes := c.completes + 1 }
  let start ← now
  let saved ← Meta.saveState
  -- With the instance problems left to the end, solve them now.
  let solved ← if (← get).checks.synthAtEnd then solvePending walker.pending else pure (some walker.pending)
  let unsolved ← (solved.getD []).filterM fun problem => return !(← problem.isAssigned)
  let result ← if solved.isSome && unsolved.isEmpty then
      tryCatch (checkProgram root goalType) fun _ => pure none
    else pure none
  saved.restore
  let stop ← now
  count fun c => { c with completeNanos := c.completeNanos + (stop - start), fits := c.fits + (if result.isSome then 1 else 0) }
  if result.isSome then modify fun w => { w with lastFit := result }
  return result.isSome

/-- Whether the current program of the walk is complete and fits. -/
def complete : WalkM Bool := do
  let w ← get
  completeWalker w.root w.goalType (← current)

/-- Keep the first `k` frames: restore the snapshot before step `k`. -/
def truncate (k : Nat) : WalkM Unit := do
  let w ← get
  if h : k < w.frames.size then
    let start ← now
    w.frames[k].saved.restore
    let stop ← now
    count fun c => { c with restores := c.restores + 1, restoreNanos := c.restoreNanos + (stop - start) }
    modify fun w => { w with frames := w.frames.extract 0 k }

/-- The outcome of an extension: `died n` when the token at index `n` (counted
from the root) failed, and the walk holds the `n` frames before it; `done fits`
when every token stepped, with whether the program fits. -/
inductive Extension where
  /-- The token at this index failed. -/
  | died (index : Nat)
  /-- Every token stepped; whether the program fits. -/
  | done (fits : Bool)

/-- Step the tokens (a leaf index and a number of children) after the current
prefix, then check the complete program. -/
def extend (tokens : Array (Nat × Nat)) : WalkM Extension := do
  for (index, children) in tokens do
    let walker ← current
    let w ← get
    let some leaf := w.leafAt index | return .died w.frames.size
    let start ← now
    let saved ← Meta.saveState
    let stop ← now
    count fun c => { c with saves := c.saves + 1, saveNanos := c.saveNanos + (stop - start) }
    let stepped ← tryCatch (step walker leaf children) fun _ => do
      count fun c => { c with errors := c.errors + 1 }
      pure none
    match stepped with
    | some walker' => modify fun w => { w with frames := w.frames.push { saved, walker := walker' } }
    | none =>
      let start ← now
      saved.restore
      let stop ← now
      count fun c => { c with restores := c.restores + 1, restoreNanos := c.restoreNanos + (stop - start) }
      return .died w.frames.size
  return .done (← complete)

end Oracle
