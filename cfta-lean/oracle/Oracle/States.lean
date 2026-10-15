import Lean
import Std.Data.HashMap
import Oracle.Walk

/-!
# States from goals: the automaton built from Lean's own goals

Here Lean builds the automaton, without Hectare and without erasure. A state
is a goal type, with its metavariables instantiated and abstracted
(`abstractMVars`, so a state is a goal up to the renaming of its
metavariables), a size, and the arguments of the query that the program of
the goal must use, as Hectare requires of a whole program: a state with more
such arguments than its size is empty, a leaf that is one of them uses it,
and each of the others goes to one child. A transition of a state is a leaf (any constant of the library, also one
without a Hectare type, or a local of the query) with `k` children whose refinement step succeeds on a fresh goal of the state's type,
with the splits of the remaining size over the children whose states are not
empty. The step is the walk's (`Oracle.Walk.step`): `isDefEq`, and
`synthInstance?` on each instance problem without metavariables. A state is
built once, the first time that a goal reaches it, and kept in a table.

With `Checks.index`, a new state steps only the leaves that a discrimination
tree of their result types (`DiscrTree`, as `exact?` and `apply?` index their
candidates) gives for its goal type: there is one tree for each number of
children, built once for a search. A lookup with `getUnify` keeps every leaf
whose result may unify with the goal up to reducible definitions, so the
index changes the cost of a state, not its transitions, except for a goal
that only unfolds to a leaf's result at the default transparency.

The children of a transition are states of their own, so their shared
metavariables are not tied in the table: a state over-approximates the
programs of a goal. The search ties them. It walks the table in preorder, and
it steps each transition again on the real goal, so that the earlier
children's assignments reach the later children before their states are
looked up. The instance problems that still have metavariables stay pending
in the walker, and the step decides them when their types are known.
-/

namespace Oracle

open Lean Meta

/-- The leaves by their result type: one discrimination tree for each number of
children, with the leaves' indices as values. -/
abbrev LeafIndex := Array (DiscrTree Nat)

/-- A goal's budget: its size, and the arguments that its program must use. -/
abbrev Budget := Nat × List Nat

/-- A transition of a state: a leaf, its number of children, and the splits of
the remaining budget over the children whose states are not empty. -/
structure Transition where
  /-- The leaf's index. -/
  leaf : Nat
  /-- The number of children. -/
  children : Nat
  /-- The budgets of the children, for each split. -/
  splits : Array (List Budget)

/-- The table of states and the figures of a search. -/
structure States where
  /-- The transitions of each state: an abstracted goal type and a budget. -/
  table : Std.HashMap (Expr × Budget) (Array Transition) := {}
  /-- The steps that built the states. -/
  buildSteps : Nat := 0
  /-- The steps of the search on real goals. -/
  searchSteps : Nat := 0
  /-- The complete programs that the search reached. -/
  programs : Nat := 0
  /-- The complete programs that fit. -/
  fits : Nat := 0
  /-- The fits that use every argument of the query. -/
  relevant : Nat := 0
  /-- The size of the expected program, when the search found it. -/
  found : Option Nat := none
  /-- The time on the monotonic clock after which the search stops. -/
  deadline : Nat
  /-- Whether the search stopped at the deadline. -/
  timedOut : Bool := false
  /-- The states that were empty because they must use more arguments than their size. -/
  budgetPrunes : Nat := 0
  /-- The lookups of a state in the table. -/
  memoLookups : Nat := 0
  /-- The lookups that found the state. -/
  memoHits : Nat := 0
  /-- The time of the lookups: the abstraction of the goal type and the table. -/
  memoNanos : Nat := 0
  /-- The splits that a child's empty state killed. -/
  splitPrunes : Nat := 0
  /-- The splits whose children's states are not empty. -/
  splitPasses : Nat := 0
  /-- The index of the leaves, when `Checks.index` is on. -/
  index : LeafIndex := #[]
  /-- The pairs of a leaf and a number of children that the index skipped. -/
  indexSkips : Nat := 0
  /-- The pairs of a leaf and a number of children that the index let through. -/
  indexPasses : Nat := 0
  /-- The lookups in the index. -/
  indexLookups : Nat := 0
  /-- The time of the lookups in the index. -/
  indexNanos : Nat := 0
  /-- The entries of the index. -/
  indexEntries : Nat := 0
  /-- The time to build the index. -/
  indexBuildNanos : Nat := 0
  /-- The number of fits to collect, and stop after; none when `0`. -/
  collect : Nat := 0
  /-- The terms of the fits that use every argument, in the order of the search. -/
  collected : Array Expr := #[]
  /-- The tokens of the collected fits. -/
  collectedTokens : Array (Array (Nat × Nat)) := #[]

/-- The monad of a search over states. -/
abbrev StatesM := StateRefT States WalkM

/-- Whether the search has used nine tenths of the heartbeats of `maxHeartbeats`,
so that the caller (a tactic) has the rest. -/
def outOfHeartbeats : CoreM Bool := do
  let context ← read
  if context.maxHeartbeats == 0 then return false
  return ((← IO.getNumHeartbeats) - context.initHeartbeats) * 10 > context.maxHeartbeats * 9

/-- Whether the search must stop: its deadline has passed, or its heartbeats
are spent. -/
def stopping : StatesM Bool := do
  return (← now) > (← get).deadline || (← outOfHeartbeats)

/-- The ways to split a total into `k` positive parts, in lexicographic order. -/
partial def compositions (total : Nat) : Nat → List (List Nat)
  | 0 => if total == 0 then [[]] else []
  | k + 1 => (List.range' 1 (total - k)).flatMap fun first => (compositions (total - first) k).map (first :: ·)

/-- The ways to give each of the arguments to one of `k` children: for each
child, the arguments that it must use. The first argument goes to the
earliest children first, so that `f x y` comes before `f y x`. -/
def assignments (arguments : List Nat) (k : Nat) : List (List (List Nat)) :=
  arguments.foldl
    (fun sofar argument => sofar.flatMap fun sets =>
      (List.range k).map fun child => sets.modify child (· ++ [argument]))
    [List.replicate k []]

/-- The splits of a budget over `k` children: the sizes, and the arguments
of each child, with no child that must use more arguments than its size. -/
def budgetSplits (size : Nat) (arguments : List Nat) (k : Nat) : List (List Budget) :=
  (compositions size k).flatMap fun sizes =>
    (assignments arguments k).filterMap fun sets =>
      if (sizes.zip sets).all fun (childSize, set) => set.length ≤ childSize then some (sizes.zip sets) else none

/-- The numbers of children of a leaf in a program of a size: none for a leaf
alone, at least one otherwise. -/
def childCounts (size : Nat) : List Nat :=
  if size == 1 then [0] else List.range' 1 (size - 1)

/-- Index the leaves by their result type after `k` explicit arguments, for
each `k` below the bound, and give the number of entries. No assignment
stays. -/
def buildIndex (leaves : Array Leaf) (bound : Nat) : MetaM (LeafIndex × Nat) := do
  let mut trees : LeafIndex := Array.replicate bound DiscrTree.empty
  let mut entries := 0
  for index in [0:leaves.size] do
    for children in [0:bound] do
      let saved ← Meta.saveState
      let instantiated ← tryCatch (do instantiateBinders (← inferType (← leaves[index]!.instantiate)) children)
        fun _ => pure none
      if let some (_, _, _, result) := instantiated then
        let keys ← DiscrTree.mkPath result
        trees := trees.modify children (·.insertKeyValue keys index)
        entries := entries + 1
      saved.restore
  return (trees, entries)

/-- For each number of children below the size, whether the index lets each
leaf through for a goal type. -/
def allowedLeaves (type : Expr) (size : Nat) (leafCount : Nat) : StatesM (Array (Array Bool)) := do
  let start ← now
  let trees := (← get).index
  let mut allowed := #[]
  for children in [0:size] do
    let mut marks := Array.replicate leafCount false
    if h : children < trees.size then
      for found in ← trees[children].getUnify type do
        marks := marks.set! found true
    allowed := allowed.push marks
  let stop ← now
  modify fun s => { s with indexLookups := s.indexLookups + 1, indexNanos := s.indexNanos + (stop - start) }
  return allowed

/-- The transitions of the state of a goal type and a budget: built on the
first visit, then taken from the table. No assignment stays. -/
partial def stateOf (type : Expr) (budget : Budget) : StatesM (Array Transition) := do
  let (size, required) := budget
  if required.length > size then
    modify fun s => { s with budgetPrunes := s.budgetPrunes + 1 }
    return #[]
  let start ← now
  let abstracted ← abstractMVars (← instantiateMVars type)
  let key := (abstracted.expr, budget)
  let found := (← get).table[key]?
  let stop ← now
  modify fun s => { s with
    memoLookups := s.memoLookups + 1, memoNanos := s.memoNanos + (stop - start),
    memoHits := s.memoHits + (if found.isSome then 1 else 0) }
  if let some transitions := found then return transitions
  let saved ← Meta.saveState
  let (_, _, opened) ← openAbstractMVarsResult abstracted
  let leaves := (← getThe Walk).stateLeaves
  let useIndex := (← getThe Walk).checks.index
  let allowed ← if useIndex then allowedLeaves opened size leaves.size else pure #[]
  let mut transitions := #[]
  for index in [0:leaves.size] do
    -- A state that the deadline stops is not kept: its transitions would be
    -- too few.
    if ← stopping then
      saved.restore
      modify fun s => { s with timedOut := true }
      return #[]
    for children in childCounts size do
      if useIndex then
        if !allowed[children]![index]! then
          modify fun s => { s with indexSkips := s.indexSkips + 1 }
          continue
        modify fun s => { s with indexPasses := s.indexPasses + 1 }
      let before ← Meta.saveState
      let goal ← mkFreshExprMVar opened
      modify fun s => { s with buildSteps := s.buildSteps + 1 }
      let stepped ← tryCatch (step { goals := [goal.mvarId!], pending := [] } leaves[index]! children) fun _ => pure none
      let rest := required.erase index
      if let some walker := stepped then
        let childTypes ← walker.goals.mapM fun child => do instantiateMVars (← child.getType)
        let mut splits := #[]
        for split in budgetSplits (size - 1) rest children do
          let mut inhabited := true
          for (childType, childBudget) in childTypes.zip split do
            if (← stateOf childType childBudget).isEmpty then
              inhabited := false
              break
          if inhabited then
            splits := splits.push split
            modify fun s => { s with splitPasses := s.splitPasses + 1 }
          else
            modify fun s => { s with splitPrunes := s.splitPrunes + 1 }
        if !splits.isEmpty then transitions := transitions.push { leaf := index, children, splits }
      before.restore
  saved.restore
  modify fun s => { s with table := s.table.insert key transitions }
  return transitions

/-- Search the programs of the walker's goals, with a budget for each goal, in
preorder; stop at the expected tokens or at the deadline. `false` when the
search stops. -/
partial def searchStates (root : MVarId) (goalType : Expr) (expected : Array (Nat × Nat)) (required : List Nat)
    (walker : Walker) (budgets : List Budget) (tokens : Array (Nat × Nat)) : StatesM Bool := do
  if ← stopping then
    modify fun s => { s with timedOut := true }
    return false
  match walker.goals, budgets with
  | [], _ =>
    modify fun s => { s with programs := s.programs + 1 }
    if ← completeWalker root goalType walker then
      let relevant := required.all fun index => tokens.any (·.1 == index)
      modify fun s => { s with fits := s.fits + 1, relevant := s.relevant + (if relevant then 1 else 0) }
      let collect := (← get).collect
      if relevant && collect > 0 then
        let term := (← getThe Walk).lastFit
        modify fun s => { s with collected := s.collected ++ term.toArray, collectedTokens := s.collectedTokens.push tokens }
      if tokens == expected then
        modify fun s => { s with found := some tokens.size }
        return false
      if collect > 0 && (← get).collected.size ≥ collect then return false
    return true
  | goal :: _, budget :: rest =>
    let transitions ← stateOf (← goal.getType) budget
    let leaves := (← getThe Walk).stateLeaves
    for transition in transitions do
      let saved ← Meta.saveState
      modify fun s => { s with searchSteps := s.searchSteps + 1 }
      let stepped ← tryCatch (step walker leaves[transition.leaf]! transition.children) fun _ => pure none
      if let some walker' := stepped then
        for split in transition.splits do
          let again ← Meta.saveState
          let more ← searchStates root goalType expected required walker' (split ++ rest)
            (tokens.push (transition.leaf, transition.children))
          again.restore
          unless more do
            saved.restore
            return false
      saved.restore
    return true
  | _, _ => return true

/-- Search the programs of the walk's goal size by size, up to a bound, for the
expected tokens. -/
def searchSizes (bound : Nat) (expected : Array (Nat × Nat)) (required : List Nat) : StatesM Unit := do
  let goalType := (← getThe Walk).goalType
  if (← getThe Walk).checks.index then
    let start ← now
    let (index, entries) ← buildIndex (← getThe Walk).stateLeaves bound
    let stop ← now
    modify fun s => { s with index, indexEntries := entries, indexBuildNanos := stop - start }
  for size in [1:bound + 1] do
    let saved ← Meta.saveState
    let root ← mkFreshExprMVar goalType
    let more ← searchStates root.mvarId! goalType expected required { goals := [root.mvarId!], pending := [] } [(size, required)] #[]
    saved.restore
    unless more do return

/-! ## The requests of the generic search

The search over states of `cfta-generator` (`Data.CFTA.Gen.Synthesis.States`
on the Haskell side) keeps the table, the budgets, and the search itself, and
asks the oracle for the refinements of a goal: one round trip for each new
goal and set of numbers of children. A goal is a key, the index of its
abstracted type in `Walk.goalKeys`; the leaves are the leaves of the
protocol (`Walk.leafAt`), so that `extend` checks the programs of the search.
-/

/-- The key of a goal type: the index of its abstracted type, added on the
first visit. -/
def goalKey (type : Expr) : WalkM Nat := do
  let abstracted ← abstractMVars (← instantiateMVars type)
  if let some key := (← get).goalIds[abstracted.expr]? then return key
  let key := (← get).goalKeys.size
  modify fun w => { w with goalKeys := w.goalKeys.push abstracted, goalIds := w.goalIds.insert abstracted.expr key }
  return key

/-- The leaves of the protocol: the leaves with a Hectare type, then the others. -/
def protocolLeaves : WalkM (Array Leaf) := do
  return (← get).leaves ++ (← get).others

/-- The refinements of the goal of a key for numbers of children: each leaf of
the protocol whose step passes on a fresh goal of the key's type with one of
the numbers, with that number and the keys of the child goals; `none` when
the deadline (on the clock of `now`) passes first. With `Checks.index`, only
the leaves that the discrimination trees of `Walk.goalIndex` give are
stepped. No assignment stays. -/
def transitionsOf (key : Nat) (counts : List Nat) (deadline : Nat) :
    WalkM (Option (Array (Nat × Nat × Array Nat))) := do
  let some abstracted := (← get).goalKeys[key]? | return some #[]
  let leaves ← protocolLeaves
  let useIndex := (← get).checks.index
  let saved ← Meta.saveState
  let (_, _, opened) ← openAbstractMVarsResult abstracted
  -- For each number of children, the leaves that the index lets through.
  let mut allowed : Std.HashMap Nat (Array Bool) := {}
  if useIndex then
    let trees := (← get).goalIndex
    for children in counts do
      let mut marks := Array.replicate leaves.size false
      if h : children < trees.size then
        for found in ← trees[children].getUnify opened do
          marks := marks.set! found true
      allowed := allowed.insert children marks
  let mut found := #[]
  for index in [0:leaves.size] do
    if (← now) > deadline then
      saved.restore
      return none
    for children in counts do
      if useIndex && !((allowed[children]?.bind (·[index]?)).getD false) then continue
      let before ← Meta.saveState
      let goal ← mkFreshExprMVar opened
      let stepped ← tryCatch (step { goals := [goal.mvarId!], pending := [] } leaves[index]! children) fun _ => pure none
      if let some walker := stepped then
        let keys ← walker.goals.toArray.mapM fun child => do goalKey (← child.getType)
        found := found.push (index, children, keys)
      before.restore
  saved.restore
  return some found

end Oracle
