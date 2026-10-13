import MicroCFTA.BoundedPruningFix
import MicroCFTA.PruneCorrectness

/-!
# Bounded pruning call sites

The edge caller repeats equality narrowing before it tests empty children
and runs the semantic pass. The recursive caller prunes its body with a new
64-round budget. Only its direct revisit receives the decreased local budget.
Successful callback contracts remain explicit. A local round bound does not
bound solver time, interned construction, or recursively reset body work.
-/

namespace MicroCFTA.BoundedPruningCaller

open Language PruneSchedule PruneCorrectness PruneCandidates BoundedPruningFix

variable {Node Edge Value : Type}

/-- The source uses this budget for each new equality or recursive-node loop. -/
def pruneRounds : Int := 64

/-- Replace already-pruned children and perform bounded equality narrowing. -/
def narrowed [DecidableEq Edge] (ops : Operations Node Edge) (edge : Edge)
    (children : List Node) : Edge :=
  fixWithin pruneRounds ops.narrow (ops.replaceChildren edge children)

/-- The bounded equality caller preserves the original transition meaning. -/
theorem narrowed_exact [DecidableEq Edge] (ops : Operations Node Edge)
    (meaning : Node → Value → Prop) (edgeMeaning : Edge → Value → Prop)
    (laws : Laws ops meaning edgeMeaning) (edge : Edge) (children : List Node)
    (same : All₂ (Equivalent meaning) (ops.children edge) children) (value : Value) :
    edgeMeaning (narrowed ops edge children) value ↔ edgeMeaning edge value := by
  exact (meaning_exact ops.narrow edgeMeaning laws.narrow pruneRounds
    (ops.replaceChildren edge children) value).trans (laws.replaceChildren edge children same value)

/-- The source remainder of pruneEdge runs after its children have completed. -/
def edgePhase [DecidableEq Edge] (ops : Operations Node Edge) (build : Build Node)
    (edge : Edge) (children : List Node) : Except Error (List Edge × Build Node) :=
  let reduced := narrowed ops edge children
  if (ops.children reduced).any ops.empty then .ok ([], build)
  else ops.evaluate build reduced

/-- Empty-child rejection and semantic pruning preserve the bounded edge language. -/
theorem edgePhase_exact [DecidableEq Edge] (ops : Operations Node Edge)
    (meaning : Node → Value → Prop) (edgeMeaning : Edge → Value → Prop)
    (laws : Laws ops meaning edgeMeaning) (build : Build Node) (edge : Edge) (children : List Node)
    (same : All₂ (Equivalent meaning) (ops.children edge) children)
    (retained : List Edge) (after : Build Node)
    (success : edgePhase ops build edge children = .ok (retained, after)) :
    (∀ value, Denotes edgeMeaning retained value ↔ edgeMeaning edge value) ∧ after.cache = build.cache := by
  unfold edgePhase at success
  dsimp only at success
  split at success
  next empty =>
    have result : retained = [] ∧ after = build := by simpa using success.symm
    obtain ⟨rfl, rfl⟩ := result
    refine ⟨?_, rfl⟩
    intro value
    have absent : ¬edgeMeaning edge value := fun accepted =>
      laws.emptyChild _ empty value ((narrowed_exact ops meaning edgeMeaning laws edge children same value).mpr accepted)
    simp [Denotes, absent]
  next nonempty =>
    obtain ⟨semantic, cache⟩ := laws.evaluate build (narrowed ops edge children) retained after success
    exact ⟨fun value => (semantic value).trans (narrowed_exact ops meaning edgeMeaning laws edge children same value), cache⟩

/-- The source pruneMu caller leaves body work and node dispatch as callbacks. -/
def pruneMu [DecidableEq Node] (ops : Operations Node Edge)
    (visit : Int → Build Node → Node → Except Error (Node × Build Node))
    (rounds : Int) (build : Build Node) (node body : Node) : Except Error (Node × Build Node) := do
  let (pruned, next) ← visit pruneRounds {build with binders := node :: build.binders} body
  let rebuilt := ops.rebuildBinder node pruned
  if rebuilt = node ∨ rounds ≤ 1 then .ok (rebuilt, next)
  else visit (rounds - 1) next rebuilt

/-- A recursive callback must preserve node meaning and the identity cache on success. -/
def CallbackExact (visit : Int → Build Node → Node → Except Error (Node × Build Node))
    (meaning : Node → Value → Prop) : Prop :=
  ∀ rounds build node result after, CacheValid meaning build → visit rounds build node = .ok (result, after) →
    Equivalent meaning node result ∧ CacheValid meaning after

/-- The current recursive caller preserves the rebuilt language when its budget expires. -/
theorem pruneMu_exact [DecidableEq Node] (ops : Operations Node Edge)
    (meaning : Node → Value → Prop) (edgeMeaning : Edge → Value → Prop)
    (laws : Laws ops meaning edgeMeaning)
    (visit : Int → Build Node → Node → Except Error (Node × Build Node))
    (callback : CallbackExact visit meaning) (rounds : Int) (build : Build Node)
    (node body result : Node) (after : Build Node) (view : ops.view node = .binder body)
    (valid : CacheValid meaning build) (success : pruneMu ops visit rounds build node body = .ok (result, after)) :
    Equivalent meaning node result ∧ CacheValid meaning after := by
  cases bodyResult : visit pruneRounds {build with binders := node :: build.binders} body with
  | error failure => simp [pruneMu, bodyResult, Bind.bind, Except.bind] at success
  | ok pair =>
      obtain ⟨pruned, next⟩ := pair
      have bodyExact := callback pruneRounds {build with binders := node :: build.binders}
        body pruned next valid bodyResult
      have rebuilt := laws.binder node body pruned view bodyExact.1
      simp only [pruneMu, bodyResult, Bind.bind, Except.bind] at success
      split at success
      next stop =>
        obtain ⟨rfl, rfl⟩ := (by simpa using success : ops.rebuildBinder node pruned = result ∧ next = after)
        exact ⟨rebuilt, bodyExact.2⟩
      next more =>
        have nextExact := callback (rounds - 1) next (ops.rebuildBinder node pruned)
          result after bodyExact.2 success
        exact ⟨fun value => (rebuilt value).trans (nextExact.1 value), nextExact.2⟩

/-- One or fewer rounds still performs its body pass and returns the rebuilt node. -/
theorem pruneMu_last [DecidableEq Node] (ops : Operations Node Edge)
    (visit : Int → Build Node → Node → Except Error (Node × Build Node))
    (rounds : Int) (build : Build Node) (node body pruned : Node) (after : Build Node)
    (last : rounds ≤ 1)
    (completed : visit pruneRounds {build with binders := node :: build.binders} body = .ok (pruned, after)) :
    pruneMu ops visit rounds build node body = .ok (ops.rebuildBinder node pruned, after) := by
  simp [pruneMu, completed, last, Bind.bind, Except.bind]

/-- The direct recursive revisit decreases its positive local budget. -/
theorem revisit_budget (rounds : Int) (more : ¬rounds ≤ 1) :
    0 < rounds - 1 ∧ rounds - 1 < rounds ∧ (rounds - 1).toNat + 1 = rounds.toNat := by omega

/-- A chain records completed recursive-node passes, excluding nested body work. -/
inductive MuChain (step : Node → Node → Prop) : Int → Node → Node → Nat → Prop where
  | last (rounds : Int) (node rebuilt : Node) (completed : step node rebuilt)
      (stop : rebuilt = node ∨ rounds ≤ 1) : MuChain step rounds node rebuilt 1
  | next (rounds : Int) (node rebuilt result : Node) (calls : Nat)
      (completed : step node rebuilt) (changed : rebuilt ≠ node) (more : 1 < rounds)
      (tail : MuChain step (rounds - 1) rebuilt result calls) :
      MuChain step rounds node result (calls + 1)

/-- Consecutive binder revisits complete at most their positive local budget. -/
theorem muChain_calls_le (step : Node → Node → Prop) (rounds : Int)
    (node result : Node) (calls : Nat) (completed : MuChain step rounds node result calls) :
    calls ≤ max 1 rounds.toNat := by
  induction completed with
  | last => omega
  | next rounds node rebuilt result calls completed changed more tail ih =>
      have := revisit_budget rounds (by omega)
      omega

/-- Every completed local pass preserves the chain's language, including budget exits. -/
theorem muChain_exact (step : Node → Node → Prop) (meaning : Node → Value → Prop)
    (preserved : ∀ node rebuilt, step node rebuilt → Equivalent meaning node rebuilt)
    (rounds : Int) (node result : Node) (calls : Nat) (completed : MuChain step rounds node result calls) :
    Equivalent meaning node result := by
  induction completed with
  | last rounds node rebuilt completed stop => exact preserved node rebuilt completed
  | next rounds node rebuilt result calls completed changed more tail ih =>
      exact fun value => (preserved node rebuilt completed value).trans (ih value)

end MicroCFTA.BoundedPruningCaller
