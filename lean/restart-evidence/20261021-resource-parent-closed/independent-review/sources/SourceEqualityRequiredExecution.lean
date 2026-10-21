import MicroCFTA.SourceEqualityRequiredWorkerComplete
import MicroCFTA.SourceEqualityRequiredComplete

/-!
# Finite required-path execution from original source construction

Graphs and instrumented execution agree in both directions. Completed graphs
have one returned value and cache. Initial closed source construction derives
finite stable execution without a supplied worker or callback completion law.
Independent language preservation remains a separate theorem.
-/
namespace MicroCFTA.SourceEqualityRequiredExecution
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredGraph
open SourceEqualityRequiredWorker SourceEqualityRequiredWorkerComplete SourceEqualityRequiredWorkerSound

/-- Stable completed executions of one function have one result and cache. -/
theorem stable_unique {evaluation : Nat → Nat → Result Symbol Guard A}
    {first second : A} {afterFirst afterSecond : State Symbol Guard}
    (left : StableRun evaluation first afterFirst) (right : StableRun evaluation second afterSecond) :
    first = second ∧ afterFirst = afterSecond := by
  obtain ⟨firstBound, firstHead, firstDone⟩ := left
  obtain ⟨secondBound, secondHead, secondDone⟩ := right
  have one := firstDone (max firstBound secondBound) (max firstHead secondHead)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have two := secondDone (max firstBound secondBound) (max firstHead secondHead)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact Result.done.inj (one.symm.trans two)

/-- Every completed physical node graph has the same final source value and cache. -/
theorem node_unique [DecidableEq (EdgeKey Symbol Guard)]
    {needed : Needed} {value first second : Value Symbol Guard} {before afterFirst afterSecond : State Symbol Guard}
    (left : RequireNode needed value before first afterFirst) (right : RequireNode needed value before second afterSecond) :
    first = second ∧ afterFirst = afterSecond := stable_unique (node_stable left) (node_stable right)

/-- Every successful graph retains the complete final invariants derived by closed completion. -/
theorem node_verified [DecidableEq (EdgeKey Symbol Guard)]
    {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after) (ready : Ready before)
    (available : Available before value) (closed : value.free = []) :
    Keeps before after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨actual, final, completed, keeps, resident, resultClosed⟩ :=
    SourceEqualityRequiredComplete.complete needed value before ready available closed
  obtain ⟨sameValue, sameState⟩ := node_unique completed trace
  cases sameValue
  cases sameState
  exact ⟨keeps, resident, resultClosed⟩

/-- Completed child graphs have one returned ordered list and final constructor cache. -/
theorem children_unique [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values first second : List (Value Symbol Guard)}
    {before afterFirst afterSecond : State Symbol Guard}
    (left : RequireChildren entries index values before first afterFirst)
    (right : RequireChildren entries index values before second afterSecond) :
    first = second ∧ afterFirst = afterSecond := stable_unique (children_stable left) (children_stable right)

/-- Successful node graphs and successful bounded executions describe exactly the same calls. -/
theorem node_execution_iff [DecidableEq (EdgeKey Symbol Guard)]
    (needed : Needed) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) :
    RequireNode needed value before result after ↔
      ∃ fuel readFuel, require fuel readFuel needed value before = .done result after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, stable⟩ := node_stable trace
    exact ⟨fuel, readFuel, stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, done⟩
    exact require_graph fuel readFuel needed value before result after done

/-- Child graphs and executions retain exactly the same selected original positions. -/
theorem children_execution_iff [DecidableEq (EdgeKey Symbol Guard)]
    (entries : List (Int × Needed)) (index : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : State Symbol Guard) :
    RequireChildren entries index values before results after ↔
      ∃ fuel readFuel, children (require fuel readFuel) entries index values before = .done results after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, stable⟩ := children_stable trace
    exact ⟨fuel, readFuel, stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, done⟩
    exact children_graph (require fuel readFuel) (require_graph fuel readFuel) entries index values before results after done

/-- Successful row graphs and executions retain exactly the same filtering and reconstruction. -/
theorem rows_execution_iff [DecidableEq (EdgeKey Symbol Guard)]
    (entries : List (Int × Needed)) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) :
    RequireRows entries edges before results after ↔
      ∃ fuel readFuel, rows (require fuel readFuel) entries edges before = .done results after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, stable⟩ := rows_stable trace
    exact ⟨fuel, readFuel, stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, done⟩
    exact rows_graph (require fuel readFuel) (require_graph fuel readFuel) entries edges before results after done

/-- Every complete closed input has finite stable execution and derived final cache invariants. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (needed : Needed)
    (value : Value Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (closed : value.free = []) :
    ∃ result after, RequireNode needed value before result after ∧ Keeps before after ∧ Available after result ∧
      result.free = [] ∧ StableRun (fun fuel readFuel => require fuel readFuel needed value before) result after := by
  obtain ⟨result, after, trace, keeps, resident, resultClosed⟩ :=
    SourceEqualityRequiredComplete.complete needed value before ready available closed
  exact ⟨result, after, trace, keeps, resident, resultClosed, node_stable trace⟩

/-- The source entry compiles Needed and applies it to the original child list. -/
def requireAll [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (paths : List Path)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) : Result Symbol Guard (List (Value Symbol Guard)) :=
  match build paths with
  | .node entries => children (require fuel readFuel) entries 0 values before

/-- An empty child map preserves every value without invoking its callback. -/
theorem children_empty_map
    (recur : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (index : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard) :
    children recur [] index values before = .done values before := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih =>
      simp only [SourceEqualityRequiredWorker.children, SourceEqualityNeededMap.lookup, ih (index + 1), Result.bind]

/-- Empty source path sets preserve even unresolved children at zero proof bounds. -/
theorem requireAll_identity [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) :
    requireAll fuel readFuel [] values before = .done values before := by
  exact children_empty_map (require fuel readFuel) 0 values before

/-- The compiled source entry has exactly the graph of its actual Needed child map. -/
theorem requireAll_execution_iff [DecidableEq (EdgeKey Symbol Guard)] (paths : List Path)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : State Symbol Guard) :
    (match build paths with | .node entries => RequireChildren entries 0 values before results after) ↔
      ∃ fuel readFuel, requireAll fuel readFuel paths values before = .done results after := by
  cases compiled : build paths with
  | node entries =>
      simpa only [requireAll, compiled] using children_execution_iff entries 0 values before results after

/-- The complete compiled child-list worker derives every callback completion premise. -/
theorem requireAll_complete [DecidableEq (EdgeKey Symbol Guard)] (paths : List Path)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (ready : Ready before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ results after, Keeps before after ∧ Values after results ∧ ClosedValues results ∧
      StableRun (fun fuel readFuel => requireAll fuel readFuel paths values before) results after := by
  cases compiled : build paths with
  | node entries =>
      have callbacks : SourceEqualityRequiredListsComplete.ChildComplete (Symbol := Symbol) (Guard := Guard) entries := by
        intro index needed member value current currentReady inputAvailable inputClosed
        exact SourceEqualityRequiredComplete.complete needed value current currentReady inputAvailable inputClosed
      obtain ⟨results, after, trace, keeps, resultAvailable, resultClosed⟩ :=
        SourceEqualityRequiredListsComplete.children_complete entries callbacks 0 values before ready available closed
      refine ⟨results, after, keeps, resultAvailable, resultClosed, ?_⟩
      simpa only [requireAll, compiled] using children_stable trace

/-- Original source construction derives the initial cache and a complete stable required-node run. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard) (needed : Needed) :
    ∃ value state result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      Keeps state after ∧ Available after result ∧ result.free = [] ∧
      StableRun (fun fuel readFuel => require fuel readFuel needed value state) result after := by
  obtain ⟨value, state, result, after, built, trace, keeps, resident, closed⟩ := SourceEqualityRequiredComplete.source expression needed
  exact ⟨value, state, result, after, built, keeps, resident, closed, node_stable trace⟩

end MicroCFTA.SourceEqualityRequiredExecution
