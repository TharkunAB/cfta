import MicroCFTA.SourceFreshOrdinaryNativeKeyExecution
import MicroCFTA.SourceShortCircuitScan

/-!
# Actual short-circuit child scans on finite source keys

Each reached child pair executes the complete native callback. The scan
passes its actual cache to the next pair and stops after false. Input-table
metadata derives every operand language. Reached-query word checks remain
explicit; no native completion or product-language premise is supplied.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeKeyScan
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)
open SourceFreshOrdinaryColdKeys (physical)

/-- Actual native callback execution for one ordered pair of source keys. -/
def Step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (encode : Key → SourceInternedRows.State) (pair : Key × Key)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (result : Bool)
    (after : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  SourceFreshOrdinaryNativeCallback.Execution emptyGuard conjoin
    (physical source (encode pair.1)) (physical source (encode pair.2)) state result after

/-- Check the native words at the current actual child query. -/
def Allowed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (encode : Key → SourceInternedRows.State) (pair : Key × Key)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
    (.node ⟨IntersectionEmptyDomain.emptyDomain, physical source (encode pair.1), physical source (encode pair.2)⟩ .pure) state

/-- Actual later query caches retain ready native state and the original input heap. -/
def Invariant [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state ∧
    Grows source state.machine.heap ∧ Extends source.nodes.issued state.machine.heap.nodes.issued

/-- Actual edge overlap rejects a different symbol or arity before any native child callback. -/
inductive EdgeExecution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (encode : Key → SourceInternedRows.State) :
    (Edge Key Symbol × Edge Key Symbol) → SourceRecursiveIntersectionThunks.State width Symbol Guard → Bool →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | reject (first second : Edge Key Symbol) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
      (different : first.label ≠ second.label ∨ first.children.length ≠ second.children.length) :
      EdgeExecution emptyGuard conjoin source encode (first, second) state false state
  | children (first second : Edge Key Symbol) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (result : Bool)
      (symbols : first.label = second.label) (arity : first.children.length = second.children.length)
      (execution : SourceShortCircuitScan.Run true (Step emptyGuard conjoin source encode)
        (first.children.zip second.children) state result after) :
      EdgeExecution emptyGuard conjoin source encode (first, second) state result after

/-- Only matching edge pairs require the reached child-query word checks. -/
def EdgeAllowed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (encode : Key → SourceInternedRows.State) (pair : Edge Key Symbol × Edge Key Symbol)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  if pair.1.label = pair.2.label ∧ pair.1.children.length = pair.2.children.length then
    SourceShortCircuitScan.Ranges true (Step emptyGuard conjoin source encode) (Allowed emptyGuard conjoin source encode)
      (pair.1.children.zip pair.2.children) state
  else True

/-- The source tails comprehension visits every later edge in its original order. -/
def edgePairs : List (Edge Key Symbol) → List (Edge Key Symbol × Edge Key Symbol)
  | [] => []
  | first :: rest => rest.map (fun second => (first, second)) ++ edgePairs rest

/-- Flattening the ordered tails comprehension preserves the source ambiguity Boolean. -/
theorem ambiguous_pairs [DecidableEq Symbol] (test : Key → Key → Bool) (edges : List (Edge Key Symbol)) :
    AutomatonAmbiguity.ambiguous test edges =
      (edgePairs edges).any (fun pair => AutomatonAmbiguity.overlapping test pair.1 pair.2) := by
  induction edges with
  | nil => rfl
  | cons first rest ih =>
      simp only [AutomatonAmbiguity.ambiguous, edgePairs, List.any_append, List.any_map, ih, Function.comp_def]

/-- The actual all-row ambiguity scan visits rows and their edge pairs in source order. -/
def edgeQueries (states : List Key) (rows : Key → List (Edge Key Symbol)) : List (Edge Key Symbol × Edge Key Symbol) :=
  states.flatMap fun state => edgePairs (rows state)

/-- Flattening row scans preserves the complete ordered reference ambiguity result. -/
theorem query_reference [DecidableEq Symbol] (test : Key → Key → Bool) (states : List Key) (rows : Key → List (Edge Key Symbol)) :
    (edgeQueries states rows).any (fun pair => AutomatonAmbiguity.overlapping test pair.1 pair.2) =
      states.any (fun state => AutomatonAmbiguity.ambiguous test (rows state)) := by
  simp only [edgeQueries, List.any_flatMap, ← ambiguous_pairs]

section Input
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SemanticHeap source) (covered : Covered [] source)
    (guarded : InternedGuardedProbeHeap.Heap source) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source)
    (rows : Rows Symbol Guard) (replayed : ReplayedRows source rows)
    (resident : ResidentRows source rows) (closedRows : CoveredRows rows rows)
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (root : Value Symbol Guard) (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys root))

local notation "raw" => SourceColdSharedRows.table rows keys root
local notation "K" => SourceDenseRows.Member (SourceDenseRows.keys raw)
local notation "A" => SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true)
local notation "test" => fun pair : K × K => AutomatonAmbiguity.productiveRows (Language.intersect A A)
  (SourceCyclicRows.pairs (SourceDenseRows.keys raw)) (SourceCyclicRows.pairs_complete _) pair

include semantic covered guarded budgetHeap replayed resident closedRows domain

/-- Actual input metadata derives finite exact child callbacks and retains the shared input cache invariant. -/
theorem callback (pair : K × K) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : Invariant emptyGuard conjoin source state) (allowed : Allowed emptyGuard conjoin source Subtype.val pair state) :
    ∃ result after, Step emptyGuard conjoin source Subtype.val pair state result after ∧
      Invariant emptyGuard conjoin source after ∧ result = test pair := by
  obtain ⟨result, after, execution, retained, extension, exact⟩ :=
    SourceFreshOrdinaryNativeKeyCallback.complete_keys emptyGuard conjoin source semantic covered guarded budgetHeap
      rows replayed resident closedRows keys domain root closed state valid.1 valid.2.1 valid.2.2 pair.1 pair.2 allowed
  exact ⟨result, after, execution,
    ⟨retained, grows_trans valid.2.1 extension.heap, extends_trans valid.2.2 extension.history⟩, exact⟩

/-- Every actual completed child callback has the finite reference test and retains the next-query invariant. -/
theorem callback_correct (pair : K × K) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : Invariant emptyGuard conjoin source state) (allowed : Allowed emptyGuard conjoin source Subtype.val pair state)
    (result : Bool) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (execution : Step emptyGuard conjoin source Subtype.val pair state result after) :
    Invariant emptyGuard conjoin source after ∧ result = test pair := by
  obtain ⟨expected, final, actual, retained, exact⟩ := callback emptyGuard conjoin source semantic covered guarded budgetHeap
    rows replayed resident closedRows keys domain root closed pair state valid allowed
  obtain ⟨rfl, rfl⟩ := execution.unique actual
  exact ⟨retained, exact⟩

/-- The actual ordered zip-and child scan completes and equals the reference child-overlap Boolean. -/
theorem children_complete (left right : List K) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : Invariant emptyGuard conjoin source state)
    (ranges : SourceShortCircuitScan.Ranges true (Step emptyGuard conjoin source Subtype.val)
      (Allowed emptyGuard conjoin source Subtype.val) (left.zip right) state) :
    ∃ result after, SourceShortCircuitScan.Run true (Step emptyGuard conjoin source Subtype.val) (left.zip right) state result after ∧
      Invariant emptyGuard conjoin source after ∧ result = AutomatonAmbiguity.childOverlap (fun first second => test (first, second)) left right := by
  obtain ⟨result, after, execution, retained, exact⟩ :=
    SourceShortCircuitScan.complete true (Step emptyGuard conjoin source Subtype.val) (Allowed emptyGuard conjoin source Subtype.val)
      (Invariant emptyGuard conjoin source) test
      (callback emptyGuard conjoin source semantic covered guarded budgetHeap rows replayed resident closedRows keys domain root closed)
      (left.zip right) state valid ranges
  refine ⟨result, after, execution, retained, ?_⟩
  simpa only [SourceShortCircuitScan.fold_all, AutomatonAmbiguity.childOverlap, List.all_map, Function.comp_def, id_eq, Prod.eta] using exact

/-- Any actual completed child scan has the reference Boolean and retains the actual subsequent cache. -/
theorem children_correct (left right : List K) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : Invariant emptyGuard conjoin source state)
    (ranges : SourceShortCircuitScan.Ranges true (Step emptyGuard conjoin source Subtype.val)
      (Allowed emptyGuard conjoin source Subtype.val) (left.zip right) state)
    (result : Bool) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (execution : SourceShortCircuitScan.Run true (Step emptyGuard conjoin source Subtype.val) (left.zip right) state result after) :
    Invariant emptyGuard conjoin source after ∧ result = AutomatonAmbiguity.childOverlap (fun first second => test (first, second)) left right := by
  have exact := SourceShortCircuitScan.Run.correct true (Step emptyGuard conjoin source Subtype.val) (Allowed emptyGuard conjoin source Subtype.val)
    (Invariant emptyGuard conjoin source) test
    (callback_correct emptyGuard conjoin source semantic covered guarded budgetHeap rows replayed resident closedRows keys domain root closed)
    execution valid ranges
  simpa only [SourceShortCircuitScan.fold_all, AutomatonAmbiguity.childOverlap, List.all_map, Function.comp_def, id_eq, Prod.eta] using exact

/-- Every matching edge pair has a finite actual child scan; mismatches perform no callback. -/
theorem edge_complete (pair : Edge K Symbol × Edge K Symbol) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : Invariant emptyGuard conjoin source state) (ranges : EdgeAllowed emptyGuard conjoin source Subtype.val pair state) :
    ∃ result after, EdgeExecution emptyGuard conjoin source Subtype.val pair state result after ∧
      Invariant emptyGuard conjoin source after ∧
      result = AutomatonAmbiguity.overlapping (fun first second => test (first, second)) pair.1 pair.2 := by
  by_cases same : pair.1.label = pair.2.label ∧ pair.1.children.length = pair.2.children.length
  · have childRanges := by simpa only [EdgeAllowed, same, ↓reduceIte] using ranges
    obtain ⟨result, after, execution, retained, exact⟩ := children_complete emptyGuard conjoin source semantic covered guarded budgetHeap
      rows replayed resident closedRows keys domain root closed pair.1.children pair.2.children state valid childRanges
    refine ⟨result, after, .children pair.1 pair.2 state after result same.1 same.2 execution, retained, ?_⟩
    simpa only [AutomatonAmbiguity.overlapping, same.1, same.2, decide_true, Bool.true_and] using exact
  · have different : pair.1.label ≠ pair.2.label ∨ pair.1.children.length ≠ pair.2.children.length := by
      by_cases symbols : pair.1.label = pair.2.label
      · exact Or.inr (fun arity => same ⟨symbols, arity⟩)
      · exact Or.inl symbols
    refine ⟨false, state, .reject pair.1 pair.2 state different, valid, ?_⟩
    rcases different with symbols | arity <;> simp [AutomatonAmbiguity.overlapping, *]

/-- Any actual completed edge scan retains its precise source Boolean and subsequent cache. -/
theorem edge_correct (pair : Edge K Symbol × Edge K Symbol) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : Invariant emptyGuard conjoin source state) (ranges : EdgeAllowed emptyGuard conjoin source Subtype.val pair state)
    (result : Bool) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (execution : EdgeExecution emptyGuard conjoin source Subtype.val pair state result after) :
    Invariant emptyGuard conjoin source after ∧
      result = AutomatonAmbiguity.overlapping (fun first second => test (first, second)) pair.1 pair.2 := by
  cases execution with
  | reject first second state different =>
      refine ⟨valid, ?_⟩
      rcases different with symbols | arity <;> simp [AutomatonAmbiguity.overlapping, *]
  | children first second state after result symbols arity execution =>
      have childRanges := by simpa [EdgeAllowed, symbols, arity] using ranges
      obtain ⟨retained, exact⟩ := children_correct emptyGuard conjoin source semantic covered guarded budgetHeap
        rows replayed resident closedRows keys domain root closed first.children second.children state valid childRanges result after execution
      refine ⟨retained, ?_⟩
      simpa only [AutomatonAmbiguity.overlapping, symbols, arity, decide_true, Bool.true_and] using exact

/-- The full actual row and edge-pair scan has finite execution and the literal reference ambiguity Boolean. -/
theorem scan_complete (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : Invariant emptyGuard conjoin source state)
    (ranges : SourceShortCircuitScan.Ranges false (EdgeExecution emptyGuard conjoin source Subtype.val)
      (EdgeAllowed emptyGuard conjoin source Subtype.val) (edgeQueries (SourceDenseRows.keys raw).attach A) state) :
    ∃ result after, SourceShortCircuitScan.Run false (EdgeExecution emptyGuard conjoin source Subtype.val)
      (edgeQueries (SourceDenseRows.keys raw).attach A) state result after ∧
      Invariant emptyGuard conjoin source after ∧
      result = (SourceDenseRows.keys raw).attach.any (fun key =>
        AutomatonAmbiguity.ambiguous (fun first second => test (first, second)) (A key)) := by
  obtain ⟨result, after, execution, retained, exact⟩ :=
    SourceShortCircuitScan.complete false (EdgeExecution emptyGuard conjoin source Subtype.val)
      (EdgeAllowed emptyGuard conjoin source Subtype.val) (Invariant emptyGuard conjoin source)
      (fun pair => AutomatonAmbiguity.overlapping (fun first second => test (first, second)) pair.1 pair.2)
      (edge_complete emptyGuard conjoin source semantic covered guarded budgetHeap rows replayed resident closedRows keys domain root closed)
      (edgeQueries (SourceDenseRows.keys raw).attach A) state valid ranges
  refine ⟨result, after, execution, retained, ?_⟩
  simpa only [SourceShortCircuitScan.fold_any, query_reference] using exact

/-- Every actual completed all-row scan has the reference result and retains the exact next native cache invariant. -/
theorem scan_correct (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : Invariant emptyGuard conjoin source state)
    (ranges : SourceShortCircuitScan.Ranges false (EdgeExecution emptyGuard conjoin source Subtype.val)
      (EdgeAllowed emptyGuard conjoin source Subtype.val) (edgeQueries (SourceDenseRows.keys raw).attach A) state)
    (result : Bool) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (execution : SourceShortCircuitScan.Run false (EdgeExecution emptyGuard conjoin source Subtype.val)
      (edgeQueries (SourceDenseRows.keys raw).attach A) state result after) :
    Invariant emptyGuard conjoin source after ∧
      result = (SourceDenseRows.keys raw).attach.any (fun key =>
        AutomatonAmbiguity.ambiguous (fun first second => test (first, second)) (A key)) := by
  have exact := SourceShortCircuitScan.Run.correct false (EdgeExecution emptyGuard conjoin source Subtype.val)
    (EdgeAllowed emptyGuard conjoin source Subtype.val) (Invariant emptyGuard conjoin source)
    (fun pair => AutomatonAmbiguity.overlapping (fun first second => test (first, second)) pair.1 pair.2)
    (edge_correct emptyGuard conjoin source semantic covered guarded budgetHeap rows replayed resident closedRows keys domain root closed)
    execution valid ranges
  simpa only [SourceShortCircuitScan.fold_any, query_reference] using exact

end Input
end MicroCFTA.SourceFreshOrdinaryNativeKeyScan
