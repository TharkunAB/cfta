import MicroCFTA.SourceCurrentClassGuardAlphabet
import MicroCFTA.SourceCurrentActualClassSemanticReads
import MicroCFTA.SourceCurrentClassCallerNumeric
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.InternedFreshOrdinaryStoredCosts
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.EndpointMemoGateSource

set_option linter.all true
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ClassGuardKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok value => value
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocated.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocation : allocated = (.ok field, allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) cached allocation
private theorem constructed : built = .done value heap := by
  obtain ⟨result, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, value, heap, done, InternedNestedConstruction.Outcome.state]
private theorem initial (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) ∧
    Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  apply SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid expression
    (fun original member => by simpa only [expression, SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards,
      List.nil_append, List.append_nil] using member) value heap constructed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap, built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (initial 0).1.good.native.machine.1 value value
    (initial 0).2.2.2 (initial 0).2.2.2 (initial 0).2.1 (initial 0).2.1 (initial 0).2.2.1 (initial 0).2.2.1
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits (width : Nat) : Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial width).1.good.native.machine.1⟩

private theorem no_cap (depth : Nat) : ¬Cap depth value := by
  intro bounded
  cbv at bounded
  cases bounded with
  | plain _ annotated =>
      cases annotated with
      | mu _ _ _ _ body =>
          cases body with
          | node _ _ _ _ annotations _ =>
              have rejected := annotations _ List.mem_cons_self
              change SourceMemoGate.plain annotation = true at rejected
              have invalid : SourceMemoGate.plain annotation = false := by cbv
              rw [invalid] at rejected
              cases rejected

private theorem initial_frame (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (before (bits + 2)) :=
  Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl

private def values : List (Value Symbol Guard) := [value, value, .reference .depth]
private def classes : EqualityNormalize.Constraints := [[[7], [8]], [[7], [8]]]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem available_values (width : Nat) : InternedNestedProvenance.Values heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (initial width).2.1
  · exact (initial width).2.1
  · exact InternedNestedProvenance.depth_available _
private theorem proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [] := by
  intro paths member path included
  have same : paths = [[7], [8]] := by
    simpa only [classes, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst paths
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl <;> decide
private theorem active : ∀ paths ∈ classes, EqualityNormalize.Nontrivial paths := by
  intro paths member
  have same : paths = [[7], [8]] := by
    simpa only [classes, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst paths
  exact ⟨[7], by simp, [8], by simp, by decide⟩
private theorem context (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory (caller width) EndpointMemoGateTrace.empty := by
  have frame : Frame formulas solver inventory (before width) :=
    Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl
  exact ⟨(initial width).1, frame.admitted,
    SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver (before width)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty,
    SourceCurrentMemoMergeEffects.stored_empty heap,
    (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty
      (SourceEqualityPCSGuard.holds formulas solver) ambient),
    SourceCurrentEmptinessMemo.empty_correct formulas solver heap, EndpointMemoGateTrace.empty_valid heap,
    SourceCurrentAllocatedMuRebuild.constructed expression value heap constructed⟩

private theorem power_large (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.add_assoc, Nat.pow_succ]
      omega

private theorem exists_room (p : SourceCurrentAllocatedNativeResourceForecast.Profile) :
    ∃ bits, SourceCurrentAllocatedNativeResourceForecast.Room bits p := by
  let total := p.nodes + p.edges + p.domains + 2 ^ (p.nodes + p.nodes * p.nodes)
  refine ⟨total + 1, ?_⟩
  have large := power_large total
  have one := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 1 by omega)
  have two := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 2 by omega)
  change p.nodes < 2 ^ (total + 1) ∧ p.edges ≤ 2 ^ (total + 1 + 2) ∧
    p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) < 2 ^ (total + 1 + 1)
  have nodes : p.nodes ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right p.nodes p.edges)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have edges : p.edges ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_left p.edges p.nodes)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have domains : p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) ≤ total :=
    Nat.add_le_add_right (Nat.le_add_left p.domains (p.nodes + p.edges)) _
  exact ⟨Nat.lt_of_le_of_lt nodes large,
    Nat.le_trans edges (Nat.le_trans (Nat.le_of_lt large) two),
    Nat.lt_of_le_of_lt domains (Nat.lt_of_lt_of_le large one)⟩



private def record : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[0,0],[0,1]] with
  | some result => result
  | none => ⟨.empty, []⟩
private theorem record_built : SourceEqualityClassOrder.recordOf [[0,0],[0,1]] = some record := by cbv
private theorem record_paths : record.paths = [[0,0],[0,1]] := by cbv
private theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨other, built, coherent, _paths⟩ := SourceEqualityClassOrder.recordOf_complete [[0,0],[0,1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0,.branch [(0,.terminal),(1,.terminal)])], by cbv⟩)
  have same : other = record := Option.some.inj (built.symm.trans record_built)
  exact same ▸ coherent
private theorem record_active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0,0], by simp, [0,1], by simp, by decide⟩
private theorem selected_domains : ∀ path ∈ record.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values := by
  intro path member
  rw [record_paths] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    intro selected found
    change some value = some selected at found
    have same := Option.some.inj found
    subst selected
    change value.free = []
    exact (initial 0).2.2.1
private def records := [record, record]
private theorem records_coherent : ∀ own ∈ records, SourceEqualityClassOrder.Coherent own := by
  intro own member
  have same : own = record := by simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ record_coherent
private theorem records_active : ∀ own ∈ records, EqualityNormalize.Nontrivial own.paths := by
  intro own member
  have same : own = record := by simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ record_active
private theorem records_domains : ∀ own ∈ records, ∀ path ∈ own.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values := by
  intro own member
  have same : own = record := by simpa only [records, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  exact same ▸ selected_domains
private theorem forest_open : ¬MergedColdReaderClosedInputs.ClosedValues values := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [values])
  cases impossible


private def alphabet := SourceCurrentConjunctionGuardUniverse.guards heap

private theorem witness (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    record.paths = [[0,0],[0,1]] ∧
    ∃ bits results after saved next final,
      ∃ actual : SourceCurrentAllocatedClassPass.Pass records values (before (bits+2))
          SourceCurrentMemoMergeGraph.empty results after saved,
        SourceCurrentAllocatedClassPass.PassReads formulas solver actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedClassPass.Receipt formulas solver next records values (before (bits+2))
          SourceCurrentMemoMergeGraph.empty results after saved EndpointMemoGateTrace.empty final ∧
        Frame formulas solver next after ∧
        Fits (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile) after ∧
        SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ SourceCurrentNativeGuardAlphabet.advance alphabet
          (SourceCurrentClassGuardAlphabet.foldCount records values.length profile)) after.native.machine.heap ∧
        results.length = values.length ∧
        SourceCurrentAllocatedClassWorker.pass
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 1)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 2)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 3)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 4)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 5)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 6)
          records values (before (bits+2)) SourceCurrentMemoMergeGraph.empty = .done results after saved := by
  obtain ⟨bits,room⟩ := exists_room (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile)
  have known := SourceCurrentConjunctionGuardUniverse.initial heap (initial (bits+2)).1.good.native.machine.1
  have reserved : SourceCurrentConstrainedCapClassForecast.Reserved bits records values.length profile := room
  obtain ⟨results,after,saved,next,final,actual,reads,receipt,returned,numeric,carrier,length,_done,stable⟩ :=
    SourceCurrentClassGuardAlphabet.pass alphabet formulas solver inventory records records_coherent records_active
      values (before (bits+2)) SourceCurrentMemoMergeGraph.empty profile (initial_frame bits formulas solver)
      (initial_fits (bits+2)) (available_values (bits+2)) records_domains
      (SourceCurrentMemoMergeEffects.stored_empty heap)
      (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty
        (SourceEqualityPCSGuard.holds formulas solver) ambient)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) reserved known
  exact ⟨no_cap,forest_open,record_paths,bits,results,after,saved,next,final,actual,reads,receipt,returned,numeric,carrier,length,
    stable _ _ _ _ _ _ (Nat.le_add_right _ 1) (Nat.le_add_right _ 2) (Nat.le_add_right _ 3)
      (Nat.le_add_right _ 4) (Nat.le_add_right _ 5) (Nat.le_add_right _ 6)⟩

/-- Repeated initial classes construct their full guard-bounded pass with an open unselected sibling. -/
theorem repeated_recursive_pass (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    record.paths = [[0,0],[0,1]] ∧
    ∃ bits results after saved next final,
      ∃ actual : SourceCurrentAllocatedClassPass.Pass records values (before (bits+2))
          SourceCurrentMemoMergeGraph.empty results after saved,
        SourceCurrentAllocatedClassPass.PassReads formulas solver actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedClassPass.Receipt formulas solver next records values (before (bits+2))
          SourceCurrentMemoMergeGraph.empty results after saved EndpointMemoGateTrace.empty final ∧
        Frame formulas solver next after ∧
        Fits (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile) after ∧
        SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ SourceCurrentNativeGuardAlphabet.advance alphabet
          (SourceCurrentClassGuardAlphabet.foldCount records values.length profile)) after.native.machine.heap ∧
        results.length = values.length ∧
        SourceCurrentAllocatedClassWorker.pass
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 1)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 2)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 3)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 4)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 5)
          (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile + 6)
          records values (before (bits+2)) SourceCurrentMemoMergeGraph.empty = .done results after saved :=
  witness formulas solver

end MicroCFTA.ClassGuardKernels
