import MicroCFTA.SourceCurrentEditListNumeric
import MicroCFTA.SourceCurrentAllocatedClassEditPlan
import MicroCFTA.SourceCurrentConjunctionRequiredActual
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.InternedFreshOrdinaryStoredCosts
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.EndpointMemoGateSource

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.EditUncappedKernels
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
  .node [.mk ("roots", .top) annotation [
    .node [.mk ("finite", .top) annotation [.node [.mk ("left", .top) annotation []], .node [.mk ("right", .top) annotation []]]],
    .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def finite : Value Symbol Guard := ((children value)[0]?).getD .empty
private def recursive : Value Symbol Guard := ((children value)[1]?).getD .empty
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
    (fun original member => by simpa [expression, SourceEqualityConstraintOrigins.guards,
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

private theorem no_cap (depth : Nat) : ¬Cap depth recursive := by
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

private def values : List (Value Symbol Guard) := [finite, recursive, .reference .depth]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem available_values (width : Nat) : InternedNestedProvenance.Values heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (initial width).2.1.children finite (by cbv; exact .head _)
  · exact (initial width).2.1.children recursive (by cbv; exact .tail _ (.head _))
  · exact InternedNestedProvenance.depth_available _
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
private theorem open_values : ¬MergedColdReaderClosedInputs.ClosedValues values := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [values])
  cases impossible
private theorem no_forest_cap : ∀ depth, ¬(∀ child ∈ values, Cap depth child) := by
  intro depth bounded
  exact no_cap depth (bounded recursive (by simp [values]))

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
  match SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] with
  | some own => own
  | none => ⟨.empty, []⟩
private def records := [record]
private theorem record_built : SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] = some record := by cbv
private theorem record_paths : record.paths = [[0, 0], [0, 1]] := by cbv
private theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨own, built, coherent, _paths⟩ := SourceEqualityClassOrder.recordOf_complete [[0, 0], [0, 1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0, .branch [(0, .terminal), (1, .terminal)])], by cbv⟩)
  have same : own = record := Option.some.inj (built.symm.trans record_built)
  exact same ▸ coherent
private theorem proper : ∀ own ∈ records, ∀ path ∈ own.paths, path ≠ [] := by
  intro own member path included
  have same : own = record := List.mem_singleton.mp member
  subst own
  rw [record_paths] at included
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl <;> decide
private theorem coherent : ∀ own ∈ records, SourceEqualityClassOrder.Coherent own := by
  intro own member
  exact (List.mem_singleton.mp member) ▸ record_coherent
private theorem active : ∀ own ∈ records, EqualityNormalize.Nontrivial own.paths := by
  intro own member
  have same : own = record := List.mem_singleton.mp member
  subst own
  rw [record_paths]
  exact ⟨[0, 0], by simp, [0, 1], by simp, by decide⟩
private def edits := SourceCurrentAllocatedClassEditPlan.compiled record
private def start (width : Nat) := SourceCurrentAllocatedSharedTargetState.initial (before width) SourceCurrentMemoMergeGraph.empty
private theorem start_ready (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedSharedTargetState.Ready formulas solver inventory record values heap (start width) := by
  have frame := Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl
  exact SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values heap
    (before width) SourceCurrentMemoMergeGraph.empty (initial width).1 frame.admitted
    (SourceEqualityRequiredCache.pure_keeps heap (initial width).1.semantic.ready)
    (SourceCurrentMemoMergeEffects.stored_empty _) (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty
      (SourceEqualityPCSGuard.holds formulas solver) ambient)
private theorem domains : ∀ path ∈ record.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values := by
  intro path member
  rw [record_paths] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro child selected
    have same : child = finite := Option.some.inj selected.symm
    subst child
    exact SourceCurrentRequiredEndpoints.closed_path [0] finite heap (initial 0).1.semantic
      ((initial 0).2.1.children finite (by cbv; exact .head _)) (by cbv)
  · intro child selected
    have same : child = finite := Option.some.inj selected.symm
    subst child
    exact SourceCurrentRequiredEndpoints.closed_path [1] finite heap (initial 0).1.semantic
      ((initial 0).2.1.children finite (by cbv; exact .head _)) (by cbv)
private theorem safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values := by
  obtain ⟨entries, built⟩ := SourceCurrentAllocatedClassEditPlan.compiled_children record record_coherent (active record List.mem_cons_self)
  change SourceCurrentAllocatedSharedEditEffects.ListSafe (SourceCurrentAllocatedClassEditPlan.compiled record) values
  rw [built]
  exact SourceCurrentAllocatedClassEditPlan.compiled_safe record record_coherent values domains entries built
private noncomputable def finalProfile := SourceCurrentEditListNumeric.finalProfile record values.length edits values.length profile
private noncomputable def fuel := SourceCurrentEditListNumeric.fuel record values.length edits values.length profile

/-- A nonempty compiled edit constructs its own full execution beside uncapped and open captured siblings. -/
theorem constructed_nonempty
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬(∀ child ∈ values, Cap depth child)) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    SourceCurrentEditDomains.HasLeaf edits ∧
    ∃ bits results after next final,
      ∃ actual : SourceCurrentAllocatedSharedEditGraph.EditList record values edits values (start (bits + 2)) results after,
        SourceCurrentAllocatedSharedEditGraph.ListReads formulas solver heap actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record values heap values
          (start (bits + 2)) results after EndpointMemoGateTrace.empty final ∧
        Frame formulas solver next after.checked ∧ Fits finalProfile after.checked ∧
        results.length = values.length ∧
        SourceCurrentAllocatedSharedEditWorker.editList
          (SourceCurrentAllocatedSharedEditWorker.edit record values fuel fuel fuel fuel fuel fuel)
          edits values (start (bits + 2)) = .done results after := by
  have nonempty : SourceEqualityClassEdits.edits record.paths id ≠ [] := by
    rw [record_paths]
    decide
  have hasLeaf := SourceCurrentEditDomains.build_hasLeaf _ nonempty
  obtain ⟨bits, room⟩ := exists_room finalProfile
  have reserved : SourceCurrentEditListNumeric.Reserved bits record values.length edits values.length profile := by
    obtain ⟨entries, built⟩ := SourceCurrentAllocatedClassEditPlan.compiled_children record record_coherent (active record List.mem_cons_self)
    simpa only [SourceCurrentEditListNumeric.Reserved, edits, built] using (show SourceCurrentAllocatedNativeResourceForecast.Room bits (SourceCurrentEditListNumeric.finalProfile record values.length edits values.length profile) from room)
  obtain ⟨results, after, next, final, actual, reads, receipt, returned, numeric, done⟩ :=
    SourceCurrentEditListNumeric.complete formulas solver inventory record values heap (start (bits + 2)) profile
      (start_ready _ formulas solver) (initial_frame bits formulas solver) (initial_fits _) (available_values 0) domains
      record_coherent (active record List.mem_cons_self) edits (SourceCurrentAllocatedClassEditPlan.compiled_populated record)
      (SourceCurrentAllocatedClassEditPlan.compiled_allowed record) values (available_values 0) safe
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) reserved
  exact ⟨no_forest_cap, open_values, hasLeaf, bits, results, after, next, final, actual, reads, receipt,
    returned, numeric, (Language.All₂.length_eq receipt.transport).symm, done⟩

/-- An ignored list-root leaf preserves the uncapped open inputs and full shared state without Room. -/
theorem constructed_root_identity (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ final,
      ∃ actual : SourceCurrentAllocatedSharedEditGraph.EditList record values (.editAt [0, 0]) values
          (start (bits + 2)) values (start (bits + 2)),
        SourceCurrentAllocatedSharedEditGraph.ListReads formulas solver heap actual EndpointMemoGateTrace.empty final ∧
        Frame formulas solver inventory (start (bits + 2)).checked ∧
        Fits profile (start (bits + 2)).checked ∧
        SourceCurrentAllocatedSharedEditWorker.editList
          (SourceCurrentAllocatedSharedEditWorker.edit record values 0 0 0 0 0 0)
          (.editAt [0, 0]) values (start (bits + 2)) = .done values (start (bits + 2)) := by
  have allowed : SourceEqualitySharedEditEffects.Allowed record (.editAt [0, 0]) := by
    simp only [SourceEqualitySharedEditEffects.Allowed, SourceEqualityEdits.All]
    rw [record_paths]
    simp
  obtain ⟨results, after, next, final, actual, reads, _receipt, _returned, _numeric, done⟩ :=
    SourceCurrentEditListNumeric.complete formulas solver inventory record values heap (start (bits + 2)) profile
      (start_ready _ formulas solver) (initial_frame bits formulas solver) (initial_fits _) (available_values 0) domains
      record_coherent (active record List.mem_cons_self) (.editAt [0, 0]) (by simp only [SourceCurrentEditDomains.Populated]) allowed values (available_values 0) trivial
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) trivial
  cases actual
  exact ⟨final, .leaf, reads, initial_frame bits formulas solver, initial_fits _, done⟩

end MicroCFTA.EditUncappedKernels

#print axioms MicroCFTA.EditUncappedKernels.constructed_nonempty
#check @MicroCFTA.EditUncappedKernels.constructed_nonempty
#print MicroCFTA.EditUncappedKernels.constructed_nonempty
#print axioms MicroCFTA.EditUncappedKernels.constructed_root_identity
#check @MicroCFTA.EditUncappedKernels.constructed_root_identity
#print MicroCFTA.EditUncappedKernels.constructed_root_identity
