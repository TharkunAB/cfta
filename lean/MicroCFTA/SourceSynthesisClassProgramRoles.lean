import MicroCFTA.SourceCurrentActualClassRowOrigins
import MicroCFTA.SourceSynthesisRequiredProgramRoles
import MicroCFTA.SourceSynthesisSelectedProgramFootprints

/-!
# Program roles through one actual class edit

This certificate proves successful-call preservation. It does not prove worker
completion, failure-prefix roles, Type progress, or a whole-driver bound.
The internal footprint premise is derived below from actual source guards,
the precheck receipt, and retained selection. No final role supplier is added.
-/
namespace MicroCFTA.SourceSynthesisClassProgramRoles
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits
open SourceCurrentLowerOperationInvariants (Effect SharedGood)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
open SourceSynthesisGeneralizeSyntax (Guard)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Worker" => SourceCurrentAllocatedSharedEditWorker.edit
variable {width : Nat} {literal : String → Symbol}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem bind_done {A B : Type}
    (first : SourceCurrentAllocatedSharedEditWorker.Outcome width A)
    (next : A → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width B)
    {value : B} {after : Shared width} (done : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result, middle, rfl, done⟩
  | failed => cases done

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem shared_advance {before : Shared width} (good : SharedGood before)
    {checked : Checked width} (effect : Effect before.checked checked) :
    SharedGood (SourceCurrentAllocatedSharedTargetState.advance before checked) :=
  ⟨effect.good, good.stored.grows effect.keeps,
    fun path value stored => effect.keeps.available value (good.slots path value stored)⟩

omit [DecidableEq Symbol] in
private theorem edge_frame {before : Checked width}
    (good : SourceCurrentNativeOperationHeap.Good before) (symbol : Symbol) (guard : Guard) (values : List Node)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations guard)
    (available : Values before.native.machine.heap values) :
    Effect before (SourceCurrentAllocatedQueryMemo.advancePhysical before
      ⟨(run (makeEdge symbol guard values) before.native.machine.heap).2, before.operations⟩) ∧
    EdgeResident (run (makeEdge symbol guard values) before.native.machine.heap).2
      (run (makeEdge symbol guard values) before.native.machine.heap).1 := by
  have cache := SourceEqualityRequiredCache.edge symbol guard values _ good.heap available
  have semantic := SourceEqualityRequiredSemanticCache.edge symbol guard values _ good.semantic available
  have fields := SourceEqualityAnnotationHeap.run (SourceCurrentConjunctionEquality.FieldAvailable before.operations)
    _ (SourceEqualityAnnotationHeap.makeEdge _ symbol guard values field) _ good.fields
  have effect : SourceCurrentConjunctionRowsAllocation.Effects
      (SourceCurrentAllocatedNativeEffects.physical before)
      ⟨(run (makeEdge symbol guard values) before.native.machine.heap).2, before.operations⟩ :=
    ⟨cache.1, ⟨semantic, good.costs, good.operations, fields⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  exact ⟨⟨good.advance _ effect, cache.1, effect.grows⟩, cache.2.1⟩

private theorem rows_frame {record originals e p h m s n entries rows before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.rows (Worker record originals e p h m s n)
      entries rows before = .done results after)
    (good : SharedGood (width := width) before)
    (originalsAvailable : Values before.checked.native.machine.heap originals)
    (resident : Edges before.checked.native.machine.heap rows) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Edges after.checked.native.machine.heap results := by
  induction rows generalizing before results after with
  | nil => cases actual; exact ⟨.refl _ good.checked, good, by simp [Edges]⟩
  | cons edge rows ih =>
      obtain ⟨values, middle, children, later⟩ := bind_done _ _ actual
      have childCall : SourceCurrentAllocatedSharedEditWorker.editList (Worker record originals e p h m s n)
          (.editBelow entries) edge.children before = .done values middle := children
      have childInputs := good.checked.heap.semantic.1.normal.facts.cached.edges _ _
        (resident _ List.mem_cons_self)
      obtain ⟨first, current, known⟩ := SourceCurrentLowerOperationInvariants.edit_list
        childCall good originalsAvailable childInputs
      obtain ⟨rebuilt, afterEdge, built, later⟩ := bind_done _ _ later
      have field := (good.checked.fields _ _ (resident _ List.mem_cons_self)).grows first.operations
      have edgeEffects := edge_frame current.checked edge.entry.key.symbol edge.entry.key.constraint values field known
      simp only [SourceCurrentAllocatedSharedEditWorker.work] at built
      cases built
      obtain ⟨tail, final, rest, returned⟩ := bind_done _ _ later
      cases returned
      have prefixEffect := first.trans edgeEffects.1
      obtain ⟨lastEffect, finalGood, tailKnown⟩ := ih rest (shared_advance current edgeEffects.1)
        (fun value member => prefixEffect.keeps.available value (originalsAvailable value member))
        (fun row member => edge_grows _ _ prefixEffect.keeps.growth row
          (resident row (List.mem_cons_of_mem _ member)))
      refine ⟨prefixEffect.trans lastEffect, finalGood, ?_⟩
      intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact edge_grows _ _ lastEffect.keeps.growth _ edgeEffects.2
      · exact tailKnown output member

omit [DecidableEq Symbol] in
private theorem head_frame {fuel input before output after}
    (actual : SourceCurrentAllocatedSharedEditWorker.head fuel input before = .done output after)
    (good : SharedGood (width := width) before) (available : Available before.checked.native.machine.heap input)
    (role : ProgramValue literal input) :
    Effect before.checked after.checked ∧ SharedGood after ∧
      Available after.checked.native.machine.heap output ∧ ProgramValue literal output := by
  cases read : SourceEqualityRequiredWorker.head fuel input before.checked.native.machine.heap with
  | pending | unresolved | exhausted =>
      simp only [SourceCurrentAllocatedSharedEditWorker.head, read] at actual
      cases actual
  | done value heap =>
      simp only [SourceCurrentAllocatedSharedEditWorker.head, read] at actual
      cases actual
      have graph := SourceEqualityRequiredWorkerSound.head_graph fuel input _ _ heap read
      obtain ⟨keeps, semantic, costs, fields, known⟩ := SourceCurrentRequiredHeapEffects.head
        (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations) graph
        good.checked.semantic good.checked.costs good.checked.fields available
      have effect : SourceCurrentConjunctionRowsAllocation.Effects
          (SourceCurrentAllocatedNativeEffects.physical before.checked) ⟨heap, before.checked.operations⟩ :=
        ⟨keeps, ⟨semantic, costs, good.checked.operations, fields⟩,
          SourceEqualityConstraintMemoAllocation.grows_refl _⟩
      have checked : Effect before.checked
          (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩) :=
        ⟨good.checked.advance _ effect, keeps, effect.grows⟩
      exact ⟨checked, shared_advance good checked, known,
        SourceSynthesisRequiredProgramRoles.head_roles graph good.checked.semantic good.checked.costs available role⟩

/-- Annotation-only below edits retain complete Program roles, including Top rows. -/
theorem below_roles {record originals e p h m s n entries input before output after}
    (actual : Worker record originals e p h m s n (.editBelow entries) input before = .done output after)
    (good : SharedGood (width := width) before)
    (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap input)
    (role : ProgramValue literal input)
    (annotationOnly : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    ProgramValue literal output := by
  induction e generalizing input before output after with
  | zero => cases actual
  | succ e ih =>
      cases input with
      | empty => cases actual; exact .empty
      | reference | mu => cases role
      | node entry rows depth free =>
          have rowRoles : ∀ edge ∈ rows, ProgramEdge literal edge := by cases role; assumption
          obtain ⟨rebuilt, middle, first, last⟩ := bind_done _ _ actual
          have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ available.resident
          obtain ⟨_effect, current, known⟩ := rows_frame first good originalsAvailable resident
          have rebuiltRoles : ∀ edge ∈ rebuilt, ProgramEdge literal edge := by
            intro edge member
            obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
            obtain ⟨original, found, origin, unchanged⟩ :=
              SourceCurrentActualEditRowOrigins.rows_indexed first good originalsAvailable resident index selected
            exact SourceSynthesisRequiredProgramRoles.rebuild_roles
              (rowRoles original (List.mem_of_getElem? found)) origin
              (fun index nonzero => unchanged index (annotationOnly index nonzero))
          simp only [SourceCurrentAllocatedSharedEditWorker.work] at last
          cases last
          exact SourceSynthesisProgramBuildRolesGeneric.makeNode_roles literal rebuilt _
            current.checked.heap.semantic.1.normal.facts known rebuiltRoles
      | union entry members depth free =>
          obtain ⟨exposed, middle, first, last⟩ := bind_done _ _ actual
          obtain ⟨effect, current, known, exposedRole⟩ := head_frame first good available role
          exact ih last current
            (fun value member => effect.keeps.available value (originalsAvailable value member))
            known exposedRole

/-- One actual class preserves a Program slot under its internal source footprint. -/
theorem run_class_roles {e p h m s n record values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo =
      .done results after saved)
    (good : SourceCurrentNativeOperationHeap.Good (width := width) before)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    (coherent : SourceEqualityClassOrder.Coherent record) (index : Nat)
    (footprint : ∀ childIndex, childIndex ≠ 0 → SourceCurrentClassPositionalFootprints.Unselected record index childIndex)
    {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result)
    (role : ProgramValue literal source) : ProgramValue literal result := by
  obtain ⟨entries, shared, start, finish, original, built, _sameState, _sameMemo, found, earlier, _later, dispatch⟩ :=
    SourceCurrentClassPositionalFootprints.class_dispatch actual coherent index 1 (footprint 1 (by decide)) output
  have same : original = source := Option.some.inj (found.symm.trans input)
  subst original
  rcases dispatch with ⟨_absent, rfl, _same⟩ | ⟨childEntries, selected, _absent, call⟩
  · exact role
  · have absent : ∀ childIndex : Nat, childIndex ≠ 0 →
        SourceEqualityNeededMap.lookup (childIndex : Int) childEntries = none := by
      intro childIndex nonzero
      obtain ⟨otherEntries, otherBuilt, other⟩ := SourceCurrentClassPositionalFootprints.compiled_unselected
        record coherent index childIndex (footprint childIndex nonzero)
      have sameEntries : otherEntries = entries := Edits.editBelow.inj (otherBuilt.symm.trans built)
      subst otherEntries
      rcases other with absent | ⟨otherChildren, otherSelected, otherAbsent⟩
      · rw [absent] at selected
        cases selected
      · have sameChildren : otherChildren = childEntries :=
          Edits.editBelow.inj (Option.some.inj (otherSelected.symm.trans selected))
        subst otherChildren
        simpa only [Int.ofNat_eq_natCast] using otherAbsent
    have earlierCall : SourceCurrentAllocatedSharedEditWorker.editList (Worker record values e p h m s n)
        (.editBelow entries) (values.take index) (SourceCurrentAllocatedSharedTargetState.initial before memo) =
        .done (results.take index) start := earlier
    obtain ⟨effect, current, _known⟩ := SourceCurrentLowerOperationInvariants.edit_list earlierCall
      (SharedGood.initial good stored) available
      (fun value member => available value (List.mem_of_mem_take member))
    exact below_roles call current
      (fun value member => effect.keeps.available value (available value member))
      (effect.keeps.available source (available source (List.mem_of_getElem? input))) role absent

open EqualityNormalize SourceSynthesisGuardRegions
open SourceSynthesisFirstOrderConstruction (Expression application ofType)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem source_signed_disjoint (path target : EqualityNormalize.Path)
    (excluded : ¬ path.IsPrefix target ∧ ¬ target.IsPrefix path) :
    SourceEqualityEditCompiledPaths.Disjoint (path.map Int.ofNat) (target.map Int.ofNat) :=
  ⟨fun initial => excluded.1 ((SourceEqualityClassEdits.signed_prefix path target).mp initial),
    fun initial => excluded.2 ((SourceEqualityClassEdits.signed_prefix target path).mp initial)⟩

section SelectedSource
variable [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
variable {inherited own : SourceEqualityConstraintAllocation.Value} {initial scanned : Checked width}
variable {records kept : List SourceEqualityClassOrder.Record} {budget : Nat} {values : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo} {outcome : Option Class} {selected : Constraints}
variable {scan : SourceCurrentConjunctionClassScan.Scan budget SourceMemoGate.unconstrained
  (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values (records.map SourceEqualityClassOrder.Record.paths)
  (SourceCurrentAllocatedPrecheck.state initial loaded inherited) fourth outcome selected scanned savedFourth}

private theorem selected_paths
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded inherited initial own (.classes records))
    (retained : SourceCurrentConjunctionSelectedRecords.Retained scan records kept)
    (region : EqualityNormalize.Path → Prop)
    (endpoints : ∀ path ∈ members ((SourceCompactGuards.sourceEqualities guard).getD []), region path)
    {record : SourceEqualityClassOrder.Record} (member : record ∈ kept) :
    SourceEqualityClassOrder.Coherent record ∧ ∀ path ∈ record.paths, region path := by
  obtain ⟨_proper, originals, _read, classes, ordered, coherent⟩ := receipt.classes records rfl
  have inRecords := retained.fields.1.subset member
  refine ⟨(coherent record inRecords).1, ?_⟩
  have inOrdered : record ∈ SourceEqualityClassOrder.ordered originals := by simpa only [ordered] using inRecords
  have inOriginals := (SourceEqualityClassOrder.ordered_perm originals).mem_iff.mp inOrdered
  intro path included
  apply endpoints path
  rw [classes]
  exact (mem_members _ _).mpr ⟨record.paths, List.mem_map.mpr ⟨record, inOriginals, rfl⟩, included⟩

/-- Actual application selection derives every non-annotation class-edit exclusion. -/
theorem selected_application_footprint (types function argument : Expression)
    (name : String) (children : List Expression)
    (occurrence : application types function argument = .node [.mk name guard children])
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded inherited initial own (.classes records))
    (retained : SourceCurrentConjunctionSelectedRecords.Retained scan records kept)
    {record : SourceEqualityClassOrder.Record} (member : record ∈ kept)
    (index : Nat) (programSlot : index = 2 ∨ index = 3) :
    SourceEqualityClassOrder.Coherent record ∧ ∀ childIndex, childIndex ≠ 0 →
      SourceCurrentClassPositionalFootprints.Unselected record index childIndex := by
  obtain ⟨coherent, paths⟩ := selected_paths receipt retained applicationRegion
    (application_guard_endpoints types function argument name guard children occurrence).2 member
  refine ⟨coherent, ?_⟩
  intro childIndex nonzero path included
  have opposite : 0 ≠ childIndex := Ne.symm nonzero
  apply source_signed_disjoint path [index, childIndex]
  have inside := paths path included
  rcases programSlot with rfl | rfl
  · rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;>
      simp_all [List.cons_prefix_cons]
  · rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;>
      simp_all [List.cons_prefix_cons]

/-- Actual filter selection derives every non-annotation class-edit exclusion. -/
theorem selected_filter_footprint (candidates goal : Expression)
    (name : String) (children : List Expression)
    (occurrence : ofType candidates goal = .node [.mk name guard children])
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded inherited initial own (.classes records))
    (retained : SourceCurrentConjunctionSelectedRecords.Retained scan records kept)
    {record : SourceEqualityClassOrder.Record} (member : record ∈ kept) :
    SourceEqualityClassOrder.Coherent record ∧ ∀ childIndex, childIndex ≠ 0 →
      SourceCurrentClassPositionalFootprints.Unselected record 1 childIndex := by
  obtain ⟨coherent, paths⟩ := selected_paths receipt retained filterRegion
    (filter_guard_endpoints candidates goal name guard children occurrence).2 member
  refine ⟨coherent, ?_⟩
  intro childIndex nonzero path included
  have opposite : 0 ≠ childIndex := Ne.symm nonzero
  apply source_signed_disjoint path [1, childIndex]
  have inside := paths path included
  rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;> simp_all [List.cons_prefix_cons]
end SelectedSource

end MicroCFTA.SourceSynthesisClassProgramRoles
