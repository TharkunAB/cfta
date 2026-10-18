import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.SourceCurrentRequiredGuardOrigins
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Positional row origins from actual ordinary edit returns

The proofs inspect successful literal worker equations. Initial physical
invariants supply intermediate fields and availability. Ordinary node
normalization can remove or reorder rows. Each retained row keeps an indexed
source row, its full raw fields, and each unselected child value.
-/
namespace MicroCFTA.SourceCurrentActualEditRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentLowerOperationInvariants (Effect SharedGood)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "RowOrigin" => SourceCurrentRequiredGuardOrigins.RowOrigin
local notation "Worker" => SourceCurrentAllocatedSharedEditWorker.edit
variable {width : Nat}

private theorem bind_done {A B : Type}
    (first : SourceCurrentAllocatedSharedEditWorker.Outcome width A)
    (next : A → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width B)
    {value : B} {after : Shared width} (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

/-- Every successful literal child scan preserves the number of positions. -/
theorem children_length
    (recur : SourceEqualityEdits.Edits EqualityNormalize.Path → Node → Shared width →
      SourceCurrentAllocatedSharedEditWorker.Outcome width Node)
    {entries offset values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.children recur entries offset values before = .done results after) :
    results.length = values.length := by
  induction values generalizing offset before results after with
  | nil => cases actual; rfl
  | cons value values ih =>
    cases found : SourceEqualityNeededMap.lookup (offset : Int) entries with
    | none =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨tail,final,rest,last⟩ := bind_done _ _ actual
      cases last
      exact congrArg Nat.succ (ih rest)
    | some edits =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨head,middle,first,later⟩ := bind_done _ _ actual
      obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
      cases last
      exact congrArg Nat.succ (ih rest)

/-- An absent child key retains the complete value at the same position. -/
theorem children_unselected
    (recur : SourceEqualityEdits.Edits EqualityNormalize.Path → Node → Shared width →
      SourceCurrentAllocatedSharedEditWorker.Outcome width Node)
    {entries offset values before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.children recur entries offset values before = .done results after)
    (index : Nat) (absent : SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = none) :
    results[index]? = values[index]? := by
  induction values generalizing offset before results after index with
  | nil => cases actual; rfl
  | cons value values ih =>
    cases found : SourceEqualityNeededMap.lookup (offset : Int) entries with
    | none =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨tail,final,rest,last⟩ := bind_done _ _ actual
      cases last
      cases index with
      | zero => rfl
      | succ index => exact ih rest index (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using absent)
    | some edits =>
      simp only [SourceCurrentAllocatedSharedEditWorker.children,found] at actual
      obtain ⟨head,middle,first,later⟩ := bind_done _ _ actual
      obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
      cases last
      cases index with
      | zero => simp only [Nat.add_zero,found] at absent; cases absent
      | succ index => exact ih rest index (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using absent)

private theorem shared_advance {before : Shared width} (good : SharedGood before) {checked : Checked width}
    (effect : Effect before.checked checked) : SharedGood (SourceCurrentAllocatedSharedTargetState.advance before checked) :=
  ⟨effect.good,good.stored.grows effect.keeps,
    fun path value present => effect.keeps.available value (good.slots path value present)⟩

private theorem edge_effect [DecidableEq (EdgeKey Symbol Guard)] {before : Checked width}
    (good : SourceCurrentNativeOperationHeap.Good before) (symbol : Symbol) (guard : Guard) (values : List Node)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations guard)
    (available : Values before.native.machine.heap values) :
    Effect before (advancePhysical before ⟨(run (makeEdge symbol guard values) before.native.machine.heap).2,before.operations⟩) ∧
      EdgeResident (run (makeEdge symbol guard values) before.native.machine.heap).2
        (run (makeEdge symbol guard values) before.native.machine.heap).1 := by
  have checked := SourceEqualityRequiredCache.edge symbol guard values _ good.heap available
  have semantic := SourceEqualityRequiredSemanticCache.edge symbol guard values _ good.semantic available
  have fields := SourceEqualityAnnotationHeap.run (SourceCurrentConjunctionEquality.FieldAvailable before.operations) _
    (SourceEqualityAnnotationHeap.makeEdge _ symbol guard values field) _ good.fields
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before)
      ⟨(run (makeEdge symbol guard values) before.native.machine.heap).2,before.operations⟩ :=
    ⟨checked.1,⟨semantic,good.costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  exact ⟨⟨good.advance _ effects,checked.1,effects.grows⟩,checked.2.1⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem rows_law {record originals e p h m s n entries rows before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.rows (Worker record originals e p h m s n)
      entries rows before = .done results after)
    (good : SharedGood (width := width) before)
    (originalsAvailable : Values before.checked.native.machine.heap originals)
    (resident : Edges before.checked.native.machine.heap rows) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Edges after.checked.native.machine.heap results ∧
    ∀ (index : Nat) (result : Edge), results[index]? = some result → ∃ original, rows[index]? = some original ∧ RowOrigin original result ∧
      ∀ (childIndex : Nat), SourceEqualityNeededMap.lookup (childIndex : Int) entries = none →
        result.children[childIndex]? = original.children[childIndex]? := by
  induction rows generalizing before results after with
  | nil =>
    cases actual
    exact ⟨.refl _ good.checked,good,by simp [Edges],by intro index result absent; cases index <;> cases absent⟩
  | cons edge rows ih =>
    obtain ⟨values,middle,children,later⟩ := bind_done _ _ actual
    have available := good.checked.heap.semantic.1.normal.facts.cached.edges _ _ (resident _ List.mem_cons_self)
    have childActual : SourceCurrentAllocatedSharedEditWorker.editList (Worker record originals e p h m s n)
        (.editBelow entries) edge.children before = .done values middle := children
    obtain ⟨firstEffect,current,known⟩ := SourceCurrentLowerOperationInvariants.edit_list childActual good originalsAvailable available
    obtain ⟨rebuilt,afterEdge,built,later⟩ := bind_done _ _ later
    have field := (good.checked.fields _ _ (resident _ List.mem_cons_self)).grows firstEffect.operations
    have checked := edge_effect current.checked edge.entry.key.symbol edge.entry.key.constraint values field known
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.checked.native.machine.heap
      current.checked.heap.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint values known
    simp only [SourceCurrentAllocatedSharedEditWorker.work] at built
    cases built
    obtain ⟨tail,final,rest,last⟩ := bind_done _ _ later
    cases last
    have edgeGood := shared_advance current checked.1
    have prefixEffect := firstEffect.trans checked.1
    obtain ⟨lastEffect,finalGood,tailKnown,origins⟩ := ih rest edgeGood
      (fun value member => prefixEffect.keeps.available value (originalsAvailable value member))
      (fun row member => edge_grows _ _ prefixEffect.keeps.growth row (resident row (List.mem_cons_of_mem _ member)))
    refine ⟨prefixEffect.trans lastEffect,finalGood,?_,?_⟩
    · intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact edge_grows _ _ lastEffect.keeps.growth _ checked.2
      · exact tailKnown output member
    · intro index result selected
      cases index with
      | zero =>
        have same := Option.some.inj selected
        subst result
        refine ⟨edge,rfl,⟨fields.2.1,fields.1,?_⟩,?_⟩
        · exact (congrArg List.length fields.2.2).trans (children_length _ children)
        · intro childIndex absent
          rw [fields.2.2]
          exact children_unselected _ children childIndex (by simpa only [Nat.zero_add] using absent)
      | succ index =>
        obtain ⟨original,found,origin,unchanged⟩ := origins index result selected
        exact ⟨original,found,origin,unchanged⟩

/-- A returned pre-normalization row has the source row at the same index and all absent child positions. -/
theorem rows_indexed {record originals e p h m s n entries rows before results after}
    (actual : SourceCurrentAllocatedSharedEditWorker.rows (Worker record originals e p h m s n)
      entries rows before = .done results after)
    (good : SharedGood (width := width) before)
    (originalsAvailable : Values before.checked.native.machine.heap originals)
    (resident : Edges before.checked.native.machine.heap rows)
    (index : Nat) {result : Edge} (selected : results[index]? = some result) :
    ∃ original, rows[index]? = some original ∧ RowOrigin original result ∧
      ∀ (childIndex : Nat), SourceEqualityNeededMap.lookup (childIndex : Int) entries = none →
        result.children[childIndex]? = original.children[childIndex]? :=
  (rows_law actual good originalsAvailable resident).2.2.2 index result selected

/-- Every normalized ordinary edit survivor retains a full indexed source row and its absent child value. -/
theorem edit_node {record originals e p h m s n entries entry rows depth free before value after}
    (actual : Worker record originals e p h m s n (.editBelow entries) (.node entry rows depth free) before = .done value after)
    (good : SharedGood (width := width) before)
    (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap (.node entry rows depth free))
    (childIndex : Nat) (absent : SourceEqualityNeededMap.lookup (childIndex : Int) entries = none)
    {result : Edge} (selected : result ∈ nodeEdges value) :
    ∃ (sourceIndex : Nat) (original : Edge), rows[sourceIndex]? = some original ∧ RowOrigin original result ∧
      result.children[childIndex]? = original.children[childIndex]? := by
  cases e with
  | zero => cases actual
  | succ e =>
    obtain ⟨rebuilt,middle,first,last⟩ := bind_done _ _ actual
    have resident := resident_edges _ good.checked.heap.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨effect,current,known,origins⟩ := rows_law first good originalsAvailable resident
    simp only [SourceCurrentAllocatedSharedEditWorker.work] at last
    cases last
    have fields := EqualityLeafProjectionPhysical.makeNode_edges rebuilt middle.checked.native.machine.heap
      current.checked.heap.semantic.1.normal.facts.coherent current.checked.heap.semantic.1.normal.facts.linked known
    have included : result ∈ canonicalEdges (surviving rebuilt) := fields ▸ selected
    have member := (List.mem_filter.mp (canonicalEdges_member _ result included)).1
    obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨original,present,origin,unchanged⟩ := origins index result found
    exact ⟨index,original,present,origin,unchanged childIndex absent⟩

end MicroCFTA.SourceCurrentActualEditRowOrigins
