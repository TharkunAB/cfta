import MicroCFTA.SourceCurrentPositionalRowOrigins
import MicroCFTA.SourceCurrentRequiredGuard
import MicroCFTA.SourceCurrentNativeOperationHeap

/-!
# Indexed positional origins through actual Required execution

An output row either has an empty own field or retains an indexed input
row and the exact unselected child. Recursive inputs use their actual
plain gate. This is an explicit entry condition. Other child calls can
contain arbitrary recursive work. No future semantic read is supplied.
-/
namespace MicroCFTA.SourceCurrentActualRequiredRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "RowOrigin" => SourceCurrentRequiredGuardOrigins.RowOrigin

/-- Recursive roots must pass the actual plain gate; ordinary roots have no guard restriction. -/
def Root : Node → Prop
  | .empty | .node .. => True
  | value => SourceMemoGate.unconstrained value = true

/-- Each output row is plain or retains a complete input row and its exact selected child. -/
def Link (childIndex : Nat) (source result : Node) : Prop :=
  ∀ row ∈ nodeEdges result,
    SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some []) ∨
      ∃ (sourceIndex : Nat) (original : Edge), (nodeEdges source)[sourceIndex]? = some original ∧
        RowOrigin original row ∧ row.children[childIndex]? = original.children[childIndex]?

/-- An unchanged value retains each indexed root row. -/
theorem Link.refl (childIndex : Nat) (value : Node) : Link childIndex value value := by
  intro row member
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
  exact .inr ⟨index,row,found,⟨rfl,rfl,rfl⟩,rfl⟩

/-- Consecutive row origins compose through the exact retained child and complete raw fields. -/
theorem Link.trans {childIndex : Nat} {source middle result : Node}
    (first : Link childIndex source middle) (last : Link childIndex middle result) :
    Link childIndex source result := by
  intro row member
  rcases last row member with plain | ⟨index,original,found,origin,unchanged⟩
  · exact .inl plain
  · rcases first original (List.mem_of_getElem? found) with plain | ⟨sourceIndex,earlier,earlierFound,earlierOrigin,earlierChild⟩
    · exact .inl (by rw [origin.1]; exact plain)
    · exact .inr ⟨sourceIndex,earlier,earlierFound,
        ⟨origin.1.trans earlierOrigin.1,origin.2.1.trans earlierOrigin.2.1,origin.2.2.trans earlierOrigin.2.2⟩,
        unchanged.trans earlierChild⟩

/-- A nonempty output own field has a complete indexed input origin and the same child value. -/
theorem Link.positive {childIndex : Nat} {source result : Node} (link : Link childIndex source result)
    {row : Edge} (member : row ∈ nodeEdges result) {records : List SourceEqualityClassOrder.Record}
    (own : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records)) (nonempty : records ≠ []) :
    ∃ (sourceIndex : Nat) (original : Edge), (nodeEdges source)[sourceIndex]? = some original ∧
      RowOrigin original row ∧ row.children[childIndex]? = original.children[childIndex]? := by
  rcases link row member with plain | origin
  · rw [own] at plain
    exact False.elim (nonempty (Option.some.inj (Except.ok.inj plain)))
  · exact origin

private theorem root_of_accepted {value : Node} (accepted : SourceMemoGate.unconstrained value = true) : Root value := by
  cases value <;> first | trivial | exact accepted

private theorem root_of_ordinary {value : Node} (ordinary : SourceEqualityRequiredCache.Ordinary value) : Root value := by
  cases value <;> trivial

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem ordinary_root {entries entry rows depth free result before after}
    (actual : RequireNode (.node entries) (.node entry rows depth free) before result after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before (.node entry rows depth free)) : Root result := by
  cases actual with
  | identity => trivial
  | @ordinary entries rows before rebuilt middle result after entry depth free nonempty call built =>
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) call semantic costs
      (by intro _ _ _; trivial) resident
    have ordinary := SourceEqualityRequiredCache.node_ordinary rebuilt middle effects.2.1.ready.semantic.1.normal.facts effects.2.2.2.2
    have same : result = (run (makeNode rebuilt) middle).1 := by rw [built]
    rw [same]
    exact root_of_ordinary ordinary
  | recursive nonempty recursive => cases recursive

/-- An actual Required node preserves positional origins and the supported root shape. -/
theorem node {entries value result before after} (actual : RequireNode (.node entries) value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : GuardHeap Plain before) (root : Root value)
    (childIndex : Nat) (absent : SourceEqualityNeededMap.lookup (childIndex : Int) entries = none) :
    Root result ∧ Link childIndex value result := by
  have acceptedCase (accepted : SourceMemoGate.unconstrained value = true) : Root result ∧ Link childIndex value result := by
    have returned := SourceCurrentRequiredGuardOrigins.accepted_node actual semantic costs available guards accepted
    exact ⟨root_of_accepted (SourceCurrentHereditaryUnconstrained.unconstrained result returned.2.1),
      fun row member => .inl (returned.2.2 row member)⟩
  cases value with
  | empty =>
    cases actual with
    | identity | empty => exact ⟨by trivial,fun row impossible => by cases impossible⟩
    | recursive nonempty recursive => cases recursive
  | node entry rows depth free =>
    exact ⟨ordinary_root actual semantic costs available,fun row member => .inr
      (SourceCurrentPositionalRowOrigins.required_node actual semantic costs available childIndex absent row member)⟩
  | reference | mu | union => exact acceptedCase root

/-- A compiled selected node must leave this continuation child unselected. -/
def Unselected (entries : List (Int × Needed)) (forestIndex childIndex : Nat) : Prop :=
  ∀ needed, SourceEqualityNeededMap.lookup (forestIndex : Int) entries = some needed →
    ∀ children, needed = .node children → SourceEqualityNeededMap.lookup (childIndex : Int) children = none

/-- An actual ordered Required scan derives the same-index positional origin from entry facts. -/
theorem children {entries offset values results before after}
    (actual : RequireChildren entries offset values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (guards : GuardHeap Plain before) (index childIndex : Nat) {source result : Node}
    (input : values[index]? = some source) (output : results[index]? = some result)
    (root : Root source) (unselected : Unselected entries (offset+index) childIndex) :
    Root result ∧ Link childIndex source result := by
  induction index generalizing offset values results before after with
  | zero =>
    cases actual with
    | nil => cases input
    | unselected =>
      have first := Option.some.inj input
      have last := Option.some.inj output
      cases first
      cases last
      exact ⟨root,Link.refl _ _⟩
    | selected offset found first rest =>
      cases Option.some.inj input
      cases Option.some.inj output
      cases observed : SourceEqualityNeededMap.lookup (offset : Int) entries with
      | none => rw [observed] at found; cases found
      | some selectedNeeded =>
        have same := Option.some.inj (observed.symm.trans found)
        cases same
        cases selectedNeeded with
        | node children => exact node first semantic costs (available _ List.mem_cons_self) guards root childIndex
            (unselected _ (by simpa using found) _ rfl)
  | succ index ih =>
    cases actual with
    | nil => cases input
    | unselected offset absent rest =>
      exact ih rest semantic costs (fun value member => available value (List.mem_cons_of_mem _ member)) guards input output root
        (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using unselected)
    | selected offset found first rest =>
      have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs
        (by intro _ _ _; trivial) (available _ List.mem_cons_self)
      have retained := SourceCurrentRequiredGuard.node Plain first semantic costs (available _ List.mem_cons_self) guards
      exact ih rest effects.2.1 effects.2.2.1
        (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member))) retained input output root
        (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using unselected)

/-- Literal source preparation supplies its own graph and indexed row relation. -/
theorem prepare {width : Nat} {fuel readFuel paths values before results after}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before.native.machine.heap = .done results after)
    (good : SourceCurrentNativeOperationHeap.Good (width := width) before)
    (available : Values before.native.machine.heap values) (guards : GuardHeap Plain before.native.machine.heap)
    (index childIndex : Nat) {source result : Node} (input : values[index]? = some source) (output : results[index]? = some result)
    (root : Root source)
    (unselected : ∀ entries, SourceEqualityNeeded.build paths = .node entries → Unselected entries index childIndex) :
    Root result ∧ Link childIndex source result := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before.native.machine.heap results after).mpr
    ⟨fuel,readFuel,actual⟩
  cases built : SourceEqualityNeeded.build paths with
  | node entries =>
    simp only [built] at graph
    exact children graph good.semantic good.costs available guards index childIndex input output root
      (by simpa only [Nat.zero_add] using unselected entries built)

end MicroCFTA.SourceCurrentActualRequiredRowOrigins
