import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceEqualityPhysicalClassEntry

/-!
# Positional original records selected by current checked scans

Each actual selected branch retains its literal original head record.
Skipped, continued, and stopped branches retain no head record. The
receipt preserves order, multiplicity, and complete trie fields. The live
normalized accessor supplies coherence and nontriviality of these records.
No historical scan or intersection-based emptiness Call is used.
-/
namespace MicroCFTA.SourceCurrentConjunctionSelectedRecords
open EqualityNormalize SourceEqualityClassOrder InternedConstructorTemplates
open SourceCurrentConjunctionClassScan
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
variable {width : Nat}

/-- The actual scan keeps the literal original head only at a selected branch. -/
inductive Retained [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)} :
    {classes selected : Constraints} → {outcome : Option Class} →
    {before after : Checked width} → {memo saved : SourceCurrentEmptinessMemo.Memo} →
    Scan budget unconstrained reaches values classes before memo outcome selected after saved → List Record → List Record → Prop where
  | nil : Retained .nil [] []
  | selected {paths : Class} {classes selected : Constraints} {outcome : Option Class}
      {before after : Checked width} {heap : State Symbol Guard} {memo saved : SourceCurrentEmptinessMemo.Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap false heap}
      {rest : Scan budget unconstrained reaches values classes (advanceHeap before heap) memo outcome selected after saved}
      {record : Record} {records kept : List Record}
      (head : record.paths = paths) (tail : Retained rest records kept) :
      Retained (.selected primary rest) (record :: records) (record :: kept)
  | skipped {paths : Class} {classes selected : Constraints} {outcome : Option Class}
      {before after : Checked width} {heap anchor : State Symbol Guard} {memo saved : SourceCurrentEmptinessMemo.Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap true anchor}
      {rest : Scan budget unconstrained reaches values classes (advanceHeap (advanceHeap before heap) anchor)
        memo outcome selected after saved}
      {record : Record} {records kept : List Record}
      (head : record.paths = paths) (tail : Retained rest records kept) :
      Retained (.skipped primary secondary rest) (record :: records) kept
  | continued {paths : Class} {classes selected : Constraints} {outcome : Option Class}
      {before middle after : Checked width} {later : Physical} {heap anchor : State Symbol Guard}
      {query : Value Symbol Guard} {memo savedMemo saved : SourceCurrentEmptinessMemo.Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor}
      {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle}
      {decision : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) false later savedMemo}
      {rest : Scan budget unconstrained reaches values classes (advancePhysical middle later)
        savedMemo outcome selected after saved}
      {record : Record} {records kept : List Record}
      (head : record.paths = paths) (tail : Retained rest records kept) :
      Retained (.continued primary secondary seeded decision rest) (record :: records) kept
  | stopped {paths : Class} {classes : Constraints} {before middle : Checked width} {later : Physical}
      {heap anchor : State Symbol Guard} {query : Value Symbol Guard} {memo saved : SourceCurrentEmptinessMemo.Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor}
      {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle}
      {decision : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) true later saved}
      {record : Record} {records : List Record}
      (head : record.paths = paths) (remaining : records.map Record.paths = classes) :
      Retained (.stopped (classes := classes) primary secondary seeded decision) (record :: records) []

/-- The positional receipt retains exact original order and the actual selected path list. -/
theorem Retained.fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {records kept : List Record} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : SourceCurrentEmptinessMemo.Memo}
    {trace : Scan budget unconstrained reaches values classes before memo outcome selected after saved}
    (receipt : Retained trace records kept) : kept.Sublist records ∧ kept.map Record.paths = selected := by
  induction receipt with
  | nil => exact ⟨.refl _, rfl⟩
  | selected head tail ih => exact ⟨.cons_cons _ ih.1, by simp only [List.map_cons, head, ih.2]⟩
  | skipped head tail ih => exact ⟨.cons _ ih.1, ih.2⟩
  | continued head tail ih => exact ⟨.cons _ ih.1, ih.2⟩
  | stopped => exact ⟨List.nil_sublist _, rfl⟩

/-- A positional receipt is aligned with the literal original input records. -/
theorem Retained.input [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {records kept : List Record} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : SourceCurrentEmptinessMemo.Memo}
    {trace : Scan budget unconstrained reaches values classes before memo outcome selected after saved}
    (receipt : Retained trace records kept) : records.map Record.paths = classes := by
  induction receipt with
  | nil => rfl
  | selected head tail ih | skipped head tail ih | continued head tail ih =>
      simp only [List.map_cons, head, ih]
  | stopped head remaining => simp only [List.map_cons, head, remaining]

/-- Every actual checked scan derives a positional record receipt without a selection premise. -/
theorem retained_records [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    (records : List Record) {selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : SourceCurrentEmptinessMemo.Memo}
    (trace : Scan budget unconstrained reaches values (records.map Record.paths) before memo outcome selected after saved) :
    ∃ kept : List Record, Retained trace records kept := by
  generalize aligned : records.map Record.paths = classes at trace
  induction trace generalizing records with
  | nil =>
      have empty : records = [] := List.map_eq_nil_iff.mp aligned
      subst records
      exact ⟨[], .nil⟩
  | selected primary rest ih =>
      cases records with
      | nil => cases aligned
      | cons record records =>
          have aligned := List.cons.inj aligned
          obtain ⟨kept, retained⟩ := ih records aligned.2
          exact ⟨record :: kept, .selected (primary := primary) aligned.1 retained⟩
  | skipped primary secondary rest ih =>
      cases records with
      | nil => cases aligned
      | cons record records =>
          have aligned := List.cons.inj aligned
          obtain ⟨kept, retained⟩ := ih records aligned.2
          exact ⟨kept, .skipped (primary := primary) (secondary := secondary) aligned.1 retained⟩
  | continued primary secondary seeded decision rest ih =>
      cases records with
      | nil => cases aligned
      | cons record records =>
          have aligned := List.cons.inj aligned
          obtain ⟨kept, retained⟩ := ih records aligned.2
          exact ⟨kept, .continued (primary := primary) (secondary := secondary) (seeded := seeded)
            (decision := decision) aligned.1 retained⟩
  | stopped primary secondary seeded decision =>
      cases records with
      | nil => cases aligned
      | cons record records =>
          have aligned := List.cons.inj aligned
          exact ⟨[], .stopped (primary := primary) (secondary := secondary) (seeded := seeded)
            (decision := decision) aligned.1 aligned.2⟩

/-- The computed live entry supplies coherent active fields for the exact retained records. -/
theorem live_retained_records [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (inherited : SourceEqualityPrecheck.Constraint) (records : List Record)
    (live : SourceEqualityPhysicalClassEntry.entry constraint inherited = .ok (.classes records))
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : SourceCurrentEmptinessMemo.Memo}
    (trace : Scan budget unconstrained reaches values (records.map Record.paths) before memo outcome selected after saved) :
    ∃ kept : List Record, Retained trace records kept ∧ kept.Sublist records ∧ kept.map Record.paths = selected ∧
      ∀ record ∈ kept, Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths := by
  obtain ⟨_, _, _, _, _, fields⟩ := SourceEqualityPhysicalClassEntry.live_records constraint cached inherited records live
  obtain ⟨kept, receipt⟩ := retained_records records trace
  have retained := receipt.fields
  exact ⟨kept, receipt, retained.1, retained.2, fun record member => fields record (retained.1.subset member)⟩

end MicroCFTA.SourceCurrentConjunctionSelectedRecords
