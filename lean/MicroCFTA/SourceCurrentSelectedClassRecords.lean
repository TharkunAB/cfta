import MicroCFTA.SourceEqualityPhysicalClassEntry

/-!
# Original physical records retained by current class scans

The returned selected paths lift to a sublist of the original record list.
The lift preserves order and multiplicity. It copies no trie or path field.
The actual normalized entry supplies coherent ascending nontrivial fields
for each retained record. Equal path lists need not determine a unique
positional witness. No forest closedness or fallback execution is asserted.
-/
namespace MicroCFTA.SourceCurrentSelectedClassRecords
open EqualityNormalize SourceEqualityClassOrder InternedConstructorTemplates
open SourceCurrentEqualityClassScan
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual selected paths retain an ordered sublist of complete original records. -/
theorem selected_records [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    (records : List Record) {selected : Constraints} {outcome : Option Class}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (trace : Scan unconstrained reaches values (records.map Record.paths) before memo outcome selected after saved) :
    ∃ kept : List Record, kept.Sublist records ∧ kept.map Record.paths = selected := by
  obtain ⟨kept, included, same⟩ := List.sublist_map_iff.mp (selected_sublist trace)
  exact ⟨kept, included, same.symm⟩


/-- The actual live accessor entry derives every retained physical record invariant. -/
theorem live_selected_records [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (inherited : SourceEqualityPrecheck.Constraint) (records : List Record)
    (live : SourceEqualityPhysicalClassEntry.entry constraint inherited = .ok (.classes records))
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {selected : Constraints} {outcome : Option Class}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (trace : Scan unconstrained reaches values (records.map Record.paths) before memo outcome selected after saved) :
    ∃ kept : List Record, kept.Sublist records ∧ kept.map Record.paths = selected ∧
      ∀ record ∈ kept, Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths := by
  obtain ⟨_, _, _, _, _, fields⟩ := SourceEqualityPhysicalClassEntry.live_records constraint cached inherited records live
  obtain ⟨kept, included, same⟩ := selected_records records trace
  exact ⟨kept, included, same, fun record member => fields record (included.subset member)⟩

/-- Positional receipts retain the literal original head only at an actual selected branch. -/
inductive Retained [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)} :
    {classes selected : Constraints} → {outcome : Option Class} →
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard} →
    {memo saved : SourceCurrentEmptinessMemo.Memo} →
    Scan unconstrained reaches values classes before memo outcome selected after saved → List Record → List Record → Prop where
  | nil : Retained .nil [] []
  | selected {paths : Class} {classes selected : Constraints} {outcome : Option Class}
      {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
      {heap : State Symbol Guard} {memo saved : SourceCurrentEmptinessMemo.Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap false heap}
      {rest : Scan unconstrained reaches values classes (SourceEqualityNativeScoped.advanceHeap before heap)
        memo outcome selected after saved}
      {record : Record} {records kept : List Record}
      (head : record.paths = paths) (tail : Retained rest records kept) :
      Retained (.selected primary rest) (record :: records) (record :: kept)
  | skipped {paths : Class} {classes selected : Constraints} {outcome : Option Class}
      {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
      {heap anchor : State Symbol Guard} {memo saved : SourceCurrentEmptinessMemo.Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap true anchor}
      {rest : Scan unconstrained reaches values classes
        (SourceEqualityNativeScoped.advanceHeap (SourceEqualityNativeScoped.advanceHeap before heap) anchor)
        memo outcome selected after saved}
      {record : Record} {records kept : List Record}
      (head : record.paths = paths) (tail : Retained rest records kept) :
      Retained (.skipped primary secondary rest) (record :: records) kept
  | continued {paths : Class} {classes selected : Constraints} {outcome : Option Class}
      {before middle later after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
      {heap anchor : State Symbol Guard} {query : Value Symbol Guard}
      {memo savedMemo saved : SourceCurrentEmptinessMemo.Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor}
      {seeded : SourceEmptinessClassFold.Seeded
        (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) SourceEqualityPCSNativeEdge.conjoin
        values (paths.map (List.map Int.ofNat))
        (SourceEqualityNativeScoped.advanceHeap (SourceEqualityNativeScoped.advanceHeap before heap) anchor) query middle}
      {decision : SourceCurrentEmptinessMemo.Call memo query middle false later savedMemo}
      {rest : Scan unconstrained reaches values classes later savedMemo outcome selected after saved}
      {record : Record} {records kept : List Record}
      (head : record.paths = paths) (tail : Retained rest records kept) :
      Retained (.continued primary secondary seeded decision rest) (record :: records) kept
  | stopped {paths : Class} {classes : Constraints}
      {before middle after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
      {heap anchor : State Symbol Guard} {query : Value Symbol Guard}
      {memo saved : SourceCurrentEmptinessMemo.Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor}
      {seeded : SourceEmptinessClassFold.Seeded
        (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) SourceEqualityPCSNativeEdge.conjoin
        values (paths.map (List.map Int.ofNat))
        (SourceEqualityNativeScoped.advanceHeap (SourceEqualityNativeScoped.advanceHeap before heap) anchor) query middle}
      {decision : SourceCurrentEmptinessMemo.Call memo query middle true after saved}
      {record : Record} {records : List Record}
      (head : record.paths = paths) (remaining : records.map Record.paths = classes) :
      Retained (.stopped primary secondary seeded decision) (record :: records) []

/-- Positional selection derives both original-record order and the actual returned path list. -/
theorem Retained.fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {records kept : List Record} {classes selected : Constraints} {outcome : Option Class}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    {trace : Scan unconstrained reaches values classes before memo outcome selected after saved}
    (receipt : Retained trace records kept) : kept.Sublist records ∧ kept.map Record.paths = selected := by
  induction receipt with
  | nil => exact ⟨.refl _, rfl⟩
  | selected head tail ih => exact ⟨.cons_cons _ ih.1, by simp only [List.map_cons, head, ih.2]⟩
  | skipped head tail ih => exact ⟨.cons _ ih.1, ih.2⟩
  | continued head tail ih => exact ⟨.cons _ ih.1, ih.2⟩
  | stopped => exact ⟨List.nil_sublist _, rfl⟩

/-- Each actual current scan derives its positional original-record receipt without a selection premise. -/
theorem retained_records [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    (records : List Record) {selected : Constraints} {outcome : Option Class}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (trace : Scan unconstrained reaches values (records.map Record.paths) before memo outcome selected after saved) :
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

/-- Normalized physical entry derives field invariants for the exact positional scan selection. -/
theorem live_retained_records [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (inherited : SourceEqualityPrecheck.Constraint) (records : List Record)
    (live : SourceEqualityPhysicalClassEntry.entry constraint inherited = .ok (.classes records))
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {selected : Constraints} {outcome : Option Class}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (trace : Scan unconstrained reaches values (records.map Record.paths) before memo outcome selected after saved) :
    ∃ kept : List Record, Retained trace records kept ∧ kept.Sublist records ∧ kept.map Record.paths = selected ∧
      ∀ record ∈ kept, Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths := by
  obtain ⟨_, _, _, _, _, fields⟩ := SourceEqualityPhysicalClassEntry.live_records constraint cached inherited records live
  obtain ⟨kept, receipt⟩ := retained_records records trace
  have retained := receipt.fields
  exact ⟨kept, receipt, retained.1, retained.2, fun record member => fields record (retained.1.subset member)⟩

end MicroCFTA.SourceCurrentSelectedClassRecords
