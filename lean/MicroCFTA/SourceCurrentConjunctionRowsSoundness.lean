import MicroCFTA.SourceCurrentConjunctionRowsAllocation
import MicroCFTA.SourceCurrentConjunctionRequirementsSoundness

/-!
# Smaller accepted witnesses in allocated conjunction rows

The actual exposure sequence supplies a common accepted tuple. Its actual
allocated equality fold excludes contradiction. The retained live tuple
supplies one literal stored row. Each requirement in that row has a smaller
accepted common term. No row supplier or final-state invariant is assumed.
-/
namespace MicroCFTA.SourceCurrentConjunctionRowsSoundness
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionRowsAllocation
open SourceCurrentConjunctionEmptinessRows (Accepts)
open InternedGuardedLanguage (meaning)

/-- Local stored rows cover every common accepted term by smaller accepted requirements. -/
def Coverage (relation : Node → Term Symbol → Prop) (nodes : List Node) (rows : List (List (List Node))) : Prop :=
  ∀ term, Accepts relation nodes term → ∃ row ∈ rows,
    ∀ requirement ∈ row, ∃ part, Accepts relation requirement part ∧ part.height < term.height

section Effects
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Actual tuple prefixes derive each next ready state and retain all original resident edges. -/
theorem tuples_verified [DecidableEq (EdgeKey Symbol Guard)]
    {tuples : List (List (EdgeValue Symbol Guard))}
    {before after : SourceCurrentConjunctionRowsAllocation.State Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Tuples tuples before rows after)
    (ready : Ready before) (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) : Effects before after ∧ RowsReady after rows := by
  revert closed resident ready
  induction actual with
  | nil => intro ready _ _; exact ⟨Effects.refl _ ready, by simp [RowsReady]⟩
  | @skip tuple before middle tuples rows after first rest ih =>
      intro ready resident closed
      have own := first.verified ready (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self)
      have later := ih own.1.ready
        (fun chosen member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap own.1.keeps.growth
          edge (resident chosen (List.mem_cons_of_mem _ member) edge included))
        (fun chosen member => closed chosen (List.mem_cons_of_mem _ member))
      exact ⟨own.1.trans later.1, later.2⟩
  | @keep tuple before row middle tuples rows after first rest ih =>
      intro ready resident closed
      have own := first.verified ready (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self)
      have later := ih own.1.ready
        (fun chosen member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap own.1.keeps.growth
          edge (resident chosen (List.mem_cons_of_mem _ member) edge included))
        (fun chosen member => closed chosen (List.mem_cons_of_mem _ member))
      refine ⟨own.1.trans later.1, ?_⟩
      intro chosen member
      rcases List.mem_cons.mp member with rfl | member
      · intro requirement included
        have earlier := own.2 requirement included
        exact ⟨fun value present => later.1.keeps.available value (earlier.1 value present), earlier.2⟩
      · exact later.2 chosen member

/-- Completed actual row reads and allocations derive their final physical and equality invariants. -/
theorem rows_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {nodes : List (Value Symbol Guard)} {before after : SourceCurrentConjunctionRowsAllocation.State Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Rows nodes before rows after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    Effects before after ∧ RowsReady after rows := by
  cases actual with
  | @run edges heap rows after before reads tuples =>
      have own := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have middle : Ready (⟨heap, before.equality⟩ : SourceCurrentConjunctionRowsAllocation.State Symbol Formula) :=
        ⟨own.1.semantic, own.1.costs, ready.valid, own.1.annotations⟩
      have later := tuples_verified tuples middle
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed tuple member).2.1)
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed tuple member).2.2)
      exact ⟨⟨own.1.keeps.trans later.1.keeps, later.1.ready, later.1.grows⟩, later.2⟩
end Effects

section ActualGuards
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A common accepted physical tuple cannot be skipped and derives its actual requirement witnesses. -/
theorem tuple_witness [DecidableEq (EdgeKey Symbol Guard)]
    {tuple : List (EdgeValue Symbol Guard)}
    {before after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula}
    {row : Option (List (List (Value Symbol Guard)))} (actual : Tuple tuple before row after)
    (ready : Ready before) (resident : Edges before.heap tuple) (closed : ClosedEdges tuple) (nonempty : tuple ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
      (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
      (SourceCurrentConjunctionCompletionReads.edgeView edge) term) :
    ∃ requirements, row = some requirements ∧ ∀ requirement ∈ requirements, ∃ part,
      Accepts (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) requirement part ∧ part.height < term.height := by
  obtain ⟨stored, done, _, _, classes, _, _, fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.heap before.equality ready.valid ready.fields resident
  cases actual with
  | @contradiction result before folded empty =>
      have same : stored = result := Option.some.inj (Except.ok.inj (done.symm.trans folded))
      subst stored
      have combined : SourceCurrentConjunctionEmptinessRows.combined
          (tuple.map SourceCurrentConjunctionCompletionReads.edgeView) = none := classes.symm.trans empty
      have satisfied := (SourceCurrentConjunctionEmptinessRows.combined_sat
        (tuple.map SourceCurrentConjunctionCompletionReads.edgeView) term).mpr (by
          intro view member
          obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
          exact (accepted edge included).choose_spec.2.2)
      rw [combined] at satisfied
      exact False.elim satisfied
  | @live result constraints row heap before folded live requirements =>
      have same : stored = result := Option.some.inj (Except.ok.inj (done.symm.trans folded))
      subst stored
      have combined : SourceCurrentConjunctionEmptinessRows.combined
          (tuple.map SourceCurrentConjunctionCompletionReads.edgeView) = some constraints := classes.symm.trans live
      exact ⟨row, rfl, SourceCurrentConjunctionRequirementsSoundness.accepted_tuple
        (SourceCurrentConjunctionEquality.FieldAvailable (SourceCurrentConjunctionEquality.fold tuple before.equality).2)
        requirements ready.semantic ready.costs fields resident closed nonempty combined
        (SourceEqualityPCSGuard.holds formulas solver) ambient term accepted⟩

/-- Ordered skip and keep receipts locate the chosen tuple's literal stored live row. -/
theorem tuples_witness [DecidableEq (EdgeKey Symbol Guard)]
    {tuples : List (List (EdgeValue Symbol Guard))}
    {before after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Tuples tuples before rows after)
    (ready : Ready before) (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple)
    (chosen : List (EdgeValue Symbol Guard)) (member : chosen ∈ tuples) (nonempty : chosen ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : ∀ edge ∈ chosen, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
      (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
      (SourceCurrentConjunctionCompletionReads.edgeView edge) term) :
    ∃ row ∈ rows, ∀ requirement ∈ row, ∃ part,
      Accepts (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) requirement part ∧ part.height < term.height := by
  revert accepted member closed resident ready
  induction actual with
  | nil => intro _ _ _ member _; cases member
  | @skip tuple before middle tuples rows after first rest ih =>
      intro ready resident closed member accepted
      rcases List.mem_cons.mp member with same | member
      · subst chosen
        obtain ⟨row, impossible, _⟩ := tuple_witness first ready (resident tuple List.mem_cons_self)
          (closed tuple List.mem_cons_self) nonempty formulas solver ambient term accepted
        cases impossible
      · have own := first.verified ready (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self)
        exact ih own.1.ready
          (fun tuple member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap own.1.keeps.growth
            edge (resident tuple (List.mem_cons_of_mem _ member) edge included))
          (fun tuple member => closed tuple (List.mem_cons_of_mem _ member)) member accepted
  | @keep tuple before row middle tuples rows after first rest ih =>
      intro ready resident closed member accepted
      rcases List.mem_cons.mp member with same | member
      · subst chosen
        obtain ⟨actualRow, same, witnesses⟩ := tuple_witness first ready (resident tuple List.mem_cons_self)
          (closed tuple List.mem_cons_self) nonempty formulas solver ambient term accepted
        have equal : row = actualRow := Option.some.inj same
        subst actualRow
        exact ⟨row, List.mem_cons_self, witnesses⟩
      · have own := first.verified ready (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self)
        obtain ⟨chosenRow, included, witnesses⟩ := ih own.1.ready
          (fun tuple member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap own.1.keeps.growth
            edge (resident tuple (List.mem_cons_of_mem _ member) edge included))
          (fun tuple member => closed tuple (List.mem_cons_of_mem _ member)) member accepted
        exact ⟨chosenRow, List.mem_cons_of_mem _ included, witnesses⟩

/-- Actual completed row allocation derives local coverage from original common acceptance. -/
theorem rows_coverage [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {nodes : List (Value Symbol Guard)}
    {before after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Rows nodes before rows after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    Coverage (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) nodes rows := by
  intro term accepted
  cases actual with
  | @run edges heap rows after before reads tuples =>
      obtain ⟨chosen, member, nonempty, _, _, common⟩ :=
        SourceCurrentConjunctionTuples.accepted_tuple (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed formulas solver ambient term accepted
      have own := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have middle : Ready (⟨heap, before.equality⟩ : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula) :=
        ⟨own.1.semantic, own.1.costs, ready.valid, own.1.annotations⟩
      exact tuples_witness tuples middle
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed tuple member).2.1)
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed tuple member).2.2)
        chosen member nonempty formulas solver ambient term common
end ActualGuards
end MicroCFTA.SourceCurrentConjunctionRowsSoundness
