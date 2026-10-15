import MicroCFTA.SourceEqualityPartialGraphLaws

/-!
# Concrete constructor cases of the recursive graph induction

The local cases use actual native effects and actual recursive child
conclusions. They derive the next physical scopes and public language laws.
The mutual graph theorem supplies those recursive conclusions.
-/
namespace MicroCFTA.SourceEqualityPartialGraphLaws
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityRequiredCache
open SourceEqualityPartialScope
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (ambient : InternedGuardedLanguage.Env Symbol)
local notation "meaning" => InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient
local notation "edgeMeaning" => InternedGuardedLanguage.edgeMeaning (acceptsConstraint formulas solver) ambient

/-- Identity source branches retain every node conclusion without recursive calls. -/
theorem identity_node (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard) (before : NativeState width Symbol Guard) :
    NodeLaw formulas solver ambient inherited value before value before := by
  intro scope available closed
  exact ⟨scope, pure_keeps _ scope.native.semantic.ready, available, closed, fun _ => ⟨id, fun _ => Iff.rfl⟩⟩

/-- A real Mu request receipt has exact cleanup and unchanged scope from the retained physical probes. -/
theorem binder_node {entry body depth ordinary result heap inherited} {before : NativeState width Symbol Guard}
    (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.machine.heap = .done result heap) :
    NodeLaw formulas solver ambient inherited (.mu entry body depth ordinary) before result (advanceHeap before heap) := by
  intro scope available closed
  have clean := InternedFreshOrdinaryProbeHeap.resident before.machine.heap scope.probes entry body depth ordinary available
  have checked := SourceEqualityMuReconstruction.verified entry body depth ordinary before.machine.heap
    scope.native.semantic.ready.semantic.1.normal.facts.coherent available clean (acceptsConstraint formulas solver) ambient
  have parts := InternedNestedConstruction.Outcome.done.inj (checked.1.symm.trans actual)
  cases parts.1; cases parts.2
  exact ⟨scope, pure_keeps _ scope.native.semantic.ready, checked.2.1, checked.2.2.1.trans closed,
    fun term => ⟨fun accepted => (iff_of_eq (congrFun checked.2.2.2 term)).mp accepted,
      fun _ => iff_of_eq (congrFun checked.2.2.2 term)⟩⟩

/-- The actual row conclusion and literal modifyNode derive the complete ordinary node conclusion. -/
theorem ordinary_node {inherited entry edges results depth free} {before middle : NativeState width Symbol Guard}
    (rowsIH : RowsLaw formulas solver ambient inherited edges before results middle) :
    NodeLaw formulas solver ambient inherited (.node entry edges depth free) before
      (SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle).1
      (SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle).2 := by
  intro scope available closed
  have rows := rowsIH scope (resident_edges _ scope.native.semantic.ready.semantic.1.normal.facts.linked _ available.resident)
    (SourceEqualityPartialStepProofs.closed_rows before scope.native entry edges depth free available closed)
  have built := Scope.modify entry edges results depth free middle rows.1 (rows.2.1.available _ available) closed rows.2.2.1 rows.2.2.2.1
    (acceptsConstraint formulas solver) ambient
  refine ⟨built.1, rows.2.1.trans built.2.1, built.2.2.1, built.2.2.2.1, ?_⟩
  intro term
  have output := (built.2.2.2.2 term).trans (SourceEqualityInheritedRowsProofs.meaning_iff (acceptsConstraint formulas solver) ambient results term).symm
  have input := (SourceEqualityPartialNodeRebuild.node_meaning (acceptsConstraint formulas solver) ambient entry edges depth free term).trans
    (SourceEqualityInheritedRowsProofs.meaning_iff (acceptsConstraint formulas solver) ambient edges term).symm
  have law := rows.2.2.2.2 term
  exact ⟨fun accepted => input.mpr (law.1 (output.mp accepted)), fun satisfied => output.trans ((law.2 satisfied).trans input.symm)⟩

/-- Physical guard readback, actual payload combination, and the real child conclusion derive literal edge meaning. -/
theorem edge_continuation {edge : EdgeValue Symbol Guard} {inherited own payload values} {before middle : NativeState width Symbol Guard}
    (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok own)
    (combined : SourceEqualityInheritedPayload.combine inherited own = .ok payload)
    (childrenIH : ChildrenLaw formulas solver ambient payload edge.children before values middle)
    (scope : Scope before) (resident : EdgeResident before.machine.heap edge) (closed : ClosedValues edge.children) :
    let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap
    Scope (advanceHeap middle built.2) ∧ Keeps before.machine.heap built.2 ∧ EdgeResident built.2 built.1 ∧ ClosedValues built.1.children ∧ ∀ term,
      (edgeMeaning built.1 term → edgeMeaning edge term) ∧
      (SourceEqualityPrecheck.Sat term inherited → (edgeMeaning built.1 term ↔ edgeMeaning edge term)) := by
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  have stored := scope.annotations edge.entry.key edge resident
  obtain ⟨actualOwn, actual, _, acceptedOwn⟩ := SourceEqualityInheritedPayload.own_complete formulas solver edge.entry.key.constraint stored
  have same := Except.ok.inj (actual.symm.trans physical)
  subst actualOwn
  have combinedFacts : SourceEqualityDescend.WellFormed payload ∧ ∀ term : Term Symbol, SourceEqualityPrecheck.Sat term payload ↔
      SourceEqualityPrecheck.Sat term inherited ∧ SourceEqualityPrecheck.Sat term own := SourceEqualityInheritedPayload.combine_exact combined
  have children := childrenIH scope (facts.cached.edges edge.entry.key edge resident) closed combinedFacts.1
  have built := Scope.edge middle children.1 edge.entry.key.symbol edge.entry.key.constraint values stored children.2.2.1
  have fields := MergedPhysicalGroupEdges.makeEdge_fields _ children.1.native.semantic.ready.semantic.1.normal.facts
    edge.entry.key.symbol edge.entry.key.constraint values children.2.2.1
  refine ⟨built.1, children.2.1.trans built.2.1, built.2.2.1, ?_, ?_⟩
  · rw [built.2.2.2]
    exact children.2.2.2.1
  · intro term
    rw [InternedGuardedLanguage.edgeMeaning_all, InternedGuardedLanguage.edgeMeaning_all]
    simp only [MergedColdInterpretation.EdgeMeaning, fields.1, fields.2.1, fields.2.2]
    constructor
    · rintro ⟨terms, shape, runs, guard⟩
      exact ⟨terms, shape, (children.2.2.2.2 edge.entry.key.symbol terms).1 runs, guard⟩
    · intro inheritedSat
      constructor
      · rintro ⟨terms, shape, runs, guard⟩
        exact ⟨terms, shape, (children.2.2.2.2 edge.entry.key.symbol terms).1 runs, guard⟩
      · rintro ⟨terms, shape, runs, guard⟩
        have parentSat := (combinedFacts.2 term).mpr ⟨inheritedSat, acceptedOwn term guard⟩
        exact ⟨terms, shape, ((children.2.2.2.2 edge.entry.key.symbol terms).2 (shape ▸ parentSat)).mpr runs, guard⟩

/-- Actual local native narrowing, its real child conclusion, and the real tail conclusion derive the ordered row result. -/
theorem rows_cons {edge narrowedEdge : EdgeValue Symbol Guard} {inherited own payload values edges results}
    {before middle afterChildren after : NativeState width Symbol Guard}
    (narrowed : SourceEqualityPCSNativeEdge.Execution edge inherited before narrowedEdge middle)
    (physical : SourceEqualityPhysicalPayload.own narrowedEdge.entry.key.constraint = .ok own)
    (combined : SourceEqualityInheritedPayload.combine inherited own = .ok payload)
    (childrenIH : ChildrenLaw formulas solver ambient payload narrowedEdge.children middle values afterChildren)
    (restIH : RowsLaw formulas solver ambient inherited edges
      (advanceHeap afterChildren (run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).2) results after) :
    RowsLaw formulas solver ambient inherited (edge :: edges) before
      ((run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).1 :: results) after := by
  intro scope resident closed
  have localPass := scope.narrow narrowed (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) formulas solver ambient
  have head := edge_continuation formulas solver ambient physical combined childrenIH localPass.1 localPass.2.2.1 localPass.2.2.2.1
  have headKeeps := localPass.2.1.trans head.2.1
  have tail := restIH head.1 (fun edge member => edge_grows _ _ headKeeps.growth edge (resident edge (List.mem_cons_of_mem _ member)))
    (fun edge member => closed edge (List.mem_cons_of_mem _ member))
  refine ⟨tail.1, headKeeps.trans tail.2.1, ?_, ?_, ?_⟩
  · intro edge member
    rcases List.mem_cons.mp member with rfl | member
    · exact edge_grows _ _ tail.2.1.growth _ head.2.2.1
    · exact tail.2.2.1 edge member
  · intro edge member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.2.2.2.1
    · exact tail.2.2.2.1 edge member
  · intro term
    have firstLaw := localPass.2.2.2.2 term
    have headLaw := head.2.2.2.2 term
    have restLaw := tail.2.2.2.2 term
    exact ⟨Or.imp (fun accepted => firstLaw.1 (headLaw.1 accepted)) restLaw.1,
      fun satisfied => or_congr ((headLaw.2 satisfied).trans (firstLaw.2 satisfied)) (restLaw.2 satisfied)⟩

end MicroCFTA.SourceEqualityPartialGraphLaws
