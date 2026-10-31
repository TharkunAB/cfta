import MicroCFTA.SourceCurrentConjunctionRowsWorker
import MicroCFTA.SourceEqualityProjectionWorkerEffects

set_option autoImplicit false
open scoped Classical

/-! Physical effects of actual current conjunction rows. -/
namespace MicroCFTA.SourceCurrentConjunctionRowsWorkerEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConjunctionRowsWorker
variable {Formula A B : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint
local notation "Heap" => InternedConstructorTemplates.State Symbol (Guard Formula)
private def LP (values : List (Value Symbol (Guard Formula))) (heap : Heap) := Values heap values ∧ ClosedValues values
private def RP (rows : List (List (Value Symbol (Guard Formula)))) (heap : Heap) := ∀ row ∈ rows, LP row heap
private def EP (edges : List (EdgeValue Symbol (Guard Formula))) (heap : Heap) := Edges heap edges ∧ ClosedEdges edges
private structure Verified (before : Heap) (actual : Outcome Symbol Formula A) (post : A → Heap → Prop) : Prop where
  semantic : SemanticHeap actual.state.heap
  covered : Covered [] actual.state.heap
  growth : Grows before actual.state.heap
  history : Extends before.nodes.issued actual.state.heap.nodes.issued
  result : ∀ value after, actual = .done value after → post value after.heap
private theorem Verified.extend {before middle : Heap} {actual : Outcome Symbol Formula A} {post : A → Heap → Prop}
    (v : Verified middle actual post) (growth : Grows before middle) (history : Extends before.nodes.issued middle.nodes.issued) : Verified before actual post :=
  ⟨v.semantic, v.covered, grows_trans growth v.growth, extends_trans history v.history, v.result⟩
private theorem pure_verified (state : Physical Symbol Formula) (semantic : SemanticHeap state.heap) (covered : Covered [] state.heap)
    (value : A) (post : A → Heap → Prop) (valid : post value state.heap) : Verified state.heap (.done value state) post :=
  ⟨semantic, covered, grows_refl _, extends_refl _, by intro result after same; cases same; exact valid⟩
private theorem fail_verified (state : Physical Symbol Formula) (semantic : SemanticHeap state.heap) (covered : Covered [] state.heap)
    (fault : Fault) (post : A → Heap → Prop) : Verified state.heap (.failed fault state) post :=
  ⟨semantic, covered, grows_refl _, extends_refl _, by intro result after same; cases same⟩
private theorem bind_verified {before : Heap} {actual : Outcome Symbol Formula A} {post : A → Heap → Prop}
    {next : A → Physical Symbol Formula → Outcome Symbol Formula B} {final : B → Heap → Prop}
    (first : Verified before actual post) (later : ∀ value after, Verified before (.done value after) post → Verified after.heap (next value after) final) :
    Verified before (actual.bind next) final := by
  cases actual with
  | done value after => exact (later value after first).extend first.growth first.history
  | failed fault after => exact ⟨first.semantic, first.covered, first.growth, first.history, by intro value state same; cases same⟩
private theorem lp_grows {before after : Heap} {values : List (Value Symbol (Guard Formula))}
    (valid : LP values before) (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued) : LP values after :=
  ⟨fun value member => (valid.1 value member).grows before after growth history, valid.2⟩
private theorem ep_grows {before after : Heap} {edges : List (EdgeValue Symbol (Guard Formula))}
    (valid : EP edges before) (growth : Grows before after) : EP edges after :=
  ⟨fun edge member => InternedEdgeResidency.edge_grows before after growth edge (valid.1 edge member), valid.2⟩
private theorem canonical_ready (heap : Heap) (values : List (Value Symbol (Guard Formula))) (valid : LP values heap) :
    LP (SourceCurrentConjunctionRequirements.canonical values) heap := by
  have member : ∀ value ∈ SourceCurrentConjunctionRequirements.canonical values, Available heap value ∧ value.free = [] := by
    intro value included; unfold SourceCurrentConjunctionRequirements.canonical at included; split at included
    · have same := List.mem_singleton.mp included; subst value; exact ⟨empty_available heap, rfl⟩
    · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp included
      have found := SourceEqualityNeededMap.lookup_of_mem entry.1 _ entry.2 (SourceCurrentConjunctionMap.fromList_ascending _ values) present
      have origin := (SourceCurrentConjunctionMap.fromList_origin _ values entry.1 entry.2 found).1
      exact ⟨valid.1 _ origin, valid.2 _ origin⟩
  exact ⟨fun value included => (member value included).1, fun value included => (member value included).2⟩
private theorem projections_verified (p h : Nat) (jobs : List (Job Symbol Formula)) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (inputs : SourceCurrentConjunctionCompletionReads.Inputs before.heap jobs) :
    Verified before.heap (projections p h jobs before) LP := by
  induction jobs generalizing before with
  | nil => exact pure_verified before semantic covered [] _ ⟨(by intro value member; cases member), (by intro value member; cases member)⟩
  | cons job jobs ih =>
    rcases job with ⟨forest, path⟩
    have first := SourceEqualityProjectionWorkerPhysical.forest_effects p h (path.map Int.ofNat) forest before.heap semantic covered (inputs _ List.mem_cons_self).1 (inputs _ List.mem_cons_self).2
    cases actual : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
    | done value heap =>
      simp only [actual, SourceEqualityProjectionWorkerPhysical.reached] at first
      rcases first with ⟨sem, cov, growth, history, own⟩
      simp only [projections, actual]
      apply (bind_verified (ih ⟨heap, before.equality⟩ sem cov (fun job member => lp_grows (inputs job (List.mem_cons_of_mem _ member)) growth history)) ?_).extend growth history
      intro values after tail; apply pure_verified after tail.semantic tail.covered (value :: values) LP
      constructor
      · intro child member; rcases List.mem_cons.mp member with same | rest
        · subst child; exact own.1.grows _ _ tail.growth tail.history
        · exact (tail.result _ _ rfl).1 child rest
      · intro child member; rcases List.mem_cons.mp member with same | rest
        · subst child; exact own.2
        · exact (tail.result _ _ rfl).2 child rest
    | pending key heap | unresolved key heap | exhausted key heap =>
      simp only [actual, SourceEqualityProjectionWorkerPhysical.reached] at first
      simp only [projections, actual]
      exact ⟨first.1, first.2.1, first.2.2.1, first.2.2.2.1, by intro value after same; cases same⟩
private theorem exposures_verified (h : Nat) (nodes : List (Value Symbol (Guard Formula))) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (inputs : LP nodes before.heap) :
    Verified before.heap (exposures h nodes before) (fun rows heap => ∀ edges ∈ rows, EP edges heap) := by
  induction nodes generalizing before with
  | nil => exact pure_verified before semantic covered [] _ (by intro edges member; cases member)
  | cons value nodes ih =>
    have first := MergedFreshOrdinaryColdEffects.nodeEdges_verified h value before.heap semantic covered (inputs.1 value List.mem_cons_self) (inputs.2 value List.mem_cons_self)
    cases actual : MergedFreshOrdinaryExposure.nodeEdges h value before.heap with
    | done edges heap =>
      rw [actual] at first; simp only [exposures, actual]
      have own : EP edges heap := ⟨first.edges _ _ rfl, first.closed _ _ rfl⟩
      apply (bind_verified (ih ⟨heap, before.equality⟩ first.semantic first.covered (lp_grows ⟨fun child member => inputs.1 child (List.mem_cons_of_mem _ member), fun child member => inputs.2 child (List.mem_cons_of_mem _ member)⟩ first.growth first.history)) ?_).extend first.growth first.history
      intro remaining after tail; apply pure_verified after tail.semantic tail.covered (edges :: remaining) _
      intro selected member; rcases List.mem_cons.mp member with same | rest
      · subst selected; exact ep_grows own tail.growth
      · exact tail.result _ _ rfl selected rest
    | pending key heap | unresolved key heap => rw [actual] at first; exact False.elim first.outcome
    | exhausted heap => rw [actual] at first; simpa only [exposures, actual, Outcome.state] using (show Verified before.heap (.failed (.exhausted .head) ⟨heap, before.equality⟩) _ from ⟨first.semantic, first.covered, first.growth, first.history, by intro value after same; cases same⟩)
private theorem classes_verified (p h : Nat) (forests : List (List (Value Symbol (Guard Formula)))) (constraints : EqualityNormalize.Constraints)
    (before : Physical Symbol Formula) (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (inputs : RP forests before.heap) :
    Verified before.heap (classes p h forests constraints before) RP := by
  induction constraints generalizing before with
  | nil => exact pure_verified before semantic covered [] _ (by intro row member; cases member)
  | cons paths constraints ih =>
    simp only [classes]; apply bind_verified (projections_verified p h _ before semantic covered (SourceCurrentConjunctionCompletionReads.jobs_inputs _ forests paths (fun row member => (inputs row member).1) (fun row member => (inputs row member).2)))
    intro projected middle first; apply bind_verified (ih middle first.semantic first.covered (fun row member => lp_grows (inputs row member) first.growth first.history))
    intro remaining after tail; apply pure_verified after tail.semantic tail.covered _ RP
    intro row member; rcases List.mem_cons.mp member with same | rest
    · subst row; exact canonical_ready _ projected (lp_grows (first.result _ _ rfl) tail.growth tail.history)
    · exact tail.result _ _ rfl row rest
private theorem children_ready (heap : Heap) (edges : List (EdgeValue Symbol (Guard Formula))) (semantic : SemanticHeap heap) (inputs : EP edges heap) : RP (edges.map EdgeValue.children) heap := by
  intro children member; obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  exact ⟨semantic.1.normal.facts.cached.edges edge.entry.key edge (inputs.1 edge present), inputs.2 edge present⟩
private theorem requirements_verified (p h : Nat) (edges : List (EdgeValue Symbol (Guard Formula))) (constraints : EqualityNormalize.Constraints)
    (before : Physical Symbol Formula) (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (inputs : EP edges before.heap) :
    Verified before.heap (requirements p h edges constraints before) RP := by
  unfold requirements; apply bind_verified (classes_verified p h _ constraints before semantic covered (children_ready _ edges semantic inputs))
  intro rows after first; apply pure_verified after first.semantic first.covered _ RP
  intro row member; rcases List.mem_append.mp member with column | own
  · obtain ⟨values, present, rfl⟩ := List.mem_map.mp column
    apply canonical_ready; constructor
    · intro value included; obtain ⟨forest, forestIn, valueIn⟩ := MergedPhysicalGroupEdges.columns_member _ _ values present value included
      exact (children_ready _ edges first.semantic (ep_grows inputs first.growth) forest forestIn).1 value valueIn
    · intro value included; obtain ⟨forest, forestIn, valueIn⟩ := MergedPhysicalGroupEdges.columns_member _ _ values present value included
      exact (children_ready _ edges first.semantic (ep_grows inputs first.growth) forest forestIn).2 value valueIn
  · exact first.result _ _ rfl row own
private theorem tuple_verified (p h : Nat) (edges : List (EdgeValue Symbol (Guard Formula))) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (inputs : EP edges before.heap) :
    Verified before.heap (tuple p h edges before) (fun row heap => match row with | none => True | some rows => RP rows heap) := by
  unfold tuple; generalize folded : SourceCurrentConjunctionEquality.fold edges before.equality = actual
  rcases actual with ⟨answer, equality⟩; dsimp only
  cases answer with
  | error message => exact fail_verified ⟨before.heap, equality⟩ semantic covered _ _
  | ok value => cases value with
    | none => exact fail_verified ⟨before.heap, equality⟩ semantic covered _ _
    | some value =>
      dsimp only
      cases selected : SourceEqualityInheritedPayload.classes value.payload with
      | none =>
        apply pure_verified ⟨before.heap, equality⟩ semantic covered none
        trivial
      | some constraints =>
        apply bind_verified (requirements_verified p h edges constraints ⟨before.heap, equality⟩ semantic covered inputs)
        intro rows after first; exact pure_verified after first.semantic first.covered (some rows) _ (first.result _ _ rfl)
private theorem tuples_verified (p h : Nat) (tuples : List (List (EdgeValue Symbol (Guard Formula)))) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (inputs : ∀ edges ∈ tuples, EP edges before.heap) :
    Verified before.heap (SourceCurrentConjunctionRowsWorker.tuples p h tuples before) (fun rows heap => ∀ row ∈ rows, RP row heap) := by
  induction tuples generalizing before with
  | nil => exact pure_verified before semantic covered [] _ (by intro row member; cases member)
  | cons edges remaining ih =>
    simp only [SourceCurrentConjunctionRowsWorker.tuples]; apply bind_verified (tuple_verified p h edges before semantic covered (inputs edges List.mem_cons_self))
    intro row middle first; apply bind_verified (ih middle first.semantic first.covered (fun edges member => ep_grows (inputs edges (List.mem_cons_of_mem _ member)) first.growth))
    intro rows after tail; apply pure_verified after tail.semantic tail.covered _ _
    cases row with
    | none => exact tail.result _ _ rfl
    | some requirements =>
      intro selected member; rcases List.mem_cons.mp member with same | rest
      · subst selected; intro nodes included; exact lp_grows (first.result _ _ rfl nodes included) tail.growth tail.history
      · exact tail.result _ _ rfl selected rest
private theorem rows_verified (p h : Nat) (nodes : List (Value Symbol (Guard Formula))) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (inputs : LP nodes before.heap) :
    Verified before.heap (rows p h nodes before) (fun rows heap => ∀ row ∈ rows, RP row heap) := by
  unfold rows; apply bind_verified (exposures_verified h nodes before semantic covered inputs)
  intro edges after first; apply tuples_verified p h _ after first.semantic first.covered
  intro tuple member; constructor
  · intro edge included; obtain ⟨row, rowIn, edgeIn⟩ := List.mem_flatten.mp (SourceCurrentConjunctionTuples.tuples_members edges tuple member edge included)
    exact (first.result _ _ rfl row rowIn).1 edge edgeIn
  · intro edge included; obtain ⟨row, rowIn, edgeIn⟩ := List.mem_flatten.mp (SourceCurrentConjunctionTuples.tuples_members edges tuple member edge included)
    exact (first.result _ _ rfl row rowIn).2 edge edgeIn
/-- Every actual rows outcome retains physical heap effects. Completed rows have closed available values. -/
theorem rows_effects (p h : Nat) (nodes : List (Value Symbol (Guard Formula))) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    let actual := rows p h nodes before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued ∧
      match actual with | .done requirements after => ∀ row ∈ requirements, ∀ nodes ∈ row, Values after.heap nodes ∧ ClosedValues nodes | .failed _ _ => True := by
  have checked := rows_verified p h nodes before semantic covered ⟨available, closed⟩
  refine ⟨checked.semantic, checked.covered, checked.growth, checked.history, ?_⟩
  cases actual : rows p h nodes before with
  | done requirements after => exact checked.result _ _ actual
  | failed fault after => trivial
end MicroCFTA.SourceCurrentConjunctionRowsWorkerEffects
