import MicroCFTA.SourceCurrentConjunctionRequirements

/-!
# Smaller accepted witnesses for actual conjunction requirements

The proof follows the actual projection graph for each class. Original
forest acceptance and class satisfaction derive one common projected
subtree. No global project function or accepted-result oracle is assumed.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementsSoundness
open Language EqualityNormalize EqualityReduction InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionCompletionReads (Effects Projections jobs Inputs projection_included)
open SourceCurrentConjunctionRequirements
open SourceCurrentConjunctionEmptinessRows (Accepts)
open InternedGuardedLanguage (meaning)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap

/-- Each actual projection keeps the same accepted subtree of its original forest. -/
theorem projections_common [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {jobs : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)}
    {before after : State Symbol Guard} {projected : List (Value Symbol Guard)}
    (actual : Projections jobs before projected after) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before) (inputs : Inputs before jobs)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (original : ∀ job ∈ jobs, All₂ (meaning holds ambient) job.1 terms)
    (proper : ∀ job ∈ jobs, job.2 ≠ [])
    (selected : ∀ job ∈ jobs, (Term.node symbol terms).atPath job.2 = some part) :
    ∀ value ∈ projected, meaning holds ambient value part := by
  induction actual with
  | nil => simp
  | @cons forest path before value middle remaining values after first rest ih =>
      have ownInputs := inputs _ List.mem_cons_self
      have own := SourceEqualityProjectionCosts.forest_effects first semantic costs ownInputs.1
      have ownFields := SourceEqualityAnnotationProjection.forest annotation first semantic ownInputs.1 ownInputs.2 fields
      have accepted := projection_included first semantic ownInputs.1 ownInputs.2
        (proper _ List.mem_cons_self) holds ambient symbol terms part
        (original _ List.mem_cons_self) (selected _ List.mem_cons_self)
      have later := ih own.2.1 own.2.2.1 ownFields
        (Inputs.keeps (fun job member => inputs job (List.mem_cons_of_mem _ member)) own.1)
        (fun job member => original job (List.mem_cons_of_mem _ member))
        (fun job member => proper job (List.mem_cons_of_mem _ member))
        (fun job member => selected job (List.mem_cons_of_mem _ member))
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · exact accepted
      · exact later result member

/-- One active satisfied class derives a smaller common witness for its actual returned requirement. -/
theorem class_witness [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (forests : List (List (Value Symbol Guard))) (paths : Class)
    {before after : State Symbol Guard} {projected : List (Value Symbol Guard)}
    (actual : Projections (jobs forests paths) before projected after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (inputs : RowsReady before forests) (nonempty : forests ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (original : ∀ forest ∈ forests, All₂ (meaning holds ambient) forest terms)
    (active : Nontrivial paths) (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ part, Accepts (meaning holds ambient) (canonical projected) part ∧
      part.height < (Term.node symbol terms).height := by
  obtain ⟨first, firstIn, second, secondIn, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstIn, second, secondIn, different⟩
  obtain ⟨part, found⟩ := class_member_exists (.node symbol terms) paths active satisfied first firstIn
  have proper := class_nonroot paths active (.node symbol terms) satisfied
  have jobInputs := SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
    (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2)
  have checked := actual.verified annotation semantic costs fields jobInputs
  have accepted := projections_common annotation actual semantic costs fields jobInputs holds ambient symbol terms part
    (by
      intro job member
      obtain ⟨forest, forestIn, pathIn⟩ := List.mem_flatMap.mp member
      obtain ⟨path, _, rfl⟩ := List.mem_map.mp pathIn
      exact original forest forestIn)
    (by
      intro job member
      obtain ⟨forest, _, pathIn⟩ := List.mem_flatMap.mp member
      obtain ⟨path, actualPathIn, rfl⟩ := List.mem_map.mp pathIn
      exact proper path actualPathIn)
    (by
      intro job member
      obtain ⟨forest, _, pathIn⟩ := List.mem_flatMap.mp member
      obtain ⟨path, actualPathIn, rfl⟩ := List.mem_map.mp pathIn
      obtain ⟨common, firstFound, pathFound⟩ := class_pair_equal (.node symbol terms) paths active satisfied first path firstIn actualPathIn
      have same := Option.some.inj (firstFound.symm.trans found)
      simpa only [same] using pathFound)
  have jobNonempty : jobs forests paths ≠ [] := by
    cases forests with
    | nil => exact False.elim (nonempty rfl)
    | cons forest rest =>
        have member : (forest, first) ∈ jobs (forest :: rest) paths :=
          List.mem_flatMap.mpr ⟨forest, List.mem_cons_self, List.mem_map.mpr ⟨first, firstIn, rfl⟩⟩
        intro same
        simp only [same, List.not_mem_nil] at member
  have projectedNonempty : projected ≠ [] := by
    intro same
    have lengths := actual.length
    rw [same] at lengths
    exact jobNonempty (List.length_eq_zero_iff.mp lengths.symm)
  refine ⟨part, (canonical_accepts projected after checked.1.semantic checked.2.1 checked.2.2 holds ambient part).mpr
    ⟨projectedNonempty, accepted⟩, ?_⟩
  have bound := atPath_height_bound (.node symbol terms) part first found
  have positive : 0 < first.length := by
    cases first with
    | nil => exact False.elim (proper [] firstIn rfl)
    | cons => simp
  omega

/-- Actual class-list scheduling preserves every smaller common witness in source class order. -/
theorem classes_witness [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {forests : List (List (Value Symbol Guard))} {classes : Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : ClassRequirements forests classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (inputs : RowsReady before forests) (nonempty : forests ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (original : ∀ forest ∈ forests, All₂ (meaning holds ambient) forest terms)
    (active : Active classes) (satisfied : Satisfies (.node symbol terms) classes) :
    ∀ requirement ∈ requirements, ∃ part, Accepts (meaning holds ambient) requirement part ∧
      part.height < (Term.node symbol terms).height := by
  induction actual with
  | nil => simp
  | @cons paths before projected middle classes requirements after first rest ih =>
      have own := first.verified annotation semantic costs fields
        (SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
          (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2))
      have firstWitness := class_witness annotation forests paths first semantic costs fields inputs nonempty
        holds ambient symbol terms original (active paths List.mem_cons_self) (satisfied paths List.mem_cons_self)
      have later := ih own.1.semantic own.1.costs own.1.annotations
        (fun forest member => ⟨fun value included => own.1.keeps.available value ((inputs forest member).1 value included),
          (inputs forest member).2⟩)
        (fun paths member => active paths (List.mem_cons_of_mem _ member))
        (fun paths member => satisfied paths (List.mem_cons_of_mem _ member))
      intro requirement member
      rcases List.mem_cons.mp member with rfl | member
      · exact firstWitness
      · exact later requirement member

/-- All actual tuple requirements have a strictly smaller accepted common term. -/
theorem requirements_witness [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {tuple : List (EdgeValue Symbol Guard)} {classes : Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Requirements tuple classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (nonempty : tuple ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (original : ∀ edge ∈ tuple, All₂ (meaning holds ambient) edge.children terms)
    (active : Active classes) (satisfied : Satisfies (.node symbol terms) classes) :
    ∀ requirement ∈ requirements, ∃ part, Accepts (meaning holds ambient) requirement part ∧
      part.height < (Term.node symbol terms).height := by
  have forests : ∀ forest ∈ tuple.map EdgeValue.children, All₂ (meaning holds ambient) forest terms := by
    intro forest member
    obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
    exact original edge edgeIn
  have forestsNonempty : tuple.map EdgeValue.children ≠ [] := by simpa using nonempty
  have commonArity : arity tuple = terms.length := by
    cases tuple with
    | nil => exact False.elim (nonempty rfl)
    | cons edge rest => exact (original edge List.mem_cons_self).length_eq
  cases actual with
  | run _ actual =>
      have classWitness := classes_witness annotation actual semantic costs fields
        (tuple_inputs tuple before semantic resident closed) forestsNonempty holds ambient symbol terms forests active satisfied
      intro requirement member
      rcases List.mem_append.mp member with column | group
      · obtain ⟨originalColumn, columnIn, rfl⟩ := List.mem_map.mp column
        have acceptedColumns := SourceCurrentConjunctionEmptinessRows.columns_accept
          (meaning holds ambient) (tuple.map EdgeValue.children) forestsNonempty terms forests
        have columnIn' : originalColumn ∈ MergedAlternativesGroups.columns (tuple.map EdgeValue.children) terms.length := by
          simpa only [columns, commonArity] using columnIn
        obtain ⟨part, partIn, accepted⟩ := SymbolicSmartRows.all₂_child (Accepts (meaning holds ambient)) _ terms
          acceptedColumns originalColumn columnIn'
        have columnInputs := columns_ready tuple before semantic resident closed originalColumn columnIn
        refine ⟨part, (canonical_accepts originalColumn before semantic columnInputs.1 columnInputs.2 holds ambient part).mpr accepted, ?_⟩
        have bound := height_le_forestHeight terms part partIn
        simpa only [Term.height, forestHeight] using Nat.lt_succ_of_le bound
      · exact classWitness requirement group

section ActualGuards
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual combined-class readback removes the separate satisfaction and active-class premises. -/
theorem accepted_tuple [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {tuple : List (EdgeValue Symbol Guard)} {classes : Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Requirements tuple classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (nonempty : tuple ≠ [])
    (live : SourceCurrentConjunctionEmptinessRows.combined
      (tuple.map SourceCurrentConjunctionCompletionReads.edgeView) = some classes)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
      (meaning holds ambient) (SourceCurrentConjunctionCompletionReads.edgeView edge) term) :
    ∀ requirement ∈ requirements, ∃ part, Accepts (meaning holds ambient) requirement part ∧ part.height < term.height := by
  have allAccepted : ∀ edge ∈ tuple.map SourceCurrentConjunctionCompletionReads.edgeView,
      SourceCurrentConjunctionEmptinessRows.EdgeAccepts (meaning holds ambient) edge term := by
    intro view member
    obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
    exact accepted edge edgeIn
  have satisfied := (SourceCurrentConjunctionEmptinessRows.combined_sat
    (tuple.map SourceCurrentConjunctionCompletionReads.edgeView) term).mpr
    (fun edge member => (allAccepted edge member).choose_spec.2.2)
  rw [live] at satisfied
  have active := SourceCurrentConjunctionEmptinessRows.combined_active
    (tuple.map SourceCurrentConjunctionCompletionReads.edgeView) classes live
  cases tuple with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      obtain ⟨terms, shape, _, _⟩ := accepted first List.mem_cons_self
      subst term
      apply requirements_witness annotation actual semantic costs fields resident closed nonempty holds ambient
        first.entry.key.symbol terms ?_ active satisfied
      intro edge member
      obtain ⟨other, same, forest, _⟩ := accepted edge member
      have equal := (Term.node.inj same).2
      change All₂ (meaning holds ambient) edge.children other at forest
      simpa only [← equal] using forest

end ActualGuards
end MicroCFTA.SourceCurrentConjunctionRequirementsSoundness
