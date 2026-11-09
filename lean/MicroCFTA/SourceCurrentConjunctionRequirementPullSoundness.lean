import MicroCFTA.SourceCurrentConjunctionRequirementPullExecution
import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual
import MicroCFTA.SourceCurrentConjunctionRequirementsSoundness

/-!
# Common witnesses in deferred class requirements

The cursor retains one accepted subtree in its collected values and pending
jobs. Each actual singleton read preserves that subtree. Such a read cannot
return Empty. The proof follows the actual finite run and does not execute
an unused suffix after an arbitrary Empty result.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementPullSoundness
open Language EqualityNormalize EqualityReduction
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionRowsWorker (Physical Outcome Job)
open SourceCurrentConjunctionRequirementPull (Cursor projection run classConjunction start)
open SourceCurrentConjunctionCompletionReads (Inputs jobs projection_included)
open SourceCurrentConjunctionRequirements (canonical canonical_accepts isEmpty)
open SourceCurrentConjunctionEmptinessRows (Accepts)
open InternedGuardedLanguage (meaning)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap

/-- The current prefix and pending source jobs share one proper subtree. -/
structure Common (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (cursor : Cursor Symbol Formula) : Prop where
  nonempty : cursor.collected ≠ [] ∨ cursor.pending ≠ []
  collected : ∀ value ∈ cursor.collected, meaning holds ambient value part
  pending : ∀ job ∈ cursor.pending, All₂ (meaning holds ambient) job.1 terms ∧
    job.2 ≠ [] ∧ (Term.node symbol terms).atPath job.2 = some part

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- An actual singleton read retains its accepted subtree and excludes Empty. -/
theorem projection_common {p h : Nat} {job : Job Symbol Formula}
    {before after : Physical Symbol Formula} {value : Node}
    (actual : projection p h job before = .done value after)
    (semantic : SemanticReady before.heap) (available : Values before.heap job.1)
    (closed : ClosedValues job.1)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (original : All₂ (meaning holds ambient) job.1 terms) (proper : job.2 ≠ [])
    (selected : (Term.node symbol terms).atPath job.2 = some part) :
    meaning holds ambient value part ∧ isEmpty value = false := by
  have singleton : SourceCurrentConjunctionRowsWorker.projections p h [job] before =
      .done [value] after := by
    rw [← SourceCurrentConjunctionRequirementPull.projection_singleton, actual]
    rfl
  have graph := (SourceCurrentConjunctionRowsWorkerActual.projections_graph singleton).1
  rcases job with ⟨forest, path⟩
  cases graph with
  | cons first rest =>
      cases rest
      have accepted := projection_included first semantic available closed proper holds ambient
        symbol terms part original selected
      have different : value ≠ .empty := by
        intro same
        subst value
        exact (InternedGuardedLanguage.laws holds ambient).empty part accepted
      refine ⟨accepted, ?_⟩
      cases value <;> first
        | exact False.elim (different rfl)
        | rfl

/-- A successful finite cursor returns its common witness in the actual canonical result. -/
theorem run_common (annotation : Guard → Prop) {p h : Nat} {cursor : Cursor Symbol Formula}
    {before after : Physical Symbol Formula} {nodes : List Node}
    (actual : run p h cursor before = .done nodes after)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (fields : AnnotationHeap annotation before.heap)
    (collectedValues : Values before.heap cursor.collected)
    (collectedClosed : ClosedValues cursor.collected) (inputs : Inputs before.heap cursor.pending)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (common : Common holds ambient symbol terms part cursor) :
    Accepts (meaning holds ambient) nodes part := by
  rcases cursor with ⟨pending, collected⟩
  induction pending generalizing collected before after nodes with
  | nil =>
      rw [SourceCurrentConjunctionRequirementPull.run_nil] at actual
      have returned := Outcome.done.inj actual
      rw [← returned.1]
      apply (canonical_accepts collected before.heap semantic collectedValues collectedClosed
        holds ambient part).mpr
      refine ⟨?_, common.collected⟩
      rcases common.nonempty with present | impossible
      · exact present
      · exact False.elim (impossible rfl)
  | cons job remaining ih =>
      have ownInputs := inputs job List.mem_cons_self
      have ownCommon := common.pending job List.mem_cons_self
      cases projected : projection p h job before with
      | failed fault middle =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job remaining collected before
            middle fault projected] at actual
          cases actual
      | done value middle =>
          have accepted := projection_common projected semantic ownInputs.1 ownInputs.2
            holds ambient symbol terms part ownCommon.1 ownCommon.2.1 ownCommon.2.2
          have singleton : SourceCurrentConjunctionRowsWorker.projections p h [job] before =
              .done [value] middle := by
            rw [← SourceCurrentConjunctionRequirementPull.projection_singleton, projected]
            rfl
          have graph := (SourceCurrentConjunctionRowsWorkerActual.projections_graph singleton).1
          have checked := graph.verified annotation semantic costs fields (by
            intro selected member
            cases List.mem_singleton.mp member
            exact ownInputs)
          have nextValues : Values middle.heap (collected ++ [value]) := by
            intro selected member
            rcases List.mem_append.mp member with old | newest
            · exact checked.1.keeps.available selected (collectedValues selected old)
            · exact checked.2.1 selected newest
          have nextClosed : ClosedValues (collected ++ [value]) := by
            intro selected member
            rcases List.mem_append.mp member with old | newest
            · exact collectedClosed selected old
            · exact checked.2.2 selected newest
          have nextInputs : Inputs middle.heap remaining := Inputs.keeps
            (fun selected member => inputs selected (List.mem_cons_of_mem _ member)) checked.1.keeps
          have nextCommon : Common holds ambient symbol terms part
              (⟨remaining, collected ++ [value]⟩ : Cursor Symbol Formula) := by
            refine ⟨Or.inl ?_, ?_, ?_⟩
            · intro empty
              have length := congrArg List.length empty
              simp only [List.length_append, List.length_singleton, List.length_nil] at length
              omega
            · intro selected member
              rcases List.mem_append.mp member with old | newest
              · exact common.collected selected old
              · cases List.mem_singleton.mp newest
                exact accepted.1
            · intro selected member
              exact common.pending selected (List.mem_cons_of_mem _ member)
          rw [SourceCurrentConjunctionRequirementPull.run_more p h job remaining collected before
            middle value projected accepted.2] at actual
          exact ih checked.1.semantic checked.1.costs checked.1.annotations
            (collected ++ [value]) actual nextValues nextClosed nextInputs nextCommon

/-- An active satisfied source class yields a strictly smaller common accepted subtree. -/
theorem classConjunction_witness (annotation : Guard → Prop)
    (forests : List (List Node)) (paths : Class) {p h : Nat}
    {before after : Physical Symbol Formula} {nodes : List Node}
    (actual : classConjunction p h forests paths before = .done nodes after)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (fields : AnnotationHeap annotation before.heap)
    (inputs : SourceCurrentConjunctionRequirements.RowsReady before.heap forests)
    (nonempty : forests ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (original : ∀ forest ∈ forests, All₂ (meaning holds ambient) forest terms)
    (active : Nontrivial paths) (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ part, Accepts (meaning holds ambient) nodes part ∧
      part.height < (Term.node symbol terms).height := by
  obtain ⟨first, firstIn, second, secondIn, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstIn, second, secondIn, different⟩
  obtain ⟨part, found⟩ := class_member_exists (.node symbol terms) paths active satisfied first firstIn
  have proper := class_nonroot paths active (.node symbol terms) satisfied
  have jobInputs := SourceCurrentConjunctionCompletionReads.jobs_inputs before.heap forests paths
    (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2)
  have jobNonempty : jobs forests paths ≠ [] := by
    cases forests with
    | nil => exact False.elim (nonempty rfl)
    | cons forest rest =>
        have member : (forest, first) ∈ jobs (forest :: rest) paths :=
          List.mem_flatMap.mpr ⟨forest, List.mem_cons_self, List.mem_map.mpr ⟨first, firstIn, rfl⟩⟩
        intro empty
        simp only [empty, List.not_mem_nil] at member
  have common : Common holds ambient symbol terms part (start forests paths) := by
    refine ⟨Or.inr jobNonempty, ?_, ?_⟩
    · intro value member
      cases member
    · intro job member
      obtain ⟨forest, forestIn, pathIn⟩ := List.mem_flatMap.mp member
      obtain ⟨path, actualPathIn, rfl⟩ := List.mem_map.mp pathIn
      refine ⟨original forest forestIn, proper path actualPathIn, ?_⟩
      obtain ⟨common, firstFound, pathFound⟩ := class_pair_equal (.node symbol terms) paths active
        satisfied first path firstIn actualPathIn
      have same := Option.some.inj (firstFound.symm.trans found)
      simpa only [same] using pathFound
  have accepted := run_common annotation actual semantic costs fields
    (by intro value member; cases member)
    (by intro value member; cases member)
    jobInputs holds ambient symbol terms part common
  refine ⟨part, accepted, ?_⟩
  have bound := atPath_height_bound (.node symbol terms) part first found
  have positive : 0 < first.length := by
    cases first with
    | nil => exact False.elim (proper [] firstIn rfl)
    | cons => simp
  omega

end MicroCFTA.SourceCurrentConjunctionRequirementPullSoundness
