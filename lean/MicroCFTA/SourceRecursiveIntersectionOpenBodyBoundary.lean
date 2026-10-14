import MicroCFTA.InternedStoredPreparationCheck
import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.SourceRecursiveIntersectionNativeConstructorCoverage

/-!
# Closed original roots reach an unprepared native binder body

Two actual repaired source builds differ only in their row constraints.
Their native intersection reaches an optional binder whose body contains
an open nested Mu. Thus general completion needs more than preservation
of the existing first-order preparation predicate.
-/
namespace MicroCFTA.SourceRecursiveIntersectionOpenBodyBoundary
open Cache InternedConstructorTemplates InternedBinderProtocol InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceRecursiveIntersectionNative
open SourceRecursiveIntersectionInputView InternedStoredClosedMuCompletion

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-- Both binders retain their own argument, and the inner binder also uses the outer argument. -/
def expression (constraint : Nat) : Syntax Nat Nat :=
  .binder true (.node [.mk 0 constraint [.binder true (.node [.mk 1 constraint [.var 1, .var 0]])]])

/-- Construct both actual roots in one shared source cache. -/
def built : Outcome Nat Nat (Value Nat Nat × Value Nat Nat) :=
  (InternedFreshOrdinaryConstruction.build (expression 1) [] empty).bind fun left after =>
    (InternedFreshOrdinaryConstruction.build (expression 2) [] after).bind fun right final =>
      .done (left, right) final

/-- Keep the actual returned operand pair. The pending branch is excluded below. -/
def operands : Value Nat Nat × Value Nat Nat :=
  match built with
  | .done values _ => values
  | .pending .. => (.empty, .empty)

/-- Keep the actual final source heap. -/
def source : InternedConstructorTemplates.State Nat Nat := built.state

/-- Observe closedness and the issued node count without comparing function-valued caches. -/
def sourceObservation : Option (Bool × Bool × Nat) :=
  match built with
  | .done (left, right) state => some (left.free.isEmpty, right.free.isEmpty, state.nodes.next)
  | .pending .. => none

set_option cbv.maxSteps 100000000 in
/-- Both source roots complete, are closed, and share the actual 32-entry identity history. -/
theorem source_observed : sourceObservation = some (true, true, 32) := by cbv

/-- The actual source result is the completed pair and its exact returned cache. -/
theorem built_done : built = .done operands source := by
  cases returned : built with
  | done values state => simp only [operands, source, returned, InternedNestedConstruction.Outcome.state]
  | pending key state =>
      have impossible := source_observed
      simp only [sourceObservation, returned] at impossible
      cases impossible

/-- Actual construction derives full source facts and both available roots. -/
theorem source_verified : Verified empty built
    (fun state values => Available state values.1 ∧ Available state values.2) := by
  unfold built
  have first := InternedFreshOrdinaryFacts.build_verified (expression 1) [] empty empty_facts (by intro value member; cases member)
  apply bind_verified empty _ _ Available _ first
  intro left after firstDone afterFacts leftAvailable
  have second := InternedFreshOrdinaryFacts.build_verified (expression 2) [] after afterFacts (by intro value member; cases member)
  apply bind_verified after _ _ Available _ second
  intro right final secondDone finalFacts rightAvailable
  apply pure_verified final finalFacts (left, right)
  exact ⟨by simpa only [secondDone, InternedNestedConstruction.Outcome.state] using second.available left leftAvailable, rightAvailable⟩

/-- Both original inputs are complete available records in their actual coherent cache. -/
theorem source_inputs : Facts source ∧ Available source operands.1 ∧ Available source operands.2 := by
  exact ⟨by simpa only [built_done, InternedNestedConstruction.Outcome.state] using source_verified.facts,
    source_verified.result operands source built_done⟩

/-- The actual two completed source builds supply complete payload coverage. -/
theorem source_covered : InternedRecordCoherence.Covered [] source := by
  have covered : InternedNestedCoverage.OnDone [] built := by
    unfold built
    apply InternedNestedCoverage.bind_covered [] [] _ _
      (InternedFreshOrdinaryCoverage.build_covered (expression 1) [] empty empty_valid InternedRecordCoherence.empty_correct.2)
    intro left after firstDone afterCovered
    have afterValid : InternedConstructorTemplates.Valid after := by
      simpa only [firstDone, InternedNestedConstruction.Outcome.state] using
        (InternedFreshOrdinaryGrowth.build_correct (expression 1) [] empty empty_valid).1
    apply InternedNestedCoverage.bind_covered [] [] _ _
      (InternedFreshOrdinaryCoverage.build_covered (expression 2) [] after afterValid afterCovered)
    intro right final secondDone finalCovered values state returned
    cases returned
    exact finalCovered
  exact covered operands source built_done

/-- Both actual builds retain normalization and the complete repaired profile and free-name heaps. -/
theorem source_context : InternedFreshOrdinaryContext.Context source [] := by
  have done := built_done
  unfold built at done
  obtain ⟨left, after, firstDone, later⟩ := InternedNestedSpecialization.bind_done _ _ _ _ done
  have afterContext : InternedFreshOrdinaryContext.Context after [] := by
    simpa only [firstDone, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryContext.empty_context.build (expression 1)
  obtain ⟨right, final, secondDone, returned⟩ := InternedNestedSpecialization.bind_done _ _ _ _ later
  have finalContext : InternedFreshOrdinaryContext.Context final [] := by
    simpa only [secondDone, InternedNestedConstruction.Outcome.state] using afterContext.build (expression 2)
  have same : final = source := (InternedNestedConstruction.Outcome.done.inj returned).2
  rw [same] at finalContext
  exact finalContext

/-- Both actual source roots have empty cached free-reference lists. -/
theorem source_closed : operands.1.free = [] ∧ operands.2.free = [] := by
  have observed : (operands.1.free.isEmpty, operands.2.free.isEmpty, source.nodes.next) = (true, true, 32) := by
    apply Option.some.inj
    simpa only [sourceObservation, built_done] using source_observed
  exact ⟨List.isEmpty_iff.mp (congrArg Prod.fst observed), List.isEmpty_iff.mp (congrArg (fun value => value.2.1) observed)⟩

set_option cbv.maxSteps 100000000 in
/-- Both actual roots use only original interned recursion references in their semantic payloads. -/
theorem source_original : Original operands.1 ∧ Original operands.2 := by
  cbv
  constructor
  all_goals
    apply Original.mu
    apply Original.node
    intro edge included child member
    have same := List.mem_singleton.mp included
    subst edge
    have same := List.mem_singleton.mp member
    subst child
    apply Original.mu
    apply Original.node
    intro edge included child member
    have same := List.mem_singleton.mp included
    subst edge
    rcases List.mem_cons.mp member with first | later
    · subst child; exact .reference _
    · have same := List.mem_singleton.mp later
      subst child
      exact .reference _

/-- Start the actual native memo driver with empty memo and domain caches. -/
def initialState : SourceRecursiveIntersectionThunks.State 64 Nat Nat := initial 64 ⟨source, Cache.emptyState⟩

/-- Request intersection of the two actual closed source roots. -/
def code : Code Nat Nat (Value Nat Nat) := .node ⟨IntersectionEmptyDomain.emptyDomain, operands.1, operands.2⟩ .pure

/-- The actual starting native state has complete source facts and valid empty memo tables. -/
theorem initial_valid : SourceRecursiveIntersectionThunks.Valid 64 0 Nat.max initialState :=
  SourceRecursiveIntersectionThunks.initial_valid 64 0 Nat.max _ ⟨source_inputs.1, Cache.empty_valid⟩

set_option cbv.maxSteps 100000000 in
/-- The actual original root request fits the checked 64-bit source keys. -/
theorem root_words : SourceRecursiveIntersectionMemo.KeySafe 64 IntersectionEmptyDomain.emptyDomain operands.1 operands.2 := by
  refine ⟨by decide, by decide, .mu 10, .mu 26, ?_, ?_, ?_, ?_⟩ <;> cbv

/-- Retain the exact native state and continuation after 22 actual steps. -/
def site := execute 0 Nat.max 22 code initialState

/-- Observe the actual pending binder pair, body free names, and existing preparation check. -/
def siteObservation : Option ((Nat × Nat) × List Reference × Bool) :=
  match site with
  | .yielded (.optionalBinder pair body _) _ => some (pair, body.free, InternedStoredPreparationCheck.check body)
  | _ => none

set_option cbv.maxSteps 200000000 in
/-- The actual reached body retains the outer pair and fails the existing preparation predicate. -/
theorem site_observed : siteObservation = some ((10, 26), [.intersection 10 26], false) := by cbv

/-- Actual finite native execution from closed original source roots reaches an unprepared optional-binder body. -/
theorem reaches_unprepared : ∃ pair body next before,
    Steps 0 Nat.max 22 code initialState (.optionalBinder pair body next) before ∧
      InternedRecordCoherence.Covered [] before.machine.heap ∧ ¬ PreparedWithoutMu body := by
  have observed := site_observed
  cases actual : site with
  | done | failed | blocked => simp only [siteObservation, actual] at observed; cases observed
  | yielded remaining before =>
      cases remaining <;> try (simp only [siteObservation, actual] at observed; cases observed)
      rename_i pair body next
      have fields := Option.some.inj (by simpa only [siteObservation, actual] using observed)
      have rejected : InternedStoredPreparationCheck.check body = false := congrArg (fun value => value.2.2) fields
      have trace := execute_steps 0 Nat.max 22 code _ initialState before actual
      have covered := trace.covered 0 Nat.max 22 code _ initialState before source_inputs.1.coherent.valid source_covered
      exact ⟨pair, body, next, before, trace, covered.2,
        InternedStoredPreparationCheck.not_prepared body rejected⟩

/-- Preparation does not follow from complete source coverage and actual closed original native inputs. -/
theorem not_all_closed_original_prepared :
    ¬ (∀ (heap : InternedConstructorTemplates.State Nat Nat) (left right : Value Nat Nat),
      Facts heap → Available heap left → Available heap right → Original left → Original right →
      left.free = [] → right.free = [] → InternedRecordCoherence.Covered [] heap →
      InternedFreshOrdinaryContext.Context heap [] →
      SourceRecursiveIntersectionMemo.KeySafe 64 IntersectionEmptyDomain.emptyDomain left right →
      ∀ fuel pair body next before,
      Steps 0 Nat.max fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial 64 ⟨heap, Cache.emptyState⟩) (.optionalBinder pair body next) before →
      InternedRecordCoherence.Covered [] before.machine.heap → PreparedWithoutMu body) := by
  intro preserved
  obtain ⟨pair, body, next, before, trace, covered, unprepared⟩ := reaches_unprepared
  exact unprepared (preserved source operands.1 operands.2 source_inputs.1 source_inputs.2.1 source_inputs.2.2
    source_original.1 source_original.2 source_closed.1 source_closed.2 source_covered source_context root_words 22 pair body next before trace covered)

/-- Observe the actual bounded native return independently of preparation. -/
def returned : Option NodeRef :=
  match execute 0 Nat.max 100 code initialState with
  | .done value _ => some value.referenceOf
  | _ => none

set_option cbv.maxSteps 400000000 in
/-- This native execution returns the original right root despite its unprepared intermediate body. -/
theorem native_returned : returned = some (.mu 26) := by cbv

end MicroCFTA.SourceRecursiveIntersectionOpenBodyBoundary
