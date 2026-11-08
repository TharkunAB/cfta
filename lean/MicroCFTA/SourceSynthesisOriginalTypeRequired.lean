import MicroCFTA.SourceSynthesisOriginalTypeFieldCalls
import MicroCFTA.SourceCurrentHereditaryTypeFieldMerge
import MicroCFTA.InternedFreshOrdinaryCosts

/-!
# Original Type slot zero after actual Required mutation

The accepted source build derives semantic readiness, costs, available
children, closed children, and the conditional Mu store. The original
row supplies its exact Type operand. The actual Required call processes
that operand before any later Program children. Later children need no
Type annotation. No returned store or repeated-call invariant is asserted.
-/
namespace MicroCFTA.SourceSynthesisOriginalTypeRequired
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisOriginalTypeAnnotations (OriginalType)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "BasicContext" => InternedFreshOrdinaryContext.Context
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem many_closed (expressions : List (Syntax Symbol Guard))
    (before after : State Symbol Guard) (context : BasicContext before [])
    (values : List (Value Symbol Guard)) (actual : buildMany expressions [] before = .done values after) :
    ClosedValues values := by
  induction expressions generalizing before values with
  | nil =>
      simp only [buildMany, Outcome.done.injEq] at actual
      obtain ⟨rfl, rfl⟩ := actual
      intro value member
      cases member
  | cons first rest ih =>
      cases one : build first [] before with
      | pending key state => simp only [buildMany, one, Outcome.bind] at actual; cases actual
      | done value middle =>
          cases tail : buildMany rest [] middle with
          | pending key state => simp only [buildMany, one, tail, Outcome.bind] at actual; cases actual
          | done remaining final =>
              simp only [buildMany, one, tail, Outcome.bind, Outcome.done.injEq] at actual
              obtain ⟨rfl, rfl⟩ := actual
              have next : BasicContext middle [] := by
                simpa only [one, Outcome.state] using context.build first
              intro chosen member
              rcases List.mem_cons.mp member with rfl | member
              · apply List.eq_nil_iff_forall_not_mem.mpr
                intro name present
                obtain ⟨input, impossible, _⟩ := InternedFreshOrdinarySourceFreeNames.build_free_origins
                  first [] before context.normal context.inputs context.freeNames context.profiles
                  chosen middle one name present
                cases impossible
              · exact ih middle next remaining tail chosen member

section Source
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
variable {expressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
variable {outputs : List (EdgeValue Symbol Guard)} {rowIndex : Nat} {symbol : Symbol}
variable {fuel readFuel : Nat} {paths : List (List Int)} {results : List (Value Symbol Guard)}
variable {finish : State Symbol Guard}
include accepted built

/-- Actual original row construction derives the physical and Type input facts. -/
theorem source_context {guard : Guard} {children : List (Syntax Symbol Guard)}
    (call : RowCall expressions [] before outputs after heap rowIndex symbol guard children) :
    SemanticReady heap ∧ CostHeap heap ∧ Values heap call.output.children ∧
      ClosedValues call.output.children ∧ MuStored (Origin lib) heap := by
  have checked := InternedFreshOrdinaryFacts.closed_verified (ordinarySymbols whole)
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, Outcome.state] using checked.facts
  have middleContext : BasicContext call.middle [] := by
    simpa only [call.called, Outcome.state] using call.context.many children
  have made := InternedEdgeResidency.makeEdge_linked symbol guard call.values call.middle
    middleContext.normal.facts.coherent middleContext.normal.facts.linked
  have residentNext : InternedEdgeResidency.EdgeResident call.next call.output := by
    simpa only [call.made] using made.2
  have resident := InternedEdgeResidency.edge_grows call.next heap call.next_growth call.output residentNext
  refine ⟨SourceEqualityRequiredSemanticCache.constructed (ordinarySymbols whole) rootValue heap built,
    ?_, ?_, ?_, SourceSynthesisNativeTypeSites.firstOrderRaw_muStored (Origin lib)
      (SourceSynthesisNativeTypeTrace.origin_top lib) lib query signed whole accepted rootValue heap built⟩
  · simpa only [built, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap (ordinarySymbols whole)
  · exact facts.cached.edges call.output.entry.key call.output resident
  · simpa only [call.children_eq] using many_closed children call.current call.middle call.context call.values call.called

private theorem head_required {guard : Guard} {children : List (Syntax Symbol Guard)}
    (call : RowCall expressions [] before outputs after heap rowIndex symbol guard children)
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths call.output.children heap = .done results finish)
    (typed : ∃ value, call.output.children[0]? = some value ∧ Annotated (Origin lib) value) :
    ∃ result, results[0]? = some result ∧ Annotated (Origin lib) result := by
  obtain ⟨semantic, costs, available, closed, stored⟩ :=
    source_context lib query signed whole accepted rootValue heap built call
  obtain ⟨value, selected, annotated⟩ := typed
  exact SourceCurrentHereditaryTypeFieldMerge.requireAll_done_head (Origin lib) actual
    semantic costs available closed stored selected annotated

/-- The actual Required return retains a generalized component Type at slot zero. -/
theorem component (typ : Ty) (original : OriginalType lib typ)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol top
      [ordinarySymbols (generalize (typesOf lib query) typ)])
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths call.output.children heap = .done results finish) :
    ∃ result, results[0]? = some result ∧ Annotated (Origin lib) result := by
  obtain ⟨value, selected, _, _, annotated⟩ := SourceSynthesisOriginalTypeFieldCalls.component_call
    lib query signed whole accepted rootValue heap built typ original call
  exact head_required lib query signed whole accepted rootValue heap built call actual ⟨value, selected, annotated⟩

/-- The actual Required return retains a rigid argument Type at slot zero. -/
theorem argument (typ : Ty)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol top
      [ordinarySymbols (typeNode top typ)])
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths call.output.children heap = .done results finish) :
    ∃ result, results[0]? = some result ∧ Annotated (Origin lib) result := by
  obtain ⟨value, selected, _, _, annotated⟩ := SourceSynthesisOriginalTypeFieldCalls.argument_call
    lib query signed whole accepted rootValue heap built typ call
  exact head_required lib query signed whole accepted rootValue heap built call actual ⟨value, selected, annotated⟩

/-- The actual Required return retains the application universe before arbitrary Program edits. -/
theorem application (function argument : Expression)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument])
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths call.output.children heap = .done results finish) :
    ∃ result, results[0]? = some result ∧ Annotated (Origin lib) result := by
  obtain ⟨value, marker, selected, _, _, _, annotated, _⟩ := SourceSynthesisOriginalTypeFieldCalls.application_call
    lib query signed whole accepted rootValue heap built function argument call
  exact head_required lib query signed whole accepted rootValue heap built call actual ⟨value, selected, annotated⟩

/-- The actual Required return retains the filter goal before arbitrary candidate edits. -/
theorem filter (candidates : Expression)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates])
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths call.output.children heap = .done results finish) :
    ∃ result, results[0]? = some result ∧ Annotated (Origin lib) result := by
  obtain ⟨value, selected, _, _, annotated⟩ := SourceSynthesisOriginalTypeFieldCalls.filter_call
    lib query signed whole accepted rootValue heap built candidates call
  exact head_required lib query signed whole accepted rootValue heap built call actual ⟨value, selected, annotated⟩
end Source
end MicroCFTA.SourceSynthesisOriginalTypeRequired
