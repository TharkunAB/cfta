import MicroCFTA.SourceCurrentHereditaryTargetQuery
import MicroCFTA.SourceCurrentHereditaryConstruction

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.TargetSupportKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
local notation "Stored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Allowed raw construction creates its own value, causal Mu store, and source-universal fresh tables. -/
theorem constructed_tables (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed Plain expression)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    ∃ value heap,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      Annotated Plain value ∧
      Stored (⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩ : Checked width) ∧
      ∀ source, SourceCurrentHereditaryNativeCache.Stored Plain source (initial width ⟨heap, Cache.emptyState⟩) := by
  obtain ⟨value, heap, actual, constructors, annotated⟩ := SourceCurrentHereditaryConstruction.closed Plain expression allowed
  have stored := SourceCurrentHereditaryNativeUniversalStore.initial Plain (width := width)
    (⟨heap, Cache.emptyState⟩ : Machine Symbol Guard) operations constructors
  exact ⟨value, heap, actual, annotated, stored, stored.native⟩

/-- A literal empty query executes in one step at any width and retains the exact full checked state. -/
theorem empty_query (before : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (stored : Stored before) :
    SourceEqualityNativeDemand.execute 1 (.code (requestNode IntersectionEmptyDomain.emptyDomain .empty .empty)) before =
      .done .empty before ∧
      SourceCurrentAllocatedTargetQuery.Step .empty .empty before .empty before ∧
      Stored before ∧ Annotated Plain (.empty : Value Symbol Guard) := by
  have actual : SourceEqualityNativeDemand.step (.code (requestNode IntersectionEmptyDomain.emptyDomain .empty .empty)) before =
      .yielded (.code (.pure .empty)) before := by
    simp [SourceEqualityNativeDemand.step, requestNode, SourceRecursiveIntersectionNative.step,
      lookupNode, SourceRecursiveIntersectionMemo.requestKey, IntersectionFlatMemoKeyDomain.sourceKey,
      IntersectionFlatMemoKey.key, IntersectionFlatMemoKey.input, Value.referenceOf,
      compileNode, SourceRecursiveIntersectionControl.decision, Code.bind]
  have inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
      (.code (requestNode IntersectionEmptyDomain.emptyDomain .empty .empty)) before := by
    refine ⟨⟨empty_domain _, trivial, trivial⟩, ?_⟩
    intro key encoded
    simp [SourceRecursiveIntersectionMemo.requestKey, IntersectionFlatMemoKeyDomain.sourceKey,
      IntersectionFlatMemoKey.key, IntersectionFlatMemoKey.input, Value.referenceOf] at encoded
  have trace := SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.cons _ _ _ _ _ _ _ inputs actual (.refl _ _)
  have step : SourceCurrentAllocatedTargetQuery.Step .empty .empty before .empty before := .run trace
  have retained := SourceCurrentHereditaryTargetQuery.step step good semantic trivial trivial rfl rfl stored trivial trivial
  exact ⟨SourceEqualityNativeDemand.trace_done _ _ before before .empty trace.steps, step, retained⟩

#print axioms constructed_tables
#check @constructed_tables
#print axioms empty_query
#check @empty_query
end MicroCFTA.TargetSupportKernels
