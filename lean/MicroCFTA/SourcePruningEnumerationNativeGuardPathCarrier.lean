import MicroCFTA.SourceCurrentNativeClosedGuardAlphabet
import MicroCFTA.SourcePruningEnumerationForecastPathDomain

/-!
# Original finite paths through actual native guard prefixes

The carrier uses the original literals and the initial enumeration state.
It does not depend on the native trace length or capacity.
The result covers projected guard paths. It does not cover inherited payloads.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeGuardPathCarrier
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State SourcePruningTemplates.Symbol Guard
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "alphabet" => SourceCurrentNativeClosedGuardAlphabet.originalAlphabet
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every projected guard path after an admitted native prefix belongs to the same original finite carrier. -/
theorem native_prefix_projected_paths (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (initial : Core) {A : Type} {width fuel : Nat}
    {control rest : SourceEqualityNativeDemand.Control A}
    {before after : SourceEqualityNativeDemand.State width}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel control before rest after)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (allocated : SourceCurrentAllocatedNativeFieldClosure.Fields control before)
    (origins : SourceEqualityAnnotationHeap.Heap
      (SourceEqualityConstraintOrigins.Derived literals top conjoin) before.native.machine.heap)
    (fields : SourceCurrentNativeGuardStep.Fields (alphabet literals) control)
    {key : EdgeKey Symbol Guard} {edge : EdgeValue Symbol Guard}
    (present : after.native.machine.heap.edgeRecords key = some edge) :
    ∀ tries residual,
      SourcePruningEnumerationConstraint.project key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie,
        path ∈ SourcePruningEnumerationForecastPathDomain.carrier (alphabet literals) initial := by
  have retained := SourceCurrentNativeClosedGuardAlphabet.original_retained literals normalized
    trace good allocated origins fields
  exact SourcePruningEnumerationForecastPathDomain.projected_paths (alphabet literals) initial
    key.constraint (retained.1 key edge present)

end MicroCFTA.SourcePruningEnumerationNativeGuardPathCarrier
