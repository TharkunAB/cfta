import MicroCFTA.SourceCurrentConstrainedCapProjection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.OwnerCapProjectionKernels
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceCurrentConstrainedCap SourceCurrentHereditaryConstruction SourceEqualityAnnotationLanguage
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Two independently constructed projections consume their summed node-path lengths at the same returns. -/
theorem serial_endpoints (valid : Guard → Prop) (depth : Nat) (first second : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before)
    (bounded : Cap valid depth value) (long : depth ≤ first.length + second.length) :
    ∃ middle current result after,
      Project first value before middle current ∧ Project second middle current result after ∧
      SourceEqualityRequiredCache.Keeps before after ∧ MuStored valid after ∧ Annotated valid result := by
  obtain ⟨middle, current, one, kept, ready, resident, middleClosed, middleStore, middleCap⟩ :=
    SourceCurrentConstrainedCapProjection.complete valid depth first value before semantic available closed stored bounded
  obtain ⟨result, after, two, later, _ready, _resident, _closed, resultStore, resultCap⟩ :=
    SourceCurrentConstrainedCapProjection.complete valid (depth - first.length) second middle current ready resident middleClosed middleStore middleCap
  have zero : (depth - first.length) - second.length = 0 := by omega
  exact ⟨middle, current, result, after, one, two, kept.trans later, resultStore, resultCap.annotated zero⟩

/-- A forest root index selects a node without consuming any constrained node layer. -/
theorem root_index (valid : Guard → Prop) (depth : Nat) (index : Int)
    (values : List (Value Symbol Guard)) (value : Value Symbol Guard) (before : State Symbol Guard)
    (selected : select values index = some value) (semantic : SemanticReady before)
    (available : InternedNestedProvenance.Values before values)
    (closed : MergedColdReaderClosedInputs.ClosedValues values) (stored : MuStored valid before)
    (bounded : ∀ input ∈ values, Cap valid depth input) :
    ∃ _actual : Forest [index] values before value before, MuStored valid before ∧ Cap valid depth value := by
  let actual : Forest [index] values before value before := .selected selected .root
  have result := SourceCurrentConstrainedCapProjection.forest valid depth actual semantic available closed stored bounded
  exact ⟨actual, result⟩

end MicroCFTA.OwnerCapProjectionKernels

#print axioms MicroCFTA.OwnerCapProjectionKernels.serial_endpoints
#check @MicroCFTA.OwnerCapProjectionKernels.serial_endpoints
#print axioms MicroCFTA.OwnerCapProjectionKernels.root_index
#check @MicroCFTA.OwnerCapProjectionKernels.root_index
