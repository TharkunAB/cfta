import MicroCFTA.SourceCurrentHereditaryNativeCache

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.HereditaryNativeReviewKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryNativeCode (NodeLaw)
variable {Symbol Guard : Type}

def emptyRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
def chosen (machine : Machine Symbol Guard) : SourceRecursiveIntersectionThunks.State 8 Symbol Guard :=
  (lookupNode 8 emptyRequest (initial 8 machine)).2
def running (machine : Machine Symbol Guard) : SourceRecursiveIntersectionThunks.State 8 Symbol Guard :=
  (demandNode 0 (chosen machine)).2
def finished (machine : Machine Symbol Guard) : SourceRecursiveIntersectionThunks.State 8 Symbol Guard :=
  finishNode 0 .empty (running machine)

private theorem empty_safe : SourceRecursiveIntersectionMemo.KeySafe 8
    (emptyRequest (Symbol := Symbol) (Guard := Guard)).domain emptyRequest.left emptyRequest.right :=
  ⟨by decide, by decide, .empty, .empty, rfl, rfl, trivial, trivial⟩
private theorem empty_ready (machine : Machine Symbol Guard) : NodeReady machine emptyRequest :=
  ⟨empty_domain machine, empty_available _, empty_available _⟩

/-- Cold publication stores a derived Empty law; its next warm observation keeps the entire native state. -/
theorem cold_finish_warm (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine) :
    (running machine).nodes.cells 0 = some ⟨emptyRequest, .evaluating⟩ ∧
    (finished machine).nodes.cells 0 = some ⟨emptyRequest, .returned .empty⟩ ∧
    SourceCurrentHereditaryNativeCache.Stored annotation source (finished machine) ∧
    NodeLaw annotation source emptyRequest .empty ∧
    lookupNode 8 emptyRequest (finished machine) = (.memoized 0, finished machine) ∧
    demandNode 0 (finished machine) = (.ready .empty, finished machine) ∧
    (finished machine).machine = machine := by
  have start := SourceCurrentHereditaryNativeCache.node_started annotation source emptyRequest emptyRequest
    (initial 8 machine) (chosen machine) (running machine) 0
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    (SourceCurrentHereditaryNativeCache.initial_stored annotation source 8 machine)
    (empty_ready machine) empty_safe rfl rfl
  have law : NodeLaw annotation source emptyRequest (.empty : Value Symbol Guard) := fun _ _ _ => .empty
  have stored := SourceCurrentHereditaryNativeCache.finishNode_stored annotation source (running machine) 0 emptyRequest .empty
    start.2.2.1 start.2.2.2 law
  have physical := SourceCurrentAllocatedNativePhysicalCache.finishNode_valid (running machine) start.2.1 0 emptyRequest .empty
    start.2.2.2 (empty_available _)
  have warm := SourceCurrentHereditaryNativeCache.node_observed_ready annotation source emptyRequest
    (finished machine) (finished machine) (finished machine) 0 .empty physical stored
    (empty_ready machine) empty_safe rfl rfl
  exact ⟨start.2.2.2, rfl, warm.2.1, warm.1, rfl, rfl, rfl⟩

/-- Actual edge work followed by actual node work uses the same returned row and representation. -/
theorem edge_then_node [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (represented : representation state.heap) (available : ∀ value ∈ values, Available state.heap value)
    (guardValid : annotation guard) (annotated : ∀ value ∈ values, Annotated annotation value) :
    SourceCurrentHereditaryNativeCode.Certified annotation source representation
      ((.work (makeEdge symbol guard values) Code.pure).bind fun edge => .work (makeNode [edge]) .pure) state
      (fun after output => Available after.heap output ∧ Annotated annotation output) := by
  apply SourceCurrentHereditaryNativeCode.certified_bind annotation source representation _ _ state valid represented
    (fun after edge => InternedEdgeResidency.EdgeResident after.heap edge ∧ SourceCurrentHereditaryConstructors.Edge annotation edge) _
    (SourceCurrentHereditaryNativeCode.edge_work annotation source representation symbol guard values state valid available guardValid annotated)
  intro edge after afterValid _ _ checked
  exact SourceCurrentHereditaryNativeCode.node_work annotation source representation [edge] after afterValid
    (fun value member => (List.mem_singleton.mp member) ▸ checked.1)
    (fun value member => (List.mem_singleton.mp member) ▸ checked.2)

end MicroCFTA.HereditaryNativeReviewKernels

#print axioms MicroCFTA.HereditaryNativeReviewKernels.cold_finish_warm
#check @MicroCFTA.HereditaryNativeReviewKernels.cold_finish_warm
#print axioms MicroCFTA.HereditaryNativeReviewKernels.edge_then_node
#check @MicroCFTA.HereditaryNativeReviewKernels.edge_then_node
