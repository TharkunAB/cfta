import MicroCFTA.SourceRecursiveIntersectionCodeMass

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.CodeMassReviewKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCodeMass (At)
variable {Symbol Guard : Type}

/-- Exact initial walk counts justify later constructor widths through bind and driver frames. -/
theorem counted_walk_framed_edge [DecidableEq (EdgeKey Symbol Guard)]
    (requests : List (Value Symbol Guard × Value Symbol Guard))
    (domain : Interned DomainKey) (state : Machine Symbol Guard) (bound : Nat)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (stored : InternedValueMassHeap.Stored bound state.heap)
    (known : Domain state domain)
    (inputs : ∀ pair ∈ requests, Available state.heap pair.1 ∧ Available state.heap pair.2)
    (original : Value Symbol Guard) (available : Available state.heap original)
    (count : requests.length + 1 ≤ bound) (symbol : Symbol) (guard : Guard)
    (nodeHandle edgeHandle : Nat) (oldEdge : EdgeValue Symbol Guard) :
    let code := SourceRecursiveIntersectionCode.walk (fun pair => requestNode domain pair.1 pair.2) requests
    At code state bound (fun after values => values.length = requests.length ∧ ∀ value ∈ values, Available after.heap value) ∧
      At (code.bind fun values => .finishNode nodeHandle .empty
        (.finishEdge edgeHandle oldEdge (.work (makeEdge symbol guard (values ++ [original])) .pure)))
        state bound (fun after edge => EdgeResident after.heap edge) := by
  dsimp only
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  have walked := SourceRecursiveIntersectionCodeMass.walk
    (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode domain pair.1 pair.2)
    requests input (fun after value => Available after.heap value)
    (by
      intro before after growth pair ready
      exact ⟨ready.1.grows domain growth, growth.available _ ready.2.1, growth.available _ ready.2.2⟩)
    available_stable
    (fun pair _ current larger _ _ ready => SourceRecursiveIntersectionCodeMass.request_node
      domain pair.1 pair.2 current larger ready)
    state bound valid stored (fun pair member => ⟨known, inputs pair member⟩)
  refine ⟨walked, ?_⟩
  apply SourceRecursiveIntersectionCodeMass.bind _ _ state bound valid stored _ _ walked
  intro values after larger afterValid growth increase current returned
  change At (.work (makeEdge symbol guard (values ++ [original])) .pure) after larger _
  apply SourceRecursiveIntersectionCodeMass.edge symbol guard _ after larger afterValid
  · intro value member
    rcases List.mem_append.mp member with earlier | last
    · exact returned.2 value earlier
    · cases List.mem_singleton.mp last
      exact growth.available original available
  · have square := Nat.mul_le_mul_left larger current.positive
    simp only [Nat.mul_one] at square
    rw [List.length_append, List.length_singleton, returned.1]
    exact Nat.le_trans count (Nat.le_trans increase square)

end MicroCFTA.CodeMassReviewKernels

#print axioms MicroCFTA.CodeMassReviewKernels.counted_walk_framed_edge
#check @MicroCFTA.CodeMassReviewKernels.counted_walk_framed_edge
