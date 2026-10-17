import MicroCFTA.SourceRecursiveIntersectionMassInputBounds
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.MassInputKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionInputView IntersectSchedule
open SourceRecursiveIntersectionMassInputBounds
private def plan : Syntax Nat Bool := .union [
  .binder false (.node [.mk 0 true [.var 0]]),
  .node [.mk 1 false [], .mk 2 true [.node [.mk 3 true []], .node [.mk 3 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build plan [] empty
private def source := built.state
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def holds (_ : Bool) (_ : Language.Term Nat) := true
private def rootIdentity := match inputOf root with | .union name => name | _ => 0
private def bodyInput := (view source holds).body 2
private def bodyIdentity := match bodyInput with | .node name => name | _ => 0
private def selectedRow : Row Nat := ((view source holds).rows bodyIdentity)[0]?.getD ⟨0, [], fun _ => true⟩
private def muPayload : Value Nat Bool := (SourcePreparedSharedRows.read source 2).getD .empty

private theorem constructed : built = .done root source := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, root, source, done, Outcome.state]
private theorem facts : Facts source := (InternedFreshOrdinaryFacts.closed_verified plan).facts
private theorem available : Available source root :=
  (InternedFreshOrdinaryFacts.closed_verified plan).result root source constructed
private theorem closed : root.free = [] :=
  InternedFreshOrdinarySourceFreeNames.closed_free_empty plan root source constructed
private theorem original : Original root :=
  SourceRecursiveIntersectionOriginalOutput.closed_original root source facts.coherent available closed
private theorem rootInput : OriginalInput source (inputOf root) := ⟨root, original, available, original.codec root⟩
private theorem rootClosed : IntersectSchedule.closed (view source holds) (inputOf root) = true := by
  rw [closed_readback source facts holds root original available, closed]
  rfl
private def bounds := mass_inputBounds source facts holds (inputOf root) (inputOf root) rootInput rootInput rootClosed rootClosed
private theorem root_union : inputOf root = .union rootIdentity := by cbv
private theorem selected_mu : Input.mu 2 ∈ (view source holds).members rootIdentity := by cbv; exact .head _
private theorem selected_body : bodyInput = .node bodyIdentity := by cbv
private theorem selected_row : selectedRow ∈ (view source holds).rows bodyIdentity := by
  have found : ((view source holds).rows bodyIdentity)[0]? = some selectedRow := by cbv
  exact List.mem_of_getElem? found
private theorem selected_reference : Input.ref 2 ∈ selectedRow.children := by cbv; exact .head _
private theorem mu_reachable : InputReach (view source holds) (inputOf root) (.mu 2) := by
  exact .member (root_union ▸ InputReach.root) selected_mu
private theorem ref_reachable : InputReach (view source holds) (inputOf root) (.ref 2) := by
  have body := InputReach.body mu_reachable
  have ordinary : InputReach (view source holds) (inputOf root) (.node bodyIdentity) := selected_body ▸ body
  exact .child ordinary selected_row selected_reference

/-- An own source Mu and union produce the mass interface, strict body and row descent, and closed recursive reference bounds. -/
theorem recursive_source_mass :
    InternedFreshOrdinaryConstruction.build plan [] empty = .done root source ∧
    InputReach (view source holds) (inputOf root) (.ref 2) ∧
    InputReach (view source holds) (inputOf root) (.mu 2) ∧
    mass source bodyInput < mass source (.mu 2) ∧
    mass source (.ref 2) < mass source (.node bodyIdentity) ∧
    mass source (.mu 2) < mass source (.union rootIdentity) ∧
    bounds.size = mass source ∧ bounds.localWeight.value = localSize (mass source) ∧
    bounds.pairs.length = (1 + 4 * source.nodes.next) * (1 + 4 * source.nodes.next) ∧
    ∀ input, InputReach (view source holds) (inputOf root) input →
      Below (mass source) (inputOf root) input ∧
      mass source input ≤ InternedValueMassHeap.initialBound source ∧
      localSize (mass source) input ≤ InternedValueMassHeap.initialBound source := by
  have muOriginal : OriginalInput source (.mu 2) :=
    closed_reach_original source facts holds (inputOf root) (.mu 2) rootInput rootClosed mu_reachable
  refine ⟨constructed, ref_reachable, .reference ref_reachable,
    body_mass source facts holds 2 muOriginal,
    rows_mass source facts holds bodyIdentity selectedRow selected_row (.ref 2) selected_reference,
    members_mass source facts holds rootIdentity (.mu 2) selected_mu, rfl, rfl, pairs_length source, ?_⟩
  intro input reached
  exact ⟨bounds.closed_reach _ (.inl .root) rootClosed input reached,
    mass_stored source facts (InternedValueMassHeap.initial source facts) input,
    local_stored source facts (InternedValueMassHeap.initial source facts) input⟩

/-- An unissued reference has bounded unit mass without a physical availability claim. -/
theorem unissued_reference_mass {Symbol Guard : Type} (state : State Symbol Guard) (facts : Facts state) :
    mass state (.ref state.nodes.next) = 1 ∧
    mass state (.ref state.nodes.next) ≤ InternedValueMassHeap.initialBound state ∧
    ¬ Available state (.reference (.interned state.nodes.next)) := by
  refine ⟨by simp only [mass, payload, InternedValueMass.value],
    mass_stored state facts (InternedValueMassHeap.initial state facts) _, ?_⟩
  intro present
  have less := IntersectionFlatMemoKeyPhysical.reference_bounded state facts state.nodes.next present
  exact Nat.lt_irrefl _ less

end MicroCFTA.MassInputKernels

#print axioms MicroCFTA.MassInputKernels.recursive_source_mass
#check @MicroCFTA.MassInputKernels.recursive_source_mass
#print axioms MicroCFTA.MassInputKernels.unissued_reference_mass
#check @MicroCFTA.MassInputKernels.unissued_reference_mass
