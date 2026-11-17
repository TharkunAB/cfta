import MicroCFTA.SourceSynthesisCurrentUniverseColdNoNewMu
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms

namespace MicroCFTA.SourceSynthesisCurrentUniverseColdBoundaryAtoms
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Authentic initial Mu inventory]
The query starts at the actual source heap. Source construction derives readiness.
The actual cold query and every bounded prefix introduce no new Mu records.
The original source inventory therefore classifies every closed resident boundary
at those endpoints. A grown heap alone would not supply that initial inventory.
This result does not assert that every classified value has an inhabitant.
-/

private theorem trace_physical
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width used : Nat} {A : Type}
    {control rest : Control A} {before after : Checked width}
    (actual : Trace used control before rest after)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native) :
    SourceCurrentAllocatedNativePhysicalCache.Valid after.native := by
  induction actual with
  | refl => exact valid
  | cons control before next middle final after count inputs one tail ih =>
      have checked := SourceCurrentAllocatedNativePhysicalExecution.step_valid control before valid inputs
      have reached : SourceCurrentAllocatedNativePhysicalCache.Valid middle.native := by
        simpa only [one, Outcome.state] using checked
      exact ih reached

/-- The original source query derives its endpoint and prefix boundary atoms. -/
theorem original_source_cold_query_closed_boundary_atoms
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (sourceStart : machine.heap = sourceHeap)
    (rootDomain : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (leftProfile : Profile entry.identity rootRequest.left)
    (rightProfile : Profile entry.identity rootRequest.right)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)) :
    (∀ value : Value Symbol Guard,
      Available
        (SourceEqualityNativeDemand.execute fuel (.code (.node rootRequest .pure))
          (⟨initial width machine, operations⟩ : Checked width)).state.native.machine.heap value →
      value.free = [] →
      ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) ∧
    ∀ (used : Nat) (rest : Control (Value Symbol Guard)) (current : Checked width),
      used ≤ fuel →
      Trace used (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width) rest current →
      ∀ value : Value Symbol Guard, Available current.native.machine.heap value →
        value.free = [] →
        ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity := by
  have initialValid : SourceCurrentAllocatedNativePhysicalCache.Valid
      (⟨initial width machine, operations⟩ : Checked width).native :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have ready : SourceEqualityRequiredCache.Ready machine.heap := by
    rw [sourceStart]
    exact SourceEqualityRequiredCache.constructed (ordinarySymbols whole) rootValue sourceHeap built
  have unchanged :=
    SourceSynthesisCurrentUniverseNativeAllocation.original_universe_cold_query_no_new_mu
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      rootRequest machine machineValid sourceGrowth rootDomain leftProfile rightProfile
      operations operationsValid fuel inputs fields
  have sourceToStart : InternedShallowHeap.NoNewMu sourceHeap machine.heap := by
    rw [sourceStart]
    exact InternedShallowHeap.noNewMu_refl _
  constructor
  · intro value available closed
    have checked := SourceCurrentAllocatedNativePhysicalExecution.execute_invariants fuel
      (.code (.node rootRequest .pure)) (⟨initial width machine, operations⟩ : Checked width)
      initialValid ready inputs
    exact SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      _ checked.1.machine.1.coherent (InternedShallowHeap.noNewMu_trans sourceToStart unchanged.1)
      value available closed
  · intro used rest current bounded actual value available closed
    have checked := trace_physical actual initialValid
    exact SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      current.native.machine.heap checked.machine.1.coherent
      (InternedShallowHeap.noNewMu_trans sourceToStart (unchanged.2 used rest current bounded actual))
      value available closed

end MicroCFTA.SourceSynthesisCurrentUniverseColdBoundaryAtoms

#check @MicroCFTA.SourceSynthesisCurrentUniverseColdBoundaryAtoms.trace_physical
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseColdBoundaryAtoms.trace_physical
#check @MicroCFTA.SourceSynthesisCurrentUniverseColdBoundaryAtoms.original_source_cold_query_closed_boundary_atoms
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseColdBoundaryAtoms.original_source_cold_query_closed_boundary_atoms
