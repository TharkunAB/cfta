import MicroCFTA.SourceCurrentAllocatedPartialMemoSound
import MicroCFTA.SourceEqualityConstraintMemoAllocation

/-!
# Complete outer requests from actual physical keys

Ready inherited values retain coherent canonical class metadata. Their
allocated identities determine the complete inherited payload. Coherent
available node records and resident edges determine the other argument.
These facts identify the captured owner of an actual evaluation request.
They do not supply a decreasing rank or prove outer completion.
-/
namespace MicroCFTA.SourceCurrentOuterKeyIdentity
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "EqCache" => Cache.State SourceEqualityPartialConstraintKey.Key
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Caller" => SourceCurrentAllocatedPartialState.State

/-- Equal keys identify both complete arguments of ready available node requests. -/
theorem node_eq_of_key (cache : EqCache) (heap : Heap)
    (valid : Cache.Valid cache) (coherent : InternedRecordCoherence.Coherent heap)
    (first second : NodeRequest) (firstReady : EqReady cache first.inherited)
    (secondReady : EqReady cache second.inherited) (firstAvailable : Available heap first.value)
    (secondAvailable : Available heap second.value) (same : first.key = second.key) : first = second := by
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity cache valid
    first.inherited second.inherited firstReady secondReady (congrArg Prod.fst same)
  have values := SourceEqualityPartialKeyTransport.available_reference_eq heap coherent
    first.value second.value firstAvailable secondAvailable (congrArg Prod.snd same)
  cases first
  cases second
  cases inherited
  cases values
  rfl

/-- Equal keys identify both complete arguments of ready resident edge requests. -/
theorem edge_eq_of_key (cache : EqCache) (heap : Heap)
    (valid : Cache.Valid cache) (coherent : InternedRecordCoherence.Coherent heap)
    (first second : EdgeRequest) (firstReady : EqReady cache first.inherited)
    (secondReady : EqReady cache second.inherited) (firstResident : EdgeResident heap first.value)
    (secondResident : EdgeResident heap second.value) (same : first.key = second.key) : first = second := by
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity cache valid
    first.inherited second.inherited firstReady secondReady (congrArg Prod.fst same)
  have values := edge_identity_unique heap coherent first.value second.value
    firstResident secondResident (congrArg Prod.snd same)
  cases first
  cases second
  cases inherited
  cases values
  rfl

/-- Actual node evaluation retains exactly the queried request as its captured owner. -/
theorem node_evaluate_owner (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {width : Nat} (request : NodeRequest) (before : Caller width)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (valid : Cache.Valid before.checked.operations.constraints)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (handle : Nat) (owner : NodeRequest) (running : Caller width)
    (started : beginNode request before = (handle, .evaluate owner, running)) : owner = request := by
  obtain ⟨_, _, good, same⟩ := SourceCurrentAllocatedPartialMemoSound.beginNode_evaluate_sound
    formulas solver request before sound inherited available handle owner running started
  have parts := beginNode_components request before
  rw [started] at parts
  dsimp only at parts
  exact node_eq_of_key _ _ valid coherent owner request (parts.1 ▸ good.inherited) inherited
    (parts.1 ▸ good.input) available same

/-- Actual edge evaluation retains exactly the queried request as its captured owner. -/
theorem edge_evaluate_owner (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {width : Nat} (request : EdgeRequest) (before : Caller width)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (valid : Cache.Valid before.checked.operations.constraints)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (handle : Nat) (owner : EdgeRequest) (running : Caller width)
    (started : beginEdge request before = (handle, .evaluate owner, running)) : owner = request := by
  obtain ⟨_, _, good, same⟩ := SourceCurrentAllocatedPartialMemoSound.beginEdge_evaluate_sound
    formulas solver request before sound inherited resident handle owner running started
  have parts := beginEdge_components request before
  rw [started] at parts
  dsimp only at parts
  exact edge_eq_of_key _ _ valid coherent owner request (parts.1 ▸ good.inherited) inherited
    (parts.1 ▸ good.input) resident same

end MicroCFTA.SourceCurrentOuterKeyIdentity
