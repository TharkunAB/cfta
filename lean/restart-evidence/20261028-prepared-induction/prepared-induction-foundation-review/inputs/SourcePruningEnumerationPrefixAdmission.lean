import MicroCFTA.SourcePruningEnumerationPrefixResources

namespace MicroCFTA.SourcePruningEnumerationPrefixAdmission
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile)
open SourcePruningEnumerationSelectedStep (Result PrefixValid finish)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationNodes (lookupNode)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}

/-- Sum every original pending bucket, including repeated suspended entries. -/
def suspendedBound (before : Core) : Nat :=
  (before.values.map fun value => match value with
    | .unenumerated _ scs => scs.length
    | _ => 0).sum

private theorem stored_length_le (before : Core) (slot : Nat) (node : Option Nat)
    (scs : List Suspended) (stored : before.values[slot]? = some (.unenumerated node scs)) :
    scs.length ≤ suspendedBound before := by
  have member : (.unenumerated node scs : UVarValue Symbol) ∈ before.values :=
    List.mem_of_getElem? stored
  unfold suspendedBound
  generalize before.values = values at member ⊢
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | listed
      · subst first
        simp only [List.map_cons, List.sum_cons]
        exact Nat.le_add_right _ _
      · have bounded := ih listed
        simp only [List.map_cons, List.sum_cons]
        omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem finish_preserves
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (r n p h k uv : Nat) (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf r n p h k uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf r n p h k uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩

/-- The actual retained narrowing cache derives ordinary-entry facts and an original bucket bound. -/
theorem narrowed_admission
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (profile : Profile) (property : Constraint → Prop)
    (bounded : Fits profile caller.checked) (known : Heap property caller.checked.native.machine.heap)
    (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .narrowed _ _ reached queries _ (some after) _ _ =>
        ∃ (handle : Nat) (scs : List Suspended) (value : Node) (final : Memos),
          Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          Packet formulas solver inventory reached final metadata after ∧
          EnumerationDriver.Ready uv after.core ∧
          after.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
          lookupNode reached.checked.native.machine.heap handle = some value ∧
          Available reached.checked.native.machine.heap value ∧ value.free = [] ∧
          EnumerationReferences.IncomingAvoid uv after.core ∧
          EnumerationDependencies.InputsPending after.core scs ∧
          (∀ sc ∈ scs, sc.var < before.core.counter) ∧
          scs.length ≤ suspendedBound before.core ∧
          after.core.counter = before.core.counter ∧ after.waiting = before.waiting ∧
          Fits (headProfile profile) reached.checked ∧ Heap property reached.checked.native.machine.heap
    | _ => True := by
  have selection : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  have unblocked := (SourcePruningEnumerationSelection.offered before (order metadata) uv selection).2.2
  have returned := SourcePruningEnumerationRecursive.prefix_packet holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller memos before packet observed valid
  obtain ⟨_roots, _paths, _storage, originalRealized, _counts, _flags⟩ := packet.valid
  have resources := SourcePruningEnumerationSelectedStep.prefix_resources holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos profile property
    packet.context originalRealized bounded known observed valid
  have full := valid.2.1
  cases observed with
  | stopped _ _ | parked _ _ _ => trivial
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨_finished, finished⟩ := finish_preserves checkEmpty edgesOf 0 0 0 0 0 uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨oldHandle, scs, readAfter, reading, _checking, _oldValue, _value, _heap,
            _selectedAction, _final, _decoded, _narrowed, _prepared, _samePrepared, _reached,
            _queries, _post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, impossible, _right, _ordinary⟩ |
            ⟨handle, cached, _nonempty, _encoded, _action, same, _valid, _safe, _pending,
              ready, stored, waiting, _right, _ordinary, _rest⟩
          · cases impossible
          · have equal : after = cached := Option.some.inj same
            subst cached
            obtain ⟨final, post, saved, afterPacket⟩ := returned
            obtain ⟨roots, paths, _storage, realized, counts, _flags⟩ := afterPacket.valid
            obtain ⟨value, decoded, available, closed⟩ := realized uv handle scs stored
            have incoming := SourcePruningEnumerationSelection.unblocked_incoming after roots paths counts uv ready.root
              (by rw [waiting]; exact unblocked)
            have read : Success (getValue fuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter := by
              rw [Success, reading]
              exact List.mem_singleton_self _
            obtain ⟨found, _lookup, originalStored, _readState⟩ :=
              (getValue_success fuel uv before.core readAfter (.unenumerated (some oldHandle) scs)).mp read
            have lengthBound := stored_length_le before.core found.representative (some oldHandle) scs originalStored
            have counter : after.core.counter = before.core.counter := valid.2.2.1
            have ids : ∀ sc ∈ scs, sc.var < before.core.counter := by
              have actual := ready.safe.1.values _ (List.mem_of_getElem? stored)
              simpa only [SlotBound, counter] using actual
            exact ⟨handle, scs, value, final, post, saved, afterPacket, ready, stored, decoded,
              available, closed, incoming, EnumerationReferences.pending_inputs after.core afterPacket.pending
                uv (some handle) scs stored, ids, lengthBound, counter, waiting, resources⟩

end MicroCFTA.SourcePruningEnumerationPrefixAdmission
