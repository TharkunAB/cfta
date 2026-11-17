import MicroCFTA.SourceSynthesisCurrentUniverseColdNoNewMu
import MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload

/-!
# A genuine inherited open-body hit at the next warm query

The old actual cold trace derives its endpoint inventory. The original
pattern is closed and available at that same endpoint. Actual source
facts and the later literal entry derive all mixed qualification fields.
The same inherited cell and ready demand then exclude the current pair.
Newly evaluated child returns remain a separate open obligation.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseWarmInheritedChild
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity tag pair)
open SourceEqualityNativeDemand
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativeGeneralCMHistory (AuthenticEntry)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Inherited B/P hit]
The actual old cold query supplies the earlier source result law.
Its endpoint inventory derives the original pattern Profile. Source body
readback excludes the reference-alias case. No caller supplies these laws.
The old returned cell and actual later memo hit refer to the same payload.
This lemma closes only the inherited-hit branch, not a fresh evaluation.
-/

/-- The same actual inherited B/P hit excludes its current source pair. -/
theorem inherited_body_pattern_hit_has_no_current_pair
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap machine.heap)
    (oldRootDomain : oldRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (oldLeftAvailable : Available machine.heap oldRoot.left)
    (oldRightAvailable : Available machine.heap oldRoot.right)
    (oldLeftClosed : oldRoot.left.free = []) (oldRightClosed : oldRoot.right.free = [])
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (oldFuel oldCount : Nat) (oldValue : Node) (oldSnapshot : Checked width)
    (oldBound : oldCount ≤ oldFuel)
    (oldInputs : InputsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldFields : FieldsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldActual : Trace oldCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) (.code (.pure oldValue)) oldSnapshot)
    (pattern : Node) (patternId : Nat)
    (patternAvailable : Available oldSnapshot.native.machine.heap pattern)
    (patternClosed : pattern.free = []) (patternIdentity : identity pattern = some patternId)
    (patternKind : tag pattern = 1 ∨ tag pattern = 3)
    (universeFirst : Bool) (newRoot : NodeRequest Symbol Guard)
    (newFuel newUsed : Nat) (beforeNew reader : Checked width)
    (next : Node → Code Symbol Guard Node)
    (handle : Nat) (value : Node)
    (chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (newBound : newUsed + 2 ≤ newFuel) :
    let universeValue : Node := .mu entry body depth ordinary
    let childLeft := if universeFirst then body else pattern
    let childRight := if universeFirst then pattern else body
    let first := if universeFirst then entry.identity else patternId
    let second := if universeFirst then patternId else entry.identity
    let binder := pair entry.identity patternId
    let entered := SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    let childRequest : NodeRequest Symbol Guard := ⟨entered.1, childLeft, childRight⟩
    let enterNext := fun domain =>
      (requestNode domain childLeft childRight).bind (fun value => .optionalBinder binder value next)
    Trace newUsed (.code (.node newRoot .pure)) oldSnapshot
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then universeValue else pattern)
        (if universeFirst then pattern else universeValue) first second enterNext)) beforeNew →
    Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain
      (if universeFirst then universeValue else pattern)
      (if universeFirst then pattern else universeValue) first second enterNext)) beforeNew
      (.code ((requestNode entered.1 childLeft childRight).bind
        (fun value => .optionalBinder binder value next))) reader →
    oldSnapshot.native.nodes.cells handle = some ⟨childRequest, .returned value⟩ →
    lookupNode width childRequest reader.native = (.memoized handle, chosen) →
    demandNode handle chosen = (.ready value, running) →
    AuthenticEntry (width := width) oldRoot machine operations oldCount
      entry body depth ordinary pattern patternId entered.1 ∧
    Reference.intersection binder.1 binder.2 ∉ value.free ∧
    reader.native.nodes.cells handle = some ⟨childRequest, .returned value⟩ ∧
    Trace (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot
      (.code ((requestNode entered.1 childLeft childRight).bind
        (fun value => .optionalBinder binder value next))) reader ∧
    SourceEqualityNativeDemand.step (.code (.node childRequest .pure)) reader =
      .yielded (.code (.pure value)) ⟨running, reader.operations⟩ ∧
    newUsed + 2 ≤ newFuel
 := by
  dsimp only
  intro newPrefix newEntry oldCell selected demanded
  let universeValue : Node := .mu entry body depth ordinary
  let childLeft := if universeFirst then body else pattern
  let childRight := if universeFirst then pattern else body
  let binder := pair entry.identity patternId
  let entered := SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let childRequest : NodeRequest Symbol Guard := ⟨entered.1, childLeft, childRight⟩
  let enterNext := fun domain =>
    (requestNode domain childLeft childRight).bind (fun value => .optionalBinder binder value next)
  change oldSnapshot.native.nodes.cells handle = some ⟨childRequest, .returned value⟩ at oldCell
  change lookupNode width childRequest reader.native = (.memoized handle, chosen) at selected
  have initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid
      (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have oldPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension oldActual initialPhysical).1
  have oldLeftProfile : Profile entry.identity oldRoot.left :=
    ⟨oldLeftClosed,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        machine.heap machineValid.1.coherent pastInventory oldRoot.left oldLeftAvailable oldLeftClosed⟩
  have oldRightProfile : Profile entry.identity oldRoot.right :=
    ⟨oldRightClosed,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        machine.heap machineValid.1.coherent pastInventory oldRoot.right oldRightAvailable oldRightClosed⟩
  have oldMuUnchanged :=
    SourceSynthesisCurrentUniverseNativeAllocation.original_universe_cold_query_no_new_mu
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine machineValid sourceGrowth oldRootDomain oldLeftProfile oldRightProfile
      operations operationsValid oldFuel oldInputs oldFields
  have readerInventory : InternedShallowHeap.NoNewMu sourceHeap oldSnapshot.native.machine.heap :=
    InternedShallowHeap.noNewMu_trans pastInventory
      (oldMuUnchanged.2 oldCount (.code (.pure oldValue)) oldSnapshot oldBound oldActual)
  have patternProfile : Profile entry.identity pattern :=
    ⟨patternClosed,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        oldSnapshot.native.machine.heap oldPhysical.machine.1.coherent readerInventory
        pattern patternAvailable patternClosed⟩
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have universeClosed : universeValue.free = [] := by
    change (Value.mu entry body depth ordinary).free = []
    rw [bodyShape]
    simp [Value.free]
  have bodyNotReference : body ≠ .reference (.interned entry.identity) := by
    intro same
    rw [bodyShape] at same
    cases same
  have inherited :=
    SourceCurrentAllocatedNativePastGammaEqualEntryPayload.closed_root_cold_returned_mixed_profile_after_later_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine oldRootDomain ⟨oldLeftClosed, oldRightClosed⟩ universeClosed
      machineValid sourceGrowth operations operationsValid oldFuel oldCount (.code (.pure oldValue))
      oldSnapshot oldBound oldActual oldInputs oldFields handle childRequest value oldCell
      pattern patternClosed patternId patternIdentity patternKind universeFirst enterNext newRoot newFuel newUsed
      beforeNew reader
      (.code ((requestNode entered.1 childLeft childRight).bind
        (fun value => .optionalBinder binder value next)))
      (by omega) newPrefix newEntry rfl body pattern (Or.inl rfl) patternProfile (Nat.le_refl _)
      (by intro impossible; exact False.elim (bodyNotReference impossible))
      (by
        change ((if universeFirst then body else pattern) = body ∧
            (if universeFirst then pattern else body) = pattern) ∨
          ((if universeFirst then body else pattern) = pattern ∧
            (if universeFirst then pattern else body) = body)
        cases universeFirst with
        | false => exact Or.inr ⟨rfl, rfl⟩
        | true => exact Or.inl ⟨rfl, rfl⟩)
  obtain ⟨authentic, valueProfile, kept, warmSpan, _entryBound⟩ := inherited
  have absent : Reference.intersection binder.1 binder.2 ∉ value.free := by
    rw [valueProfile.1]
    exact List.not_mem_nil
  have hit : SourceEqualityNativeDemand.step (.code (.node childRequest .pure)) reader =
      .yielded (.code (.pure value)) ⟨running, reader.operations⟩ := by
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
      selected, demanded, SourceEqualityNativeDemand.lift]
  exact ⟨authentic, absent, kept, warmSpan, hit, newBound⟩

end MicroCFTA.SourceSynthesisCurrentUniverseWarmInheritedChild

#check @MicroCFTA.SourceSynthesisCurrentUniverseWarmInheritedChild.inherited_body_pattern_hit_has_no_current_pair
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseWarmInheritedChild.inherited_body_pattern_hit_has_no_current_pair
