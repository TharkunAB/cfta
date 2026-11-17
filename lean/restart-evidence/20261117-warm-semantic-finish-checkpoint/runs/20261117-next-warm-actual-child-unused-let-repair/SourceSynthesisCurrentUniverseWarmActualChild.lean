import MicroCFTA.SourceSynthesisCurrentUniverseWarmInheritedChild
import MicroCFTA.SourceCurrentNativeWarmCMHistory
import MicroCFTA.SourceCurrentNativeOrderedOriginalEntry

namespace MicroCFTA.SourceSynthesisCurrentUniverseWarmInheritedChild
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity tag pair)
open SourceEqualityNativeDemand
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
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

/- Note [Actual warm body-pattern child]
The actual entry and completed child form one bounded root history.
Its final control is the literal optional continuation of that child.
The source warm cache law applies to that whole actual history.
The same child's retained returned cell supplies its result Profile.
-/

private theorem actual_child_closed_codec (value : Node) (closed : value.free = []) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value <;> simp_all [Value.free, Value.referenceOf, IntersectionFlatMemoKey.input]

theorem next_warm_actual_body_pattern_child_has_no_current_pair
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
    (newRootDomain : newRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (newLeftAvailable : Available oldSnapshot.native.machine.heap newRoot.left)
    (newRightAvailable : Available oldSnapshot.native.machine.heap newRoot.right)
    (newLeftClosed : newRoot.left.free = []) (newRightClosed : newRoot.right.free = [])
    (newInputs : InputsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (newFields : FieldsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (childFuel childCount : Nat) (value : Node) (childAfter : Checked width)
    (newBound : newUsed + 1 + childFuel ≤ newFuel)
    (childBound : childCount ≤ childFuel) :
    let universeValue : Node := .mu entry body depth ordinary
    let childLeft := if universeFirst then body else pattern
    let childRight := if universeFirst then pattern else body
    let first := if universeFirst then entry.identity else patternId
    let second := if universeFirst then patternId else entry.identity
    let binder := pair entry.identity patternId
    let entered := SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    let _childRequest : NodeRequest Symbol Guard := ⟨entered.1, childLeft, childRight⟩
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
    Trace childCount (.code (requestNode entered.1 childLeft childRight)) reader
      (.code (.pure value)) childAfter →
    Reference.intersection binder.1 binder.2 ∉ value.free
 := by
  dsimp only
  intro newPrefix newEntry childActual
  let universeValue : Node := .mu entry body depth ordinary
  let childLeft := if universeFirst then body else pattern
  let childRight := if universeFirst then pattern else body
  let binder := pair entry.identity patternId
  let entered := SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let childRequest : NodeRequest Symbol Guard := ⟨entered.1, childLeft, childRight⟩
  let enterNext := fun domain =>
    (requestNode domain childLeft childRight).bind (fun value => .optionalBinder binder value next)
  let optionalNext : Node → Code Symbol Guard Node := fun result => .optionalBinder binder result next
  let horizon := newUsed + 1 + childCount
  have _retainedNewRoot := And.intro newRootDomain
    (And.intro newLeftAvailable (And.intro newRightAvailable (And.intro newLeftClosed newRightClosed)))
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
  have bodyNotReference : body ≠ .reference (.interned entry.identity) := by
    intro same
    rw [bodyShape] at same
    cases same
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyShape]
    exact ⟨.node bodyEntry.identity, rfl⟩
  have beforePhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension newPrefix oldPhysical).1
  have ordered := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary pattern patternClosed patternId patternIdentity patternKind universeFirst
    enterNext 0 beforeNew reader (.code (enterNext entered.1)) beforePhysical newEntry
  have actualEntry : SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt (width := width)
      newRoot oldSnapshot horizon entry body depth ordinary pattern patternId entered.1 := by
    refine ⟨patternClosed, patternIdentity, patternKind, universeFirst, newUsed, beforeNew, enterNext, ?_⟩
    dsimp only
    exact ⟨by dsimp only [horizon]; omega, newPrefix, ordered.1, ordered.2.2.1, rfl⟩
  have childQualified : SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt (width := width)
      newRoot oldSnapshot horizon entry body depth ordinary childRequest := by
    refine ⟨pattern, patternId, body, pattern, actualEntry, Or.inl rfl,
      patternProfile, Nat.le_refl _, ?_, ?_⟩
    · intro impossible
      exact False.elim (bodyNotReference impossible)
    · cases universeFirst with
      | false => exact Or.inr ⟨rfl, rfl⟩
      | true => exact Or.inl ⟨rfl, rfl⟩
  have childOrigin : Steps (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot
      (.code ((requestNode entered.1 childLeft childRight).bind optionalNext)) reader := by
    exact (newPrefix.trans newEntry).steps
  have actualHorizon : Trace horizon (.code (.node newRoot .pure)) oldSnapshot
      (.code (.optionalBinder binder value next)) childAfter := by
    have joined := (newPrefix.trans newEntry).trans (childActual.bind optionalNext)
    simpa only [horizon, Control.bind, Code.bind, optionalNext] using joined
  have horizonBound : horizon ≤ newFuel := by dsimp only [horizon]; omega
  have wholeLaws := SourceCurrentNativeWarmCMHistory.current_stored_universe_warm_cm_returned_at_every_actual_prefix
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine oldRootDomain ⟨oldLeftClosed, oldRightClosed⟩ machineValid sourceGrowth pastInventory
    operations operationsValid oldFuel oldCount (.code (.pure oldValue)) oldSnapshot oldBound oldInputs oldFields oldActual
    newRoot newFuel horizon (.code (.optionalBinder binder value next)) childAfter horizonBound
    newInputs newFields actualHorizon
  dsimp only at wholeLaws
  obtain ⟨firstInput, leftCodec⟩ : ∃ input,
      IntersectionFlatMemoKey.input childLeft.referenceOf = some input := by
    cases universeFirst with
    | false => exact actual_child_closed_codec pattern patternClosed
    | true => exact bodyCodec
  obtain ⟨secondInput, rightCodec⟩ : ∃ input,
      IntersectionFlatMemoKey.input childRight.referenceOf = some input := by
    cases universeFirst with
    | false => exact bodyCodec
    | true => exact actual_child_closed_codec pattern patternClosed
  have keyed : ∃ key, SourceRecursiveIntersectionMemo.requestKey width
      entered.1 childLeft childRight = some key := by
    exact ⟨_, IntersectionFlatMemoKeyDomain.sourceKey_complete width entered.1 _ _
      firstInput secondInput leftCodec rightCodec⟩
  obtain ⟨childKey, childKeyEq⟩ := keyed
  have observed := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
    (SourceCurrentNativeWarmCMDefinitions.NodeResult (width := width)
      newRoot oldSnapshot horizon entry body depth ordinary)
    (SourceCurrentNativeWarmCMDefinitions.EdgeResult (width := width)
      newRoot oldSnapshot horizon entry body depth ordinary)
    newRoot oldSnapshot oldPhysical newFuel horizon (newUsed + 1) childCount
    (.code (.optionalBinder binder value next)) childAfter horizonBound actualHorizon wholeLaws.1
    childRequest childKey childKeyEq optionalNext reader childAfter value
    (by dsimp only [horizon]; omega) childOrigin childActual.steps
  have valueProfile : Profile entry.identity value := observed.1.2 childQualified
  rw [valueProfile.1]
  exact List.not_mem_nil

end MicroCFTA.SourceSynthesisCurrentUniverseWarmInheritedChild
