import MicroCFTA.SourcePruningEnumerationAction
import MicroCFTA.SourceCurrentAllocatedQueryMemo
import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourceCurrentNativeNumericalSeedInvariant

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationAction
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/- Note [Original-fuel narrowing between source queries]
The selected prefix reads source rows at the supplied native fuel.
Every reader outcome has a checked NoNewMu receipt in the prepared fragment.
Filtering constructs only an ordinary node. It introduces no Mu record.
The computed enumeration action does not run a native query.
The literal caller advance keeps both native tables and the domain cache.
The accepted original build derives Prepared. Past Seeds retains it here.
The next worker induction must supply this actual lookup and past invariant.
This local component does not prove every worker admission or inhabitance.
-/

private theorem narrowAt_noNewMu
    (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (fuel : Nat) (key : Key) (value : Node) (before : State Symbol Constraint)
    (facts : InternedNestedFacts.Facts before)
    (prepared : MergedPhysicalWarmup.Prepared before)
    (available : Available before value) :
    InternedShallowHeap.NoNewMu before
      (SourcePruningNativeView.narrowAt fits admits fuel key value before).state := by
  have retained := (MergedFreshOrdinaryExposure.nodeEdges_verified
    fuel value before facts prepared available).unchanged
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows middle =>
      have first : InternedShallowHeap.NoNewMu before middle := by
        simpa only [actual, MergedSourceExposure.Result.state] using retained
      simpa only [SourcePruningNativeView.narrowAt, actual,
        MergedSourceComparison.Result.state] using
          InternedShallowHeap.noNewMu_trans first
            (InternedShallowHeap.makeNode_noNewMu
              (rows.filter (SourcePruningNativeView.keeps fits admits key)) middle)
  | unresolved name after | pending key after | exhausted after =>
      simpa only [SourcePruningNativeView.narrowAt, actual,
        MergedSourceExposure.Result.state, MergedSourceComparison.Result.state] using retained

private theorem outer_narrow_noNewMu
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (fuel uv : Nat) (value : Node) (before : State Symbol Constraint)
    (facts : InternedNestedFacts.Facts before)
    (prepared : MergedPhysicalWarmup.Prepared before)
    (available : Available before value) :
    InternedShallowHeap.NoNewMu before
      (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before).state := by
  by_cases typed : uv ∈ metadata.types
  · rw [SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value before typed]
    exact InternedShallowHeap.noNewMu_refl before
  · cases value with
    | mu => exact InternedShallowHeap.noNewMu_refl before
    | empty | reference | node | union =>
        rw [SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata fuel uv _ before
          (by intro entry body depth ordinary impossible; cases impossible) typed]
        exact narrowAt_noNewMu fits admits fuel (holeKey metadata.typing uv) _ before
          facts prepared available

private theorem prepare_noNewMu
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (oldValue : Node) (before : State Symbol Constraint)
    (facts : InternedNestedFacts.Facts before)
    (prepared : MergedPhysicalWarmup.Prepared before)
    (available : Available before oldValue) :
    InternedShallowHeap.NoNewMu before
      (prepare (EnumGuard := Constraint) holeKey fits admits metadata nativeFuel representativeFuel
        uv oldHandle scs oldValue before).state := by
  have retained := outer_narrow_noNewMu holeKey fits admits metadata nativeFuel uv oldValue
    before facts prepared available
  cases actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue before with
  | done value after | failed fault after =>
      simpa only [prepare, prepareWithNarrow, actual, MergedSourceComparison.Result.state] using retained

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem lookup_available
    (heap : State Symbol Constraint) (handle : Nat) (value : Node)
    (facts : InternedNestedFacts.Facts heap)
    (present : lookupNode heap handle = some value) : Available heap value := by
  cases handle with
  | zero =>
      have same : Value.empty = value := Option.some.inj present
      rw [← same]
      exact InternedProbeProvenance.empty_available heap
  | succ identity =>
      cases issued : heap.nodes.issued identity with
      | none =>
          simp only [lookupNode, issued] at present
          cases present
      | some key =>
          cases canonical : heap.nodes.table key with
          | none =>
              simp only [lookupNode, issued, canonical] at present
              cases present
          | some entry =>
              by_cases winner : entry.identity = identity
              · exact facts.cached.nodes key value (by
                  simpa only [lookupNode, issued, canonical, ite_eq_left winner] using present)
              · simp only [lookupNode, issued, canonical, ite_eq_right winner] at present
                cases present

theorem original_source_prepare_endpoint_preserves_seeds
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Node) (bodyId : Nat)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (oldValue : Node) (caller : Caller width)
    (facts : InternedNestedFacts.Facts caller.checked.native.machine.heap)
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (pastSeeds : SourceCurrentNativeNumericalSeedInvariant.Seeds
      sourceHeap entry body depth ordinary bodyId caller.checked) :
    let prepared := prepare (EnumGuard := Constraint) holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked
        ⟨prepared.state, caller.checked.operations⟩) caller.fourth caller.merge
    InternedShallowHeap.NoNewMu caller.checked.native.machine.heap reached.checked.native.machine.heap ∧
      reached.checked.native.nodes = caller.checked.native.nodes ∧
      reached.checked.native.edges = caller.checked.native.edges ∧
      reached.checked.native.machine.domains = caller.checked.native.machine.domains ∧
      SourceCurrentNativeNumericalSeedInvariant.Seeds
        sourceHeap entry body depth ordinary bodyId reached.checked := by
  have sourcePrepared := SourceSynthesisCurrentUniverseOwnership.current_build_prepared
    lib query signed whole accepted rootValue sourceHeap built
  have currentPrepared := sourcePrepared.preserve pastSeeds.1
  have available := lookup_available caller.checked.native.machine.heap oldHandle oldValue facts decoded
  have unchanged := prepare_noNewMu holeKey fits admits metadata nativeFuel representativeFuel
    uv oldHandle scs oldValue caller.checked.native.machine.heap facts currentPrepared available
  dsimp only
  refine ⟨unchanged, rfl, rfl, rfl, ?_⟩
  unfold SourceCurrentNativeNumericalSeedInvariant.Seeds at pastSeeds ⊢
  dsimp only at pastSeeds ⊢
  refine ⟨InternedShallowHeap.noNewMu_trans pastSeeds.1 unchanged, ?_⟩
  exact pastSeeds.2

end MicroCFTA.SourcePruningEnumerationAction

namespace MicroCFTA.SourcePruningEnumerationAction
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/- Note [Narrowing growth is independent of native memo meaning]
Exposure retains the input heap records at every native outcome.
Filtering constructs one ordinary node at that actual exposure endpoint.
Mu and raw type skips retain the exact input heap.
Computing the enumeration action does not change the native heap.
-/

private theorem narrowAt_grows
    (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (fuel : Nat) (key : Key) (value : Node) (before : State Symbol Constraint)
    (facts : InternedNestedFacts.Facts before)
    (prepared : MergedPhysicalWarmup.Prepared before)
    (available : Available before value) :
    Grows before (SourcePruningNativeView.narrowAt fits admits fuel key value before).state
 := by
  have verified := MergedFreshOrdinaryExposure.nodeEdges_verified
    fuel value before facts prepared available
  have growth := verified.growth
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows middle =>
      have first : Grows before middle := by
        simpa only [actual, MergedSourceExposure.Result.state] using growth
      have middleFacts : InternedNestedFacts.Facts middle := by
        simpa only [actual, MergedSourceExposure.Result.state] using verified.facts
      have constructed := InternedConstructorTemplates.run_correct
        (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits key)))
        middle middleFacts.coherent.valid
      simpa only [SourcePruningNativeView.narrowAt, actual,
        MergedSourceComparison.Result.state] using
          InternedConstructorTemplates.grows_trans first constructed.2
  | unresolved name after | pending pendingKey after | exhausted after =>
      simpa only [SourcePruningNativeView.narrowAt, actual,
        MergedSourceExposure.Result.state, MergedSourceComparison.Result.state] using growth

private theorem outer_narrow_grows
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (fuel uv : Nat) (value : Node) (before : State Symbol Constraint)
    (facts : InternedNestedFacts.Facts before)
    (prepared : MergedPhysicalWarmup.Prepared before)
    (available : Available before value) :
    Grows before
      (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before).state
 := by
  by_cases typed : uv ∈ metadata.types
  · rw [SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value before typed]
    exact InternedConstructorTemplates.grows_refl before
  · cases value with
    | mu => exact InternedConstructorTemplates.grows_refl before
    | empty | reference | node | union =>
        rw [SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata fuel uv _ before
          (by intro entry body depth ordinary impossible; cases impossible) typed]
        exact narrowAt_grows fits admits fuel (holeKey metadata.typing uv) _ before
          facts prepared available

/-- The literal advanced caller grows at every actual narrowing preparation outcome. -/
theorem prepare_endpoint_grows
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (oldValue : Node) (caller : Caller width)
    (facts : InternedNestedFacts.Facts caller.checked.native.machine.heap)
    (prepared : MergedPhysicalWarmup.Prepared caller.checked.native.machine.heap)
    (available : Available caller.checked.native.machine.heap oldValue) :
    let actual := prepare (EnumGuard := Constraint) holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked
        ⟨actual.state, caller.checked.operations⟩) caller.fourth caller.merge
    Grows caller.checked.native.machine.heap reached.checked.native.machine.heap
 := by
  change Grows caller.checked.native.machine.heap
    (prepare (EnumGuard := Constraint) holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap).state
  have growth := outer_narrow_grows holeKey fits admits metadata nativeFuel uv oldValue
    caller.checked.native.machine.heap facts prepared available
  cases actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue
      caller.checked.native.machine.heap with
  | done value after | failed fault after =>
      simpa only [prepare, prepareWithNarrow, actual, MergedSourceComparison.Result.state] using growth

end MicroCFTA.SourcePruningEnumerationAction
