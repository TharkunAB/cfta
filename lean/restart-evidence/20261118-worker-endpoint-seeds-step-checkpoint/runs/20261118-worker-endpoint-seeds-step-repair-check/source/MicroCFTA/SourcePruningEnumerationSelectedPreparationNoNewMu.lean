import MicroCFTA.SourcePruningEnumerationSelectedPreparation
import MicroCFTA.SourcePruningEnumerationSharedPreparedContinuations
import MicroCFTA.SourcePruningEnumerationEntryRecordedBucketOrigin
import MicroCFTA.MergedFreshOrdinaryExposure
import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourceCurrentNativeNumericalSeedInvariant

set_option autoImplicit false

/- Note [Original-fuel selected preparation between native queries]
Selected preparation can change the native heap without running a query.
The prepared source fragment makes each unfolding add no Mu record.
The proof uses the actual exposure result at the supplied native fuel.
Failed, pending and exhausted results retain their actual returned heaps.
The caller advance retains both complete native memo tables.
The original accepted build derives Prepared for the source heap.
Past Seeds transfers Prepared to this actual caller heap through NoNewMu.
The same tables then retain all five Returned clauses of Seeds.
This component does not attach Seeds to every eager-worker phase.
It does not prove native inhabitance or one joint finite assignment.
-/

namespace MicroCFTA.SourcePruningEnumerationSelectedValue
open InternedConstructorTemplates InternedProbeProvenance
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-! The actual native preparation retains its supplied fuel. -/

theorem run_noNewMu
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (facts : InternedNestedFacts.Facts before)
    (prepared : MergedPhysicalWarmup.Prepared before)
    (available : Available before value) :
    InternedShallowHeap.NoNewMu before (run fuel value before).state := by
  cases value with
  | empty | reference | node => exact InternedShallowHeap.noNewMu_refl before
  | mu entry body depth ordinary =>
      have retained := MergedPhysicalWarmup.unfold_noNewMu
        (.mu entry body depth ordinary) before prepared available
      rw [← InternedFreshOrdinaryStoredSubstitution.unfold_eq
        (.mu entry body depth ordinary) before prepared available] at retained
      cases actual : InternedFreshOrdinaryStoredSubstitution.unfold
          (.mu entry body depth ordinary) before with
      | done result after | pending key after =>
          simpa only [run, actual, InternedNestedConstruction.Outcome.state,
            MergedSourceComparison.Result.state] using retained
  | union entry members depth free =>
      have retained := (MergedFreshOrdinaryExposure.nodeEdges_verified fuel
        (.union entry members depth free) before facts prepared available).unchanged
      cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel
          (.union entry members depth free) before with
      | done rows middle =>
          have first : InternedShallowHeap.NoNewMu before middle := by
            simpa only [actual, MergedSourceExposure.Result.state] using retained
          simpa only [run, actual, MergedSourceComparison.Result.state] using
            InternedShallowHeap.noNewMu_trans first
              (InternedShallowHeap.makeNode_noNewMu rows middle)
      | unresolved name after | pending key after | exhausted after =>
          simpa only [run, actual, MergedSourceExposure.Result.state,
            MergedSourceComparison.Result.state] using retained

end MicroCFTA.SourcePruningEnumerationSelectedValue

namespace MicroCFTA.SourcePruningEnumerationSelectedPreparation
open EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList

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

/-- Actual entry and preparation retain the native memo tables at every outcome. -/
theorem run_endpoint_no_new_mu_and_tables
    (entryFuel nativeFuel uv : Nat) (caller : Caller width) (before : Cached) (queries : Queries)
    (facts : InternedNestedFacts.Facts caller.checked.native.machine.heap)
    (prepared : MergedPhysicalWarmup.Prepared caller.checked.native.machine.heap)
    (total : UnionFind.Total before.core.representatives) :
    let endpoint := SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint caller queries
      (run entryFuel nativeFuel uv caller before)
    InternedShallowHeap.NoNewMu caller.checked.native.machine.heap endpoint.1.checked.native.machine.heap ∧
      endpoint.1.checked.native.nodes = caller.checked.native.nodes ∧
      endpoint.1.checked.native.edges = caller.checked.native.edges ∧
      endpoint.1.checked.native.machine.domains = caller.checked.native.machine.domains ∧
      endpoint.1.checked.operations = caller.checked.operations ∧
      endpoint.2 = queries := by
  unfold run
  generalize reading : ExceptT.run (SourcePruningEnumerationEntry.enter
    caller.checked.native.machine.heap entryFuel uv before.core) = raw
  cases raw with
  | nil => exact ⟨InternedShallowHeap.noNewMu_refl _, rfl, rfl, rfl, rfl, rfl⟩
  | cons first rest =>
      cases rest with
      | cons another remaining =>
          cases first <;> exact ⟨InternedShallowHeap.noNewMu_refl _, rfl, rfl, rfl, rfl, rfl⟩
      | nil =>
          cases first with
          | error fault => exact ⟨InternedShallowHeap.noNewMu_refl _, rfl, rfl, rfl, rfl, rfl⟩
          | ok pair =>
              obtain ⟨⟨target, handle, scs, value⟩, entered⟩ := pair
              have actual : Success (SourcePruningEnumerationEntry.enter
                  caller.checked.native.machine.heap entryFuel uv) before.core
                  (target, handle, scs, value) entered := by
                rw [Success, reading]
                exact List.mem_singleton_self _
              obtain ⟨_size, _path, _stored, _values, decoded, _ancestry, _expansion⟩ :=
                SourcePruningEnumerationEntry.enter_recorded_bucket_origin
                  caller.checked.native.machine.heap entryFuel uv before.core entered
                  target handle scs value total actual
              have available := lookup_available caller.checked.native.machine.heap handle value facts decoded
              have unchanged := SourcePruningEnumerationSelectedValue.run_noNewMu
                nativeFuel value caller.checked.native.machine.heap facts prepared available
              have tables := SourceCurrentAllocatedQueryMemo.advance_tables caller.checked
                ⟨(SourcePruningEnumerationSelectedValue.run nativeFuel value
                    caller.checked.native.machine.heap).state, caller.checked.operations⟩
              exact ⟨unchanged, tables.1, tables.2.1, tables.2.2, rfl, rfl⟩

/-- An accepted source and past Seeds derive Seeds at the literal preparation endpoint. -/
theorem original_source_run_endpoint_preserves_seeds
    [DecidableEq Symbol]
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Node) (bodyId : Nat)
    (entryFuel nativeFuel uv : Nat) (caller : Caller width) (before : Cached) (queries : Queries)
    (facts : InternedNestedFacts.Facts caller.checked.native.machine.heap)
    (total : UnionFind.Total before.core.representatives)
    (pastSeeds : SourceCurrentNativeNumericalSeedInvariant.Seeds
      sourceHeap entry body depth ordinary bodyId caller.checked) :
    SourceCurrentNativeNumericalSeedInvariant.Seeds sourceHeap entry body depth ordinary bodyId
      (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint caller queries
        (run entryFuel nativeFuel uv caller before)).1.checked := by
  have sourcePrepared := SourceSynthesisCurrentUniverseOwnership.current_build_prepared
    lib query signed whole accepted rootValue sourceHeap built
  have prepared := sourcePrepared.preserve pastSeeds.1
  have endpoint := run_endpoint_no_new_mu_and_tables
    entryFuel nativeFuel uv caller before queries facts prepared total
  unfold SourceCurrentNativeNumericalSeedInvariant.Seeds at pastSeeds ⊢
  dsimp only at pastSeeds ⊢
  refine ⟨InternedShallowHeap.noNewMu_trans pastSeeds.1 endpoint.1, ?_⟩
  simpa only [endpoint.2.1, endpoint.2.2.1] using pastSeeds.2

end MicroCFTA.SourcePruningEnumerationSelectedPreparation

namespace MicroCFTA.SourcePruningEnumerationSelectedValue
open InternedConstructorTemplates InternedProbeProvenance
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/- Note [Growth follows the actual selected preparation outcome]
The stored unfolding and exposure receipts retain their actual heap histories.
Node reconstruction extends the exact exposure endpoint.
The proof covers failed, pending and exhausted native outcomes.
NoNewMu does not supply these growth facts.
-/

private theorem actual_run_grows
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (facts : InternedNestedFacts.Facts before)
    (prepared : MergedPhysicalWarmup.Prepared before)
    (available : Available before value) :
    Grows before (run fuel value before).state
 := by
  cases value with
  | empty | reference | node => exact InternedConstructorTemplates.grows_refl before
  | mu entry body depth ordinary =>
      have growth := (InternedStoredSubstitution.unfold_verified
        (.mu entry body depth ordinary) before facts available).growth
      rw [← InternedFreshOrdinaryStoredSubstitution.unfold_eq
        (.mu entry body depth ordinary) before prepared available] at growth
      cases actual : InternedFreshOrdinaryStoredSubstitution.unfold
          (.mu entry body depth ordinary) before with
      | done result after | pending key after =>
          simpa only [run, actual, InternedNestedConstruction.Outcome.state,
            MergedSourceComparison.Result.state] using growth
  | union entry members depth free =>
      have verified := MergedFreshOrdinaryExposure.nodeEdges_verified fuel
        (.union entry members depth free) before facts prepared available
      have growth := verified.growth
      cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel
          (.union entry members depth free) before with
      | done rows middle =>
          have first : Grows before middle := by
            simpa only [actual, MergedSourceExposure.Result.state] using growth
          have middleFacts : InternedNestedFacts.Facts middle := by
            simpa only [actual, MergedSourceExposure.Result.state] using verified.facts
          have constructed := InternedConstructorTemplates.run_correct
            (makeNode rows) middle middleFacts.coherent.valid
          simpa only [run, actual, MergedSourceComparison.Result.state] using
            InternedConstructorTemplates.grows_trans first constructed.2
      | unresolved name after | pending key after | exhausted after =>
          simpa only [run, actual, MergedSourceExposure.Result.state,
            MergedSourceComparison.Result.state] using growth

end MicroCFTA.SourcePruningEnumerationSelectedValue

namespace MicroCFTA.SourcePruningEnumerationSelectedPreparation
open EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList

/-- Every actual selected preparation endpoint retains the input heap records. -/
theorem run_endpoint_grows
    (entryFuel nativeFuel uv : Nat) (caller : Caller width) (before : Cached) (queries : Queries)
    (facts : InternedNestedFacts.Facts caller.checked.native.machine.heap)
    (prepared : MergedPhysicalWarmup.Prepared caller.checked.native.machine.heap)
    (total : UnionFind.Total before.core.representatives) :
    Grows caller.checked.native.machine.heap
      (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint caller queries
        (run entryFuel nativeFuel uv caller before)).1.checked.native.machine.heap
 := by
  unfold run
  generalize reading : ExceptT.run (SourcePruningEnumerationEntry.enter
    caller.checked.native.machine.heap entryFuel uv before.core) = raw
  cases raw with
  | nil => exact InternedConstructorTemplates.grows_refl _
  | cons first rest =>
      cases rest with
      | cons another remaining =>
          cases first <;> exact InternedConstructorTemplates.grows_refl _
      | nil =>
          cases first with
          | error fault => exact InternedConstructorTemplates.grows_refl _
          | ok pair =>
              obtain ⟨⟨target, handle, scs, value⟩, entered⟩ := pair
              have actual : Success (SourcePruningEnumerationEntry.enter
                  caller.checked.native.machine.heap entryFuel uv) before.core
                  (target, handle, scs, value) entered := by
                rw [Success, reading]
                exact List.mem_singleton_self _
              obtain ⟨_size, _path, _stored, _values, decoded, _ancestry, _expansion⟩ :=
                SourcePruningEnumerationEntry.enter_recorded_bucket_origin
                  caller.checked.native.machine.heap entryFuel uv before.core entered
                  target handle scs value total actual
              have available := lookup_available caller.checked.native.machine.heap
                handle value facts decoded
              exact SourcePruningEnumerationSelectedValue.actual_run_grows
                nativeFuel value caller.checked.native.machine.heap facts prepared available

end MicroCFTA.SourcePruningEnumerationSelectedPreparation

#print axioms MicroCFTA.SourcePruningEnumerationSelectedPreparation.run_endpoint_grows
