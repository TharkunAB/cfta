import MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEventResources
import MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEventResources
import MicroCFTA.SourceCurrentNativeNumericalSeedClosure
import MicroCFTA.SourceSynthesisCurrentRetainedSharedEmptySkip
import MicroCFTA.SourceCurrentAllocatedTargetCallerCreditResources

namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents
open Cache EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open EnumerationState (Suspended)
open SourcePruningEnumerationNodes
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityNativeDemand (Control)
open SourceRecursiveIntersectionThunks (NodeRequest)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl SourceRecursiveIntersectionCode
open InternedBinderProtocol (NodeKey)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Profile" => SourceCurrentAllocatedNativeResourceForecast.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Source Seeds through the actual incoming query]
The observer has one native query site and retains its original input tuple.
Current resources admit that same query at the supplied native fuel.
The source closure retains Seeds at every native outcome and actual prefix.
An actual completed query supplies its own Post and query availability.
Source NoNewMu then makes the actual enabled check skip at the supplied p/h.
The returned incoming caller therefore keeps that queried native state.
No future cache law or final Seeds premise is used.
-/

omit [DecidableEq Node] in
private theorem actual_trace_source_growth
    (sourceHeap : State Symbol Constraint)
    (control rest : Control Node) (before after : Checked (bits + 2)) (count : Nat)
    (trace : Trace count control before rest after) :
    SourceCurrentAllocatedNativePhysicalCache.Valid before.native →
      Grows sourceHeap before.native.machine.heap → Grows sourceHeap after.native.machine.heap
 := by
  induction trace with
  | refl =>
      intro _valid growth
      exact growth
  | cons start before next middle final after count inputs actual rest ih =>
      intro valid growth
      have oneValid := SourceCurrentAllocatedNativePhysicalExecution.step_valid
        start before valid inputs
      have oneExtension := SourceCurrentAllocatedNativePhysicalExecution.step_extension
        start before valid.machine inputs
      have middleValid : SourceCurrentAllocatedNativePhysicalCache.Valid middle.native := by
        simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using oneValid
      have middleExtension : Extension before.native.machine middle.native.machine := by
        simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using oneExtension
      exact ih middleValid (grows_trans growth middleExtension.heap)

omit [DecidableEq Node] in
private theorem actual_query_source_seeds
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (before : Checked (bits + 2)) (profile : Profile)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (fits : Fits profile before)
    (admitted : SourceCurrentAllocatedNativeCreditProfile.Admits bits profile)
    (sourceGrowth : Grows sourceHeap before.native.machine.heap)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId before)
    (left right : Node)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) (fuel : Nat) :
    (Seeds sourceHeap entry body depth ordinary bodyId
        (SourceEqualityNativeDemand.execute fuel
          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before).state ∧
      Grows sourceHeap (SourceEqualityNativeDemand.execute fuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before).state.native.machine.heap) ∧
    ∀ (count : Nat) (rest : Control Node) (after : Checked (bits + 2)),
      count ≤ fuel → Trace count
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before rest after →
      Seeds sourceHeap entry body depth ordinary bodyId after ∧
        Grows sourceHeap after.native.machine.heap
 := by
  let request : NodeRequest Symbol Constraint :=
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have seeds := SourceCurrentNativeNumericalSeedInvariant.original_universe_resource_admitted_request_seeds
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity request before sourceGrowth pastSeeds rfl
    ⟨leftAvailable, rightAvailable⟩ ⟨leftClosed, rightClosed⟩ profile ready fits admitted fuel
  have plans := SourcePruningEnumerationNativeRequestFields.admitted_request_plans
    profile before ready fits admitted left right leftAvailable rightAvailable leftClosed rightClosed fuel
  have physical := SourceCurrentAllocatedNativePhysicalExecution.execute_invariants
    fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before
    ready.good.native ready.good.heap plans.1
  have endpointSeeds : Seeds sourceHeap entry body depth ordinary bodyId
      (SourceEqualityNativeDemand.execute fuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before).state := by
    exact seeds.1
  refine ⟨⟨endpointSeeds, grows_trans sourceGrowth physical.2.1.heap⟩, ?_⟩
  intro count rest after bounded actual
  exact ⟨seeds.2 count rest after bounded actual,
    actual_trace_source_growth sourceHeap _ _ before after count actual ready.good.native sourceGrowth⟩

theorem original_source_observe_preserves_seeds
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed 1)
    (sourceGrowth : Grows sourceHeap beforeCaller.checked.native.machine.heap)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId beforeCaller.checked)
    (checkEmpty : Bool) (representativeFuel nativeFuel p h uv : Nat)
    (incoming : Node) (incomingScs : List Suspended)
    (available : Available beforeCaller.checked.native.machine.heap incoming)
    (closed : incoming.free = []) :
    let observed := observe checkEmpty representativeFuel nativeFuel p h
      beforeCaller before uv incoming incomingScs memos.query
    observed.1 = SourcePruningEnumerationSharedIncomingNode.run
      checkEmpty representativeFuel nativeFuel p h
      beforeCaller before uv incoming incomingScs memos.query ∧
    (Seeds sourceHeap entry body depth ordinary bodyId observed.1.2.1.checked ∧
      Grows sourceHeap observed.1.2.1.checked.native.machine.heap) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      start = beforeCaller ∧ saved = memos.query ∧ left = incoming ∧
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked ∧
      (Seeds sourceHeap entry body depth ordinary bodyId actual.state ∧
        Grows sourceHeap actual.state.native.machine.heap) ∧
      ∀ (count : Nat) (rest : Control Node) (after : Checked (bits + 2)),
        count ≤ nativeFuel → Trace count
          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked rest after →
        Seeds sourceHeap entry body depth ordinary bodyId after ∧
          Grows sourceHeap after.native.machine.heap
 := by
  dsimp only
  have literal := observe_exact checkEmpty representativeFuel nativeFuel p h
    beforeCaller before uv incoming incomingScs memos.query
  have eventResources := observe_query_resources seed formulas solver inventory beforeCaller before memos
    initial realized fits reserved checkEmpty representativeFuel nativeFuel p h uv incoming incomingScs
    available closed
  refine ⟨literal.1, ?_, ?_⟩
  · cases rootRead : UnionFind.findRoot representativeFuel before.representatives uv with
    | none =>
        simp only [observe, rootRead]
        exact ⟨pastSeeds, sourceGrowth⟩
    | some found =>
        cases slotRead : before.values[found.representative]? with
        | none =>
            simp only [observe, rootRead, slotRead]
            exact ⟨pastSeeds, sourceGrowth⟩
        | some value =>
            cases value with
            | eliminated =>
                simp only [observe, rootRead, slotRead]
                exact ⟨pastSeeds, sourceGrowth⟩
            | enumerated fragment =>
                simp only [observe, rootRead, slotRead]
                exact ⟨pastSeeds, sourceGrowth⟩
            | unenumerated oldNode oldScs =>
                cases oldNode with
                | none =>
                    cases encoded : encodeNode incoming <;>
                      simp only [observe, rootRead, slotRead, encoded] <;>
                      exact ⟨pastSeeds, sourceGrowth⟩
                | some oldHandle =>
                    cases oldRead : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
                    | none =>
                        simp only [observe, rootRead, slotRead, oldRead]
                        exact ⟨pastSeeds, sourceGrowth⟩
                    | some old =>
                        obtain ⟨value, decoded, resident, oldClosed⟩ :=
                          realized found.representative oldHandle oldScs slotRead
                        have valueSame : value = old := Option.some.inj (decoded.symm.trans oldRead)
                        subst value
                        have native := actual_query_source_seeds
                          lib query signed whole accepted rootValue sourceHeap built
                          key entry body depth ordinary stored bodyId bodyIdentity beforeCaller.checked
                          seed.2 initial.ready fits reserved.head sourceGrowth pastSeeds incoming old
                          available resident closed oldClosed nativeFuel
                        cases nativeRead : SourceEqualityNativeDemand.execute nativeFuel
                            (.code (requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                            beforeCaller.checked with
                        | done value queried =>
                            have nativeFacts : Seeds sourceHeap entry body depth ordinary bodyId queried ∧
                                Grows sourceHeap queried.native.machine.heap := by
                              simpa only [nativeRead, SourceEqualityNativeDemand.Outcome.state] using native.1
                            obtain ⟨_next, _source, _roots, receipt, _post, _bounded, _mass⟩ :=
                              SourceCurrentAllocatedTargetQuery.raw_done_caller_admitted_resources
                                seed.2 nativeFuel formulas solver inventory beforeCaller queried incoming old value
                                memos initial fits reserved.head available resident closed oldClosed nativeRead
                            have skip :=
                              SourceSynthesisCurrentRootEmptyCheckGate.source_retained_available_shared_empty_check_skipped
                                lib query signed whole accepted rootValue sourceHeap built queried
                                receipt.ready.good.native.machine.1.coherent nativeFacts.1.1 value
                                receipt.available memos.query receipt.globals.query beforeCaller.fourth p h
                            cases checkEmpty with
                            | false =>
                                cases encoded : encodeNode value <;>
                                  simpa only [observe, rootRead, slotRead, oldRead, nativeRead,
                                    Bool.false_eq_true, ↓reduceIte,
                                    SourcePruningEnumerationSharedEnabledEmpty.Outcome.completed,
                                    SourcePruningEnumerationSharedEnabledEmpty.Outcome.state,
                                    SourceCurrentAllocatedPartialState.advance, encoded] using nativeFacts
                            | true =>
                                cases encoded : encodeNode value <;>
                                  simpa only [observe, rootRead, slotRead, oldRead, nativeRead, Bool.false_eq_true, ↓reduceIte,
                                    skip.2.1, SourcePruningEnumerationSharedEnabledEmpty.Outcome.completed,
                                    SourcePruningEnumerationSharedEnabledEmpty.Outcome.state,
                                    SourceCurrentAllocatedPartialState.advance, encoded] using nativeFacts
                        | yielded next queried =>
                            simpa only [observe, rootRead, slotRead, oldRead, nativeRead,
                              SourceEqualityNativeDemand.Outcome.state,
                              SourceCurrentAllocatedPartialState.advance] using native.1
                        | failed failure queried =>
                            simpa only [observe, rootRead, slotRead, oldRead, nativeRead,
                              SourceEqualityNativeDemand.Outcome.state,
                              SourceCurrentAllocatedPartialState.advance] using native.1
                        | constraintError message queried =>
                            simpa only [observe, rootRead, slotRead, oldRead, nativeRead,
                              SourceEqualityNativeDemand.Outcome.state,
                              SourceCurrentAllocatedPartialState.advance] using native.1
                        | blocked reason next queried =>
                            simpa only [observe, rootRead, slotRead, oldRead, nativeRead,
                              SourceEqualityNativeDemand.Outcome.state,
                              SourceCurrentAllocatedPartialState.advance] using native.1
  · intro start saved left right actual member
    obtain ⟨startSame, savedSame, leftSame, _ready, _fitted, _admitted,
        leftAvailable, rightAvailable, leftClosed, rightClosed, actualSame⟩ :=
      eventResources.2 start saved left right actual member
    subst start
    have native := actual_query_source_seeds
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity beforeCaller.checked seed.2 initial.ready fits reserved.head sourceGrowth
      pastSeeds left right leftAvailable rightAvailable leftClosed rightClosed nativeFuel
    refine ⟨rfl, savedSame, leftSame, actualSame, ?_, native.2⟩
    rw [actualSame]
    exact native.1

end MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents

namespace MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents
open Cache EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open EnumerationState (Suspended)
open SourcePruningEnumerationNodes
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityNativeDemand (Control)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl SourceRecursiveIntersectionCode
open InternedBinderProtocol (NodeKey)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Source Seeds through the actual dispatch query]
Both operands come from the same observed pending source and target slots.
Branches without a native query keep their original native caller.
The actual query reuses the source closure in this same owning file.
Its completed receipt makes the actual enabled check skip at the supplied p/h.
All native outcomes and bounded prefixes retain their original query input.
-/

theorem original_source_observe_preserves_seeds
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed 1)
    (sourceGrowth : Grows sourceHeap caller.checked.native.machine.heap)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId caller.checked)
    (checkEmpty : Bool) (nativeFuel p h source target : Nat) :
    let observed := observe checkEmpty nativeFuel p h caller before source target memos.query
    observed.1 = SourcePruningEnumerationSharedDispatch.dispatch
      checkEmpty nativeFuel p h caller before source target memos.query ∧
    (Seeds sourceHeap entry body depth ordinary bodyId observed.1.2.1.checked ∧
      Grows sourceHeap observed.1.2.1.checked.native.machine.heap) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      start = caller ∧ saved = memos.query ∧
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked ∧
      (Seeds sourceHeap entry body depth ordinary bodyId actual.state ∧
        Grows sourceHeap actual.state.native.machine.heap) ∧
      ∀ (count : Nat) (rest : Control Node) (after : SourceEqualityNativeDemand.State (bits + 2)),
        count ≤ nativeFuel → Trace count
          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked rest after →
        Seeds sourceHeap entry body depth ordinary bodyId after ∧
          Grows sourceHeap after.native.machine.heap
 := by
  dsimp only
  have literal := observe_exact checkEmpty nativeFuel p h caller before source target memos.query
  have eventResources := observe_query_resources seed formulas solver inventory caller before memos
    initial realized fits reserved checkEmpty nativeFuel p h source target
  have unchanged : Seeds sourceHeap entry body depth ordinary bodyId caller.checked ∧
      Grows sourceHeap caller.checked.native.machine.heap := ⟨pastSeeds, sourceGrowth⟩
  refine ⟨literal.1, ?_, ?_⟩
  · by_cases same : source = target
    · simpa [observe, same] using unchanged
    · cases sourceRead : before.values[source]? with
      | none => simpa [observe, same, sourceRead] using unchanged
      | some sourceValue =>
          cases sourceValue with
          | eliminated => simpa [observe, same, sourceRead] using unchanged
          | enumerated fragment =>
              cases targetRead : before.values[target]? <;>
                simpa [observe, same, sourceRead, targetRead] using unchanged
          | unenumerated sourceNode sourceScs =>
              cases targetRead : before.values[target]? with
              | none => simpa [observe, same, sourceRead, targetRead] using unchanged
              | some targetValue =>
                  cases targetValue with
                  | eliminated => simpa [observe, same, sourceRead, targetRead] using unchanged
                  | enumerated fragment => simpa [observe, same, sourceRead, targetRead] using unchanged
                  | unenumerated targetNode targetScs =>
                      cases sourceNode with
                      | none => simpa [observe, same, sourceRead, targetRead] using unchanged
                      | some sourceHandle =>
                          cases targetNode with
                          | none => simpa [observe, same, sourceRead, targetRead] using unchanged
                          | some targetHandle =>
                              cases leftRead : lookupNode caller.checked.native.machine.heap sourceHandle with
                              | none =>
                                  simpa [observe, same, sourceRead, targetRead, leftRead] using unchanged
                              | some left =>
                                  cases rightRead : lookupNode caller.checked.native.machine.heap targetHandle with
                                  | none =>
                                      simpa [observe, same, sourceRead, targetRead, leftRead, rightRead] using unchanged
                                  | some right =>
                                      obtain ⟨leftValue, leftDecoded, leftResident, leftClosed⟩ :=
                                        realized source sourceHandle sourceScs sourceRead
                                      have leftSame : leftValue = left :=
                                        Option.some.inj (leftDecoded.symm.trans leftRead)
                                      subst leftValue
                                      obtain ⟨rightValue, rightDecoded, rightResident, rightClosed⟩ :=
                                        realized target targetHandle targetScs targetRead
                                      have rightSame : rightValue = right :=
                                        Option.some.inj (rightDecoded.symm.trans rightRead)
                                      subst rightValue
                                      have native :=
                                        SourcePruningEnumerationSharedIncomingQueryEvents.actual_query_source_seeds
                                          lib query signed whole accepted rootValue sourceHeap built
                                          key entry body depth ordinary stored bodyId bodyIdentity caller.checked
                                          seed.2 initial.ready fits reserved.head sourceGrowth pastSeeds left right
                                          leftResident rightResident leftClosed rightClosed nativeFuel
                                      cases nativeRead : SourceEqualityNativeDemand.execute nativeFuel
                                          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
                                          caller.checked with
                                      | done value queried =>
                                          have nativeFacts : Seeds sourceHeap entry body depth ordinary bodyId queried ∧
                                              Grows sourceHeap queried.native.machine.heap := by
                                            simpa only [nativeRead, SourceEqualityNativeDemand.Outcome.state] using native.1
                                          obtain ⟨_next, _source, _roots, receipt, _post, _bounded, _mass⟩ :=
                                            SourceCurrentAllocatedTargetQuery.raw_done_caller_admitted_resources
                                              seed.2 nativeFuel formulas solver inventory caller queried left right value
                                              memos initial fits reserved.head leftResident rightResident
                                              leftClosed rightClosed nativeRead
                                          have skip :=
                                            SourceSynthesisCurrentRootEmptyCheckGate.source_retained_available_shared_empty_check_skipped
                                              lib query signed whole accepted rootValue sourceHeap built queried
                                              receipt.ready.good.native.machine.1.coherent nativeFacts.1.1 value
                                              receipt.available memos.query receipt.globals.query caller.fourth p h
                                          cases checkEmpty with
                                          | false =>
                                              simpa [observe, same, sourceRead, targetRead, leftRead, rightRead,
                                                nativeRead, SourcePruningEnumerationSharedDispatch.afterQuery,
                                                SourcePruningEnumerationSharedEnabledEmpty.Outcome.completed,
                                                SourcePruningEnumerationSharedEnabledEmpty.Outcome.state,
                                                SourceCurrentAllocatedPartialState.advance] using nativeFacts
                                          | true =>
                                              simpa [observe, same, sourceRead, targetRead, leftRead, rightRead,
                                                nativeRead, SourcePruningEnumerationSharedDispatch.afterQuery,
                                                skip.2.1, SourcePruningEnumerationSharedEnabledEmpty.Outcome.completed,
                                                SourcePruningEnumerationSharedEnabledEmpty.Outcome.state,
                                                SourceCurrentAllocatedPartialState.advance] using nativeFacts
                                      | yielded next queried =>
                                          simpa [observe, same, sourceRead, targetRead, leftRead, rightRead, nativeRead,
                                            SourceEqualityNativeDemand.Outcome.state,
                                            SourceCurrentAllocatedPartialState.advance] using native.1
                                      | failed failure queried =>
                                          simpa [observe, same, sourceRead, targetRead, leftRead, rightRead, nativeRead,
                                            SourceEqualityNativeDemand.Outcome.state,
                                            SourceCurrentAllocatedPartialState.advance] using native.1
                                      | constraintError message queried =>
                                          simpa [observe, same, sourceRead, targetRead, leftRead, rightRead, nativeRead,
                                            SourceEqualityNativeDemand.Outcome.state,
                                            SourceCurrentAllocatedPartialState.advance] using native.1
                                      | blocked reason next queried =>
                                          simpa [observe, same, sourceRead, targetRead, leftRead, rightRead, nativeRead,
                                            SourceEqualityNativeDemand.Outcome.state,
                                            SourceCurrentAllocatedPartialState.advance] using native.1
  · intro start saved left right actual member
    obtain ⟨startSame, savedSame, _ready, _fitted, _admitted,
        leftAvailable, rightAvailable, leftClosed, rightClosed, actualSame⟩ :=
      eventResources.2 start saved left right actual member
    subst start
    have native := SourcePruningEnumerationSharedIncomingQueryEvents.actual_query_source_seeds
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity caller.checked seed.2 initial.ready fits reserved.head sourceGrowth
      pastSeeds left right leftAvailable rightAvailable leftClosed rightClosed nativeFuel
    refine ⟨rfl, savedSame, actualSame, ?_, native.2⟩
    rw [actualSame]
    exact native.1

end MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents
