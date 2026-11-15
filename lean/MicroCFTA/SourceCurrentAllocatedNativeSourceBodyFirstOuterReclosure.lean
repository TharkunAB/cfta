import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody
import MicroCFTA.SourceCurrentAllocatedNativeRawMuCutoffReplay
import MicroCFTA.SourceCurrentAllocatedNativeCoherentOpenBodyResult
import MicroCFTA.SourceCurrentAllocatedNativePrefixInputs
import MicroCFTA.SourceCurrentNativeOpenRequestResults

/-!
# Reclosure of the actual source body-first Mu frame

The original source and full pattern select B/U at the original domain.
The actual current-cache entry requests B/B at the body-first key.
The genuine smaller child supplies its coherent product with cutoff e.
The same original plan supplies endpoint facts and availability.
The used outer binder e recloses the full original U at that endpoint.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstOuterReclosure
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceCurrentAllocatedNativeCoherentOpenBodyResult (ProductShape)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid

set_option autoImplicit false

private theorem optional_reclosed_trace
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (binder : Nat × Nat) (product expected : Value Symbol Guard)
    (before after : Checked width) (count : Nat) (result : Value Symbol Guard)
    (one : SourceEqualityNativeDemand.step (.code (.optionalBinder binder product .pure)) before =
      .yielded (.code (.pure expected)) before)
    (actual : Steps count (.code (.optionalBinder binder product .pure)) before (.code (.pure result)) after) :
    count = 1 ∧ result = expected ∧ after = before := by
  cases count with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      have same := Outcome.yielded.inj (chosen.symm.trans one)
      rw [same.1, same.2] at tail
      have terminal := pure_trace remaining expected result before after tail
      have remainingZero : remaining = 0 := terminal.1
      exact ⟨by omega, terminal.2.1.symm, terminal.2.2.symm⟩

/-- The actual body-first Mu body returns the full original U at its same child endpoint. -/
theorem current_stored_universe_body_first_outer_body_reclosure
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (original before after : Checked width) (physical : Physical original.native)
    (growth : Grows sourceHeap original.native.machine.heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available original.native.machine.heap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) (patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
    body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧ bodyEntry.identity ≠ entry.identity ∧
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
      body universeValue bodyEntry.identity entry.identity
    ∀ (actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
    actualDomain.key = sourceDomain.1.key →
    let request : NodeRequest Symbol Guard := ⟨actualDomain, body, universeValue⟩
    ∀ (parentFuel bodySteps : Nat) (result : Value Symbol Guard)
      (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
    InputsThrough parentFuel (.code (.node request .pure)) original →
    Steps 1 (.code (.node request .pure)) original
      (.code ((compileNode request).bind finishNext)) before →
    bodySteps < parentFuel →
    Steps bodySteps (.code (compileNode request)) before (.code (.pure result)) after →
    let allocated := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right bodyEntry.identity entry.identity
    let started : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := allocated.2}}
    (∀ used count, 0 < used → used + count ≤ parentFuel → count < parentFuel →
      ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (product : Value Symbol Guard) (middle : Checked width),
      Steps used (.code (.node request .pure)) original
        (.code ((requestNode allocated.1 body body).bind next)) started →
      allocated.1.key = bodyFirst.1.key →
      Steps count (.code (requestNode allocated.1 body body)) started (.code (.pure product)) middle →
      ProductShape entry.identity bodyEntry.identity entry.identity body product) →
    decision request.domain.key request.left request.right = .rightMu ∧
    allocated.1.key = bodyFirst.1.key ∧ result = universeValue ∧
    ∃ (childSteps : Nat) (product : Value Symbol Guard) (middle : Checked width),
      bodySteps = 1 + childSteps + 1 ∧ 2 + childSteps ≤ parentFuel ∧ childSteps < parentFuel ∧
      Steps 1 (.code (compileNode request)) before
        (.code ((requestNode allocated.1 body body).bind
          (fun value => .optionalBinder (pair bodyEntry.identity entry.identity) value .pure))) started ∧
      Steps 2 (.code (.node request .pure)) original
        (.code ((requestNode allocated.1 body body).bind
          (fun value => .optionalBinder (pair bodyEntry.identity entry.identity) value finishNext))) started ∧
      Steps childSteps (.code (requestNode allocated.1 body body)) started
        (.code (.pure product)) middle ∧
      ProductShape entry.identity bodyEntry.identity entry.identity body product ∧
      Physical middle.native ∧ Grows sourceHeap middle.native.machine.heap ∧
      Available middle.native.machine.heap product ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu (pair bodyEntry.identity entry.identity) product
        middle.native.machine.heap = .done universeValue middle.native.machine.heap ∧
      SourceEqualityNativeDemand.step
        (.code (.optionalBinder (pair bodyEntry.identity entry.identity) product .pure)) middle =
        .yielded (.code (.pure universeValue)) middle ∧
      Steps 1 (.code (.optionalBinder (pair bodyEntry.identity entry.identity) product .pure)) middle
        (.code (.pure universeValue)) after ∧ after = middle := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody.current_stored_universe_diagonal_first_actual_mu_body
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      original.native.machine.heap physical.machine.1 growth domains cacheValid pattern patternAvailable
      patternClosed patternId patternIdentity patternKind
  refine ⟨bodyEntry, bodyRows, bodyShape, bodyApart, ?_⟩
  dsimp only
  intro actualDomain sameKey parentFuel bodySteps result finishNext plan entered smaller actual children
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    universeValue referenceValue entry.identity entry.identity
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    body universeValue bodyEntry.identity entry.identity
  let request : NodeRequest Symbol Guard := ⟨actualDomain, body, universeValue⟩
  let allocated := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
    request.left request.right bodyEntry.identity entry.identity
  let started : Checked width :=
    {before with native := advance before.native {before.native.machine with domains := allocated.2}}
  let binder := pair bodyEntry.identity entry.identity
  let childCode := requestNode allocated.1 body body
  let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun value => .optionalBinder binder value .pure
  let lifted : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun value => (next value).bind finishNext
  dsimp only at sourceFacts
  obtain ⟨bodyIdentity, _universeIdentity, _bodyOpen, _cutoffApart, incomingFacts, _terminalFacts⟩ := sourceFacts
  have bodySelected : decision diagonalFirst.1.key body universeValue = .rightMu :=
    (incomingFacts diagonalFirst.1 rfl).1
  have sourceValid : Cache.Valid sourceDomain.2 :=
    (IntersectionEmptyDomain.make_correct domains cacheValid _).1
  have diagonalKey := SourceRecursiveIntersectionSchedule.entered_key sourceDomain.2 sourceValid sourceDomain.1.key
    universeValue referenceValue entry.identity entry.identity
  have tagOrder : compare (1 : Nat) 2 = .lt := by decide
  have bodyDiagonalFresh : pair bodyEntry.identity entry.identity ∉ diagonalFirst.1.key.seen := by
    intro member
    have repeated : decision diagonalFirst.1.key body universeValue =
        .repeated (pair bodyEntry.identity entry.identity) := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity,
        bodyShape, universeValue, Value.referenceOf, Value.free, member, tagOrder]
    rw [repeated] at bodySelected
    cases bodySelected
  have sourceFresh : pair bodyEntry.identity entry.identity ∉ sourceDomain.1.key.seen := by
    intro member
    apply bodyDiagonalFresh
    rw [diagonalKey]
    exact (extend_seen _ _ _ _).mpr (Or.inr member)
  have actualFresh : pair bodyEntry.identity entry.identity ∉ actualDomain.key.seen := by
    rw [sameKey]
    exact sourceFresh
  have selected : decision request.domain.key request.left request.right = .rightMu := by
    simp [request, decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      bodyShape, universeValue, Value.referenceOf, Value.free, actualFresh, tagOrder]
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    simp only [compileNode, selected]
  have reachedBefore := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
    parentFuel 1 (.code (.node request .pure)) (.code (compileNode request)) finishNext
    original before physical plan entered (by omega)
  have allocatedKey : allocated.1.key = bodyFirst.1.key := by
    have currentKey := SourceRecursiveIntersectionSchedule.entered_key before.native.machine.domains
      reachedBefore.2.1.machine.2 actualDomain.key body universeValue bodyEntry.identity entry.identity
    have historicalKey := SourceRecursiveIntersectionSchedule.entered_key sourceDomain.2 sourceValid
      sourceDomain.1.key body universeValue bodyEntry.identity entry.identity
    have extendedSame := congrArg (fun currentDomain => extend currentDomain
      ((SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst)
      (pair bodyEntry.identity entry.identity)) sameKey
    exact currentKey.trans (extendedSame.trans historicalKey.symm)
  have one : SourceEqualityNativeDemand.step (.code (compileNode request)) before =
      .yielded (.code (childCode.bind next)) started := by
    rw [compiled]
    have receipt := SourceCurrentAllocatedNativeMuSource.enter_prefix request before
      bodyEntry.identity entry.identity bodyIdentity rfl
    simpa only [childCode, requestNode, Code.bind, next, binder, started, allocated,
      request, universeValue, bodyShape, SourceRecursiveIntersectionKernel.body] using receipt
  have origin : Steps 1 (.code (compileNode request)) before (.code (childCode.bind next)) started :=
    .cons _ _ _ _ _ _ _ one (.refl _ _)
  have appended := origin.bind _ _ _ _ _ finishNext
  have composed := entered.trans _ _ _ _ _ _ _ _ appended
  have outer : Steps 2 (.code (.node request .pure)) original (.code (childCode.bind lifted)) started := by
    simpa only [Control.bind, Code.bind_assoc, Code.bind, lifted] using composed
  cases bodySteps with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans one)
      obtain ⟨childSteps, optionalSteps, product, middle, splitCount, childTrace, optionalTrace⟩ :=
        steps_bind_inverse remaining (.code childCode) next started after result tail
      have shape : ProductShape entry.identity bodyEntry.identity entry.identity body product :=
        children 2 childSteps (by omega) (by omega) (by omega) lifted product middle outer allocatedKey childTrace
      have atChild := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
        parentFuel 2 (.code (.node request .pure)) (.code childCode) lifted
        original started physical plan outer (by omega)
      have atEnd := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
        (parentFuel - 2) childSteps (.code childCode) (.code (.pure product)) .pure
        started middle atChild.2.1 atChild.2.2.2.2 childTrace (by omega)
      have middleGrowth : Grows sourceHeap middle.native.machine.heap :=
        InternedConstructorTemplates.grows_trans growth
          (InternedConstructorTemplates.grows_trans atChild.2.2.1.heap atEnd.2.2.1.heap)
      have available : Available middle.native.machine.heap product :=
        SourceCurrentNativeOpenRequestResults.node_result childSteps
          ⟨allocated.1, body, body⟩ started middle product atChild.2.1 atEnd.1
      obtain ⟨reclosed, optionalOne, _optionalDone⟩ :=
        SourceCurrentAllocatedNativeCoherentOpenBodyResult.stored_open_product_optional_reclosure
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          middle atEnd.2.1.machine.1 middleGrowth bodyEntry.identity entry.identity product available shape
      obtain ⟨optionalCount, resultEq, endpoint⟩ :=
        optional_reclosed_trace binder product universeValue middle after optionalSteps result optionalOne optionalTrace
      refine ⟨selected, allocatedKey, resultEq, childSteps, product, middle,
        by omega, by omega, by omega, origin, outer, childTrace, shape, atEnd.2.1, middleGrowth,
        available, reclosed, optionalOne, ?_, endpoint⟩
      simpa only [optionalCount, resultEq] using optionalTrace

end MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstOuterReclosure
