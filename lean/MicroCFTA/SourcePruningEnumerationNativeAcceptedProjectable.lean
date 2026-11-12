import MicroCFTA.SourcePruningEnumerationNativeCheckedProjectable

/-!
# Projection for actual accepted native edge results

The checked gate and ordered child walk determine the returned edge.
Its complete accepted receipt retains a successful own projection.
A completed physical receipt also supplies projection for its actual result.
These results do not establish checked history for every retained row.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeAcceptedProjectable
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open EnumerationState EnumerationCorrectness
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "readback" => SourceEqualityConjoinAllocation.readback
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

/-- The complete accepted result retains projection for the same constructed edge. -/
theorem accepted_body_projectable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state after : SourceEqualityNativeDemand.State width)
    (first second combined : Allocated) (values : List (Value Symbol Guard)) (fuel : Nat)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (inputs : EdgeReady state.native.machine request)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    (walk : SourceEqualityNativeDemandChildWalk.Walk (SourceEqualityPCSGuard.holds formulas solver) request.domain
      (request.left.children.zip request.right.children)
      {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length state.operations).2} values after fuel) :
    let built := run (makeEdge request.left.entry.key.symbol (readback combined) values) after.native.machine.heap
    let final : SourceEqualityNativeDemand.State width :=
      {after with native := advance after.native {after.native.machine with heap := built.2}}
    (execute (fuel + 3) (.edgeBody request .pure) state = .done built.1 final ∧
      EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) final.native.machine request built.1 ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap final.native.machine.heap ∧
      EdgeResident final.native.machine.heap built.1 ∧
      built.1.children = values ∧ built.1.children.length = request.left.children.length ∧
      SourcePruningEnumerationArityOrigins.Fits built.1.entry.key.constraint built.1.children.length) ∧
    ∃ classes : EqualityNormalize.Constraints,
      SourceCompactGuards.sourceEqualities built.1.entry.key.constraint = some classes ∧
      SourcePruningEnumerationConstraint.project built.1.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive built.1.entry.key.constraint.guard).isSome
            then none else some built.1.entry.key.constraint) ∧
      (∀ trie ∈ EnumerationEquality.readClasses classes, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows built.1.children.length
        (suspendedVars start (EnumerationEquality.readClasses classes)) = true := by
  let built := run (makeEdge request.left.entry.key.symbol (readback combined) values) after.native.machine.heap
  have original := SourcePruningEnumerationNativeCheckedOriginArity.accepted_body_produced
    formulas solver request state after first second combined values fuel valid heapReady inputs
      leftCached rightCached arity symbols left right accepted walk
  have childEffects := walk.effects heapReady
  have fields := MergedPhysicalGroupEdges.makeEdge_fields after.native.machine.heap
    childEffects.1.ready.semantic.1.normal.facts request.left.entry.key.symbol
    (readback combined) values childEffects.2.2.1
  obtain ⟨firstReady, _firstFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _
    valid.constraints leftCached first left
  obtain ⟨secondReady, _secondFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _
    valid.constraints rightCached second right
  obtain ⟨_accepted, classes, source, projection, validTries, _fits⟩ :=
    SourcePruningEnumerationNativeCheckedProjectable.ready_projectable GuardStructuralOrder.le
      first second combined request.left.children.length request.right.children.length
      state.operations valid firstReady secondReady accepted
  have guardSame : built.1.entry.key.constraint = readback combined := fields.2.1
  have outputSource : SourceCompactGuards.sourceEqualities built.1.entry.key.constraint = some classes := by
    rw [guardSame]
    exact source
  have outputProjection : SourcePruningEnumerationConstraint.project built.1.entry.key.constraint =
      some (EnumerationEquality.readClasses classes,
        if (SourceCompactGuards.positive built.1.entry.key.constraint.guard).isSome
          then none else some built.1.entry.key.constraint) := by
    rw [guardSame]
    exact projection
  exact ⟨original, classes, outputSource, outputProjection, validTries,
    original.2.2.2.2.2.2 _ _ outputProjection⟩

/-- Final record coherence identifies the guard of the actual constructor return. -/
private theorem constructed_guard [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (constraint : Guard) (values : List (Value Symbol Guard))
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent (run (makeEdge symbol constraint values) heap).2) :
    (run (makeEdge symbol constraint values) heap).1.entry.key.constraint = constraint := by
  let key : EdgeKey Symbol Guard := ⟨symbol, values.map Value.referenceOf, constraint⟩
  let candidate := EdgeValue.mk (Cache.intern heap.edges key).1 values
  obtain ⟨stored, present⟩ := Cache.keepFirst_present heap.edgeRecords key candidate
  have recorded : (run (makeEdge symbol constraint values) heap).2.edgeRecords key =
      some (run (makeEdge symbol constraint values) heap).1 := by
    simp only [makeEdge, run, edgeStep, key, candidate, present, Option.getD_some]
  exact congrArg EdgeKey.constraint (coherent.edges key _ recorded).2.1

/-- An actual physical receipt retains its child history and projects its returned edge. -/
theorem accepted_receipt_projectable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (first second combined : Allocated)
    (initial : SourceCurrentAllocatedNativePhysicalCompletion.Good state)
    (inputs : EdgeReady state.native.machine request)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    {count : Nat} {result : EdgeValue Symbol Guard} {after : SourceEqualityNativeDemand.State width}
    {post : Machine Symbol Guard → EdgeValue Symbol Guard → Prop}
    (receipt : SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt count
      (.edgeBody request .pure) state result after post) :
    (∃ values middle childCount, childCount + 1 < count + 1 ∧
      SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)
        {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length state.operations).2} values middle childCount ∧
      result = (run (makeEdge request.left.entry.key.symbol (readback combined) values)
        middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeEdge request.left.entry.key.symbol (readback combined) values)
          middle.native.machine.heap).2}} ∧
      result.children.length = request.left.children.length ∧
      SourcePruningEnumerationArityOrigins.Fits result.entry.key.constraint result.children.length) ∧
    ∃ classes : EqualityNormalize.Constraints,
      SourceCompactGuards.sourceEqualities result.entry.key.constraint = some classes ∧
      SourcePruningEnumerationConstraint.project result.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive result.entry.key.constraint.guard).isSome
            then none else some result.entry.key.constraint) ∧
      (∀ trie ∈ EnumerationEquality.readClasses classes, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows result.children.length
        (suspendedVars start (EnumerationEquality.readClasses classes)) = true := by
  have original := SourcePruningEnumerationNativeCheckedOriginArity.accepted_receipt_fits
    request state first second combined initial inputs left right accepted receipt
  have retained := original
  obtain ⟨values, middle, childCount, _bounded, _walk, resultSame, afterSame, _lengthSame, ownFits⟩ := retained
  have coherent : InternedRecordCoherence.Coherent
      (run (makeEdge request.left.entry.key.symbol (readback combined) values)
        middle.native.machine.heap).2 := by
    simpa only [afterSame, advance] using receipt.good.heap.semantic.1.normal.facts.coherent
  have guardSame : result.entry.key.constraint = readback combined := by
    rw [resultSame]
    exact constructed_guard request.left.entry.key.symbol (readback combined) values
      middle.native.machine.heap coherent
  obtain ⟨firstReady, _firstFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _
    initial.operations.constraints (initial.fields _ _ inputs.2.1).1 first left
  obtain ⟨secondReady, _secondFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _
    initial.operations.constraints (initial.fields _ _ inputs.2.2).1 second right
  obtain ⟨_accepted, classes, source, projection, validTries, _fits⟩ :=
    SourcePruningEnumerationNativeCheckedProjectable.ready_projectable GuardStructuralOrder.le
      first second combined request.left.children.length request.right.children.length
      state.operations initial.operations firstReady secondReady accepted
  have outputSource : SourceCompactGuards.sourceEqualities result.entry.key.constraint = some classes := by
    rw [guardSame]
    exact source
  have outputProjection : SourcePruningEnumerationConstraint.project result.entry.key.constraint =
      some (EnumerationEquality.readClasses classes,
        if (SourceCompactGuards.positive result.entry.key.constraint.guard).isSome
          then none else some result.entry.key.constraint) := by
    rw [guardSame]
    exact projection
  exact ⟨original, classes, outputSource, outputProjection, validTries, ownFits _ _ outputProjection⟩

end MicroCFTA.SourcePruningEnumerationNativeAcceptedProjectable
