import MicroCFTA.SourceCurrentAllocatedNativeOpenBodyProduct
import MicroCFTA.SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeCoherentOpenBodyResult
import MicroCFTA.InternedStoredSubstitutionScope

/-!
# Coherent open source products from actual nonterminal row traces

The original source classifies each child of each actual row.
The stronger edge law fixes its ordered products at the actual domain.
The original raw replay retains the parent count and endpoint.
Actual resident products supply finite identity functionality.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeBodyFirstCoherentProductReplay
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open IntersectionFlatMemoKeyDomain (DomainKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (repeatedValue)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable {width : Nat}

set_option autoImplicit false

/-- Actual nonterminal row query traces derive a coherent open source product at the same endpoint. -/
theorem open_body_product_of_reference_row_traces
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (cutoffLeft cutoffRight : Nat) (domain : Interned DomainKey)
    (original before after : Checked width) (parentFuel bodySteps : Nat) (result : Value Symbol Guard)
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (compiled : compileNode ⟨domain, body, body⟩ =
      compileRows domain (nodeEdges body) (nodeEdges body))
    (physical : Physical original.native) (sourceGrowth : Grows sourceHeap original.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid original.operations)
    (plan : InputsThrough parentFuel (.code (.node ⟨domain, body, body⟩ .pure)) original)
    (fields : FieldsThrough parentFuel (.code (.node ⟨domain, body, body⟩ .pure)) original)
    (entered : Steps 1 (.code (.node ⟨domain, body, body⟩ .pure)) original
      (.code ((compileNode ⟨domain, body, body⟩).bind finishNext)) before)
    (smaller : bodySteps < parentFuel)
    (actual : Steps bodySteps (.code (compileNode ⟨domain, body, body⟩)) before (.code (.pure result)) after)
    (edges : ∀ pair ∈ pairs (nodeEdges body) (nodeEdges body),
      ∀ (childNext : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (childBefore childAfter : Checked width) (used count : Nat) (childValue : EdgeValue Symbol Guard),
      0 < used → used + count ≤ parentFuel →
      Steps used (.code (.node ⟨domain, body, body⟩ .pure)) original
        (.code ((requestEdge domain pair.1 pair.2).bind childNext)) childBefore →
      Steps count (.code (requestEdge domain pair.1 pair.2)) childBefore
        (.code (.pure childValue)) childAfter →
      SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.EdgeResult
        ⟨domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
        ⟨domain, .reference (.interned entry.identity), .reference (.interned entry.identity)⟩
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))
        ⟨domain, pair.1, pair.2⟩ childValue) :
    SourceCurrentAllocatedNativeCoherentOpenBodyResult.ProductShape
      entry.identity cutoffLeft cutoffRight body result ∧
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
    Extension original.native.machine after.native.machine ∧
    Grows sourceHeap after.native.machine.heap ∧ Available after.native.machine.heap result ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)
      result after.native.machine.heap = .done (.mu entry body depth ordinary) after.native.machine.heap ∧
    SourceEqualityNativeDemand.step
      (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight) result .pure)) after =
      .yielded (.code (.pure (.mu entry body depth ordinary))) after ∧
    SourceEqualityNativeDemand.execute 2
      (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight) result .pure)) after =
      .done (.mu entry body depth ordinary) after := by
  let cutoff : Value Symbol Guard :=
    repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)
  let muTarget : NodeRequest Symbol Guard :=
    ⟨domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
  let referenceTarget : NodeRequest Symbol Guard :=
    ⟨domain, .reference (.interned entry.identity), .reference (.interned entry.identity)⟩
  let environment : InternedStoredSubstitution.Environment Symbol Guard :=
    replacement (.interned entry.identity) cutoff
  obtain ⟨_bodyEntry, _marker, arrow, rows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      childKinds, _arrowPresent⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      original.native.machine.heap physical.machine.1 sourceGrowth
  have sourceRows : nodeEdges body = canonicalEdges (arrow :: rows) := by
    rw [bodyShape]
    rfl
  have sourceTop (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges body) :
      row.entry.key.constraint = top :=
    (childKinds row (by rw [← sourceRows]; exact member)).2.1
  have referenceInput : input environment (.reference (.interned entry.identity)) = cutoff := by
    simp [environment, input, replacement]
  have knownMany (values : List (Value Symbol Guard)) :
      (∀ child ∈ values,
        SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.KnownResult
          muTarget referenceTarget cutoff ⟨domain, child, child⟩ (input environment child)) →
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.KnownResult
          muTarget referenceTarget cutoff ⟨domain, children.1, children.2⟩ value)
        (values.zip values) (values.map (input environment)) := by
    induction values with
    | nil => intro _each; exact .nil
    | cons child tail ih =>
        intro each
        exact .cons (each child List.mem_cons_self)
          (ih (fun value member => each value (List.mem_cons_of_mem child member)))
  have rowInputs (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges body) :
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.KnownResult
          muTarget referenceTarget cutoff ⟨domain, children.1, children.2⟩ value)
        (row.children.zip row.children) (row.children.map (input environment)) := by
    apply knownMany row.children
    intro child childMember
    have kinds := childKinds row (by rw [← sourceRows]; exact member)
    rcases kinds.2.2 child childMember with referenceCase | closedCase
    · subst child
      exact Or.inr ⟨Or.inr rfl, referenceInput⟩
    · exact Or.inl (Or.inl ⟨rfl, closedCase.2.2.1,
        InternedStoredSubstitutionScope.input_closed child environment closedCase.2.2.1⟩)
  have observed := SourceCurrentAllocatedNativeRawOpenBodyProductReplay.open_body_product_trace_result
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    cutoffLeft cutoffRight domain original before after parentFuel bodySteps result finishNext
    compiled physical sourceGrowth operationsValid plan fields entered smaller actual (by
      intro pair member childNext childBefore childAfter used count childValue
        positive bounded origin childTrace
      have property := edges pair member childNext childBefore childAfter used count childValue
        positive bounded origin childTrace
      change SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.EdgeResult
        muTarget referenceTarget cutoff ⟨domain, pair.1, pair.2⟩ childValue at property
      refine ⟨?_, property.1⟩
      intro self
      have sourceMember := (SourceRecursiveIntersectionKernel.pairs_member
        (nodeEdges body) (nodeEdges body) pair).mp member
      have selectedInputs :
          All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
            SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.KnownResult
              muTarget referenceTarget cutoff ⟨domain, children.1, children.2⟩ value)
            (pair.1.children.zip pair.2.children)
            (pair.1.children.map (input environment)) := by
        rw [← self]
        exact rowInputs pair.1 sourceMember.1
      exact property.2 self.symm (sourceTop pair.1 sourceMember.1) _ selectedInputs)
  obtain ⟨productEntry, products, _rawRows, _workMiddle, _count, _bounded, aligned, _retained,
      _middlePhysical, _middleExtension, _middleResident, _throughWork, _resultEq, _afterEq,
      _canonical, nodeRead, afterPhysical, afterExtension, originalExtension, afterGrowth,
      available, afterResident, reclosed, optionalStep, optionalDone⟩ := observed
  have functional := SourceCurrentAllocatedNativeCoherentOpenBodyResult.identity_functional_of_resident
    after.native.machine.heap afterPhysical.machine.1 products afterResident
  exact ⟨⟨productEntry, products, aligned, functional, nodeRead⟩, afterPhysical, afterExtension,
    originalExtension, afterGrowth, available, reclosed, optionalStep, optionalDone⟩

end MicroCFTA.SourceCurrentAllocatedNativeBodyFirstCoherentProductReplay
