import MicroCFTA.SourceCurrentAllocatedNativeOpenBodyProduct
import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations

/-!
# Raw open source-body products under the original node query

The original node dispatch retains its actual finish continuation.
Each edge hypothesis uses its original raw count and outer prefix.
Local completion observations do not change an induction budget.
The result retains the constructor endpoint and original-U reclosure.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRawOpenBodyProductReplay
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

/-- Smaller actual edge traces derive the open body product under the original node dispatch. -/
theorem open_body_product_trace_result
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
      (pair.1 = pair.2 →
        childValue.children = pair.1.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
        childValue.entry.key = ⟨pair.1.entry.key.symbol,
          (pair.1.children.map (input (replacement (.interned entry.identity)
            (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf,
          top⟩) ∧
      (pair.1.children.length ≠ pair.2.children.length → childValue.children = [.empty])) :
    ∃ (productEntry : Interned NodeKey) (products rawRows : List (EdgeValue Symbol Guard))
      (middle : Checked width) (count : Nat),
      count + 1 ≤ bodySteps ∧
      All₂ (fun (source : EdgeValue Symbol Guard) target =>
        target.children = source.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
        target.entry.key = ⟨source.entry.key.symbol,
          (source.children.map (input (replacement (.interned entry.identity)
            (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf,
          top⟩) (nodeEdges body) products ∧
      (∀ row ∈ products, row ∈ rawRows) ∧
      Physical middle.native ∧ Extension before.native.machine middle.native.machine ∧
      (∀ row ∈ products, EdgeResident middle.native.machine.heap row) ∧
      Trace count (.code (compileRows domain (nodeEdges body) (nodeEdges body))) before
        (.code (.work (makeNode rawRows) .pure)) middle ∧
      result = (run (makeNode rawRows) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeNode rawRows) middle.native.machine.heap).2}} ∧
      canonicalEdges (surviving rawRows) = canonicalEdges products ∧
      result = .node productEntry (canonicalEdges products) 0
        [.intersection (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight).1
          (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight).2] ∧
      Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      Extension original.native.machine after.native.machine ∧
      Grows sourceHeap after.native.machine.heap ∧
      Available after.native.machine.heap result ∧
      (∀ row ∈ products, EdgeResident after.native.machine.heap row) ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)
        result after.native.machine.heap = .done (.mu entry body depth ordinary) after.native.machine.heap ∧
      SourceEqualityNativeDemand.step
        (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight) result .pure)) after =
        .yielded (.code (.pure (.mu entry body depth ordinary))) after ∧
      SourceEqualityNativeDemand.execute 2
        (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight) result .pure)) after =
        .done (.mu entry body depth ordinary) after := by
  have dispatched := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel 1 (.code (.node ⟨domain, body, body⟩ .pure))
    (.code (compileNode ⟨domain, body, body⟩)) finishNext original before sourceHeap
    physical plan fields operationsValid sourceGrowth entered (by omega)
  obtain ⟨_checkedEntry, firstPhysical, firstExtension, firstGrowth, _firstOperationsValid,
    _firstOperationsGrowth, _boundPlan, rawPlan, _boundFields, _rawFields⟩ := dispatched
  have checkedBody := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
    (parentFuel - 1) bodySteps (.code (compileNode ⟨domain, body, body⟩))
    (.code (.pure result)) .pure before after firstPhysical rawPlan actual (by omega)
  have bodyTrace : Trace bodySteps (.code (compileNode ⟨domain, body, body⟩)) before
      (.code (.pure result)) after := checkedBody.1
  have rowsTrace : Trace bodySteps (.code (compileRows domain (nodeEdges body) (nodeEdges body))) before
      (.code (.pure result)) after := by
    rw [← compiled]
    exact bodyTrace
  have rowsDone : execute (bodySteps + 1)
      (.code (compileRows domain (nodeEdges body) (nodeEdges body))) before = .done result after :=
    trace_done bodySteps _ before after result rowsTrace.steps
  have product := SourceCurrentAllocatedNativeOpenBodyProduct.current_open_body_product_of_smaller_queries
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    cutoffLeft cutoffRight domain before after (bodySteps + 1) bodySteps result
    firstPhysical firstGrowth rowsDone rowsTrace (by
      intro stepsBefore childFuel room _childSmaller pair member next first last row origin _physical childDone
      obtain ⟨rawCount, rawSmaller, rawTrace⟩ := done_trace childFuel _ first last row childDone
      let lifted : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
        fun value => (next value).bind finishNext
      have bodyPrefix : Steps stepsBefore (.code (compileNode ⟨domain, body, body⟩)) before
          (.code ((requestEdge domain pair.1 pair.2).bind next)) first := by
        rw [compiled]
        exact origin
      have appended := bodyPrefix.bind _ _ _ _ _ finishNext
      have outer : Steps (1 + stepsBefore) (.code (.node ⟨domain, body, body⟩ .pure)) original
          (.code ((requestEdge domain pair.1 pair.2).bind lifted)) first := by
        simpa only [Control.bind, Code.bind_assoc, lifted] using
          entered.trans _ _ _ _ _ _ _ _ appended
      exact edges pair member lifted first last (1 + stepsBefore) rawCount row
        (by omega) (by omega) outer rawTrace)
  obtain ⟨productEntry, products, rawRows, middle, count, bounded, aligned, retained,
    middlePhysical, middleExtension, middleResident, throughWork, resultEq, afterEq, canonical,
    nodeRead, afterPhysical, afterExtension, available, afterResident, reclosed, optionalStep,
    optionalDone⟩ := product
  have originalExtension := firstExtension.trans afterExtension
  exact ⟨productEntry, products, rawRows, middle, count, by omega, aligned, retained,
    middlePhysical, middleExtension, middleResident, throughWork, resultEq, afterEq, canonical,
    nodeRead, afterPhysical, afterExtension, originalExtension,
    grows_trans sourceGrowth originalExtension.heap, available, afterResident, reclosed,
    optionalStep, optionalDone⟩

end MicroCFTA.SourceCurrentAllocatedNativeRawOpenBodyProductReplay
