import MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback
import MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryResult
import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourceEqualityNativeDemandPrefixSplit

/-!
# Open source-row readback at the actual native edge query

The actual checked query supplies its own key check and body trace.
Dispatch retains the original operation state and source field origin.
An evaluated body retains its real finish continuation in each child prefix.
A ready hit uses the prior returned law at the exact original request.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowQuery
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeContextCache (Returned)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (repeatedValue)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

set_option autoImplicit false

/-- The actual edge query retains the exact open substitution children and source key. -/
theorem open_row_query_readback_of_children
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (sourceName cutoffLeft cutoffRight : Nat)
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (fuel traceFuel : Nat) (result : EdgeValue Symbol Guard)
    (physical : Physical before.native)
    (self : request.right = request.left) (sourceTop : request.left.entry.key.constraint = top)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (fieldOrigin : SourceEqualityOriginalFieldOrigins.Origin before.operations.constraints
      request.left.entry.key.constraint)
    (returned : Returned (fun old row => old = request →
      row.children = request.left.children.map
        (input (replacement (.interned sourceName)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
      row.entry.key = ⟨request.left.entry.key.symbol,
        (request.left.children.map (input (replacement (.interned sourceName)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf, top⟩)
      before.native.edges)
    (done : execute fuel (.code (requestEdge request.domain request.left request.right)) before = .done result after)
    (actual : Trace traceFuel (.code (requestEdge request.domain request.left request.right)) before
      (.code (.pure result)) after)
    (childrenReplay : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : Checked width) (value : Value Symbol Guard),
      Steps stepsBefore (.code (requestEdge request.domain request.left request.right)) before
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      execute childFuel (.code (requestNode request.domain pair.1 pair.2)) first = .done value last →
      value = input (replacement (.interned sourceName)
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))) pair.1) :
    result.children = request.left.children.map
      (input (replacement (.interned sourceName)
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
    result.entry.key = ⟨request.left.entry.key.symbol,
      (request.left.children.map (input (replacement (.interned sourceName)
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf, top⟩ := by
  let law : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop := fun old row => old = request →
    row.children = request.left.children.map
      (input (replacement (.interned sourceName)
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
    row.entry.key = ⟨request.left.entry.key.symbol,
      (request.left.children.map (input (replacement (.interned sourceName)
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf, top⟩
  have checkedInputs := SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs actual
  change EdgeReady before.native.machine request ∧
    SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right at checkedInputs
  have queryLaw := SourceCurrentAllocatedNativeEdgeQueryResult.edge_query_result_of_body_induction
    law request before after fuel result physical checkedInputs.1 checkedInputs.2 returned done
    (by
      intro bodySteps bodyBound next first middle value origin bodyRaw
      intro _
      obtain ⟨tailFuel, _traceCount, dispatchPhysical, tailPhysical⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix origin actual
      have bodyBoundPhysical : Trace tailFuel
          ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind next)
          first (.code (.pure result)) after := by
        simpa only [Control.bind, Code.bind] using tailPhysical
      obtain ⟨actualBodySteps, _outer, actualValue, actualMiddle, _bodyCount, bodyPhysical, _finishPhysical⟩ :=
        SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse tailFuel
          (.edgeBody request .pure) next first after result bodyBoundPhysical
      have countSame : actualBodySteps = bodySteps :=
        Nat.le_antisymm (bodyRaw.length_le_complete bodyPhysical.steps)
          (bodyPhysical.steps.length_le_complete bodyRaw)
      subst actualBodySteps
      have rawDone := trace_done bodySteps (.edgeBody request .pure) first middle value bodyRaw
      have physicalDone := trace_done bodySteps (.edgeBody request .pure)
        first actualMiddle actualValue bodyPhysical.steps
      have sameBody := Outcome.done.inj (rawDone.symm.trans physicalDone)
      have matchingBody : Trace bodySteps (.edgeBody request .pure) first (.code (.pure value)) middle := by
        rw [sameBody.1, sameBody.2]
        exact bodyPhysical
      have firstPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension dispatchPhysical physical
      have dispatchOne : step (.code (requestEdge request.domain request.left request.right)) before =
          .yielded (.edgeBody request next) first := by
        obtain ⟨control, current, one, tail⟩ := steps_succ 0 _ _ _ _ origin
        obtain ⟨rfl, rfl⟩ := steps_zero _ _ _ _ tail
        exact one
      have operationsSame : first.operations = before.operations := by
        simpa only [dispatchOne, Outcome.state] using
          SourceEqualityNativeDemandOperations.step_code_operations
            (requestEdge request.domain request.left request.right) before
      have firstValid : SourceEqualityConstraintMemoAllocation.Valid first.operations := by
        rw [operationsSame]
        exact valid
      have firstOrigin : SourceEqualityOriginalFieldOrigins.Origin first.operations.constraints
          request.left.entry.key.constraint := by
        rw [operationsSame]
        exact fieldOrigin
      have replayAtBody : ∀ stepsBefore childFuel, 0 < stepsBefore →
          stepsBefore + childFuel ≤ bodySteps + 1 → childFuel < bodySteps + 1 →
          ∀ pair ∈ request.left.children.zip request.right.children,
          ∀ (childNext : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
            (childBefore childAfter : Checked width) (childValue : Value Symbol Guard),
          Steps stepsBefore (.edgeBody request .pure) first
            (.code ((requestNode request.domain pair.1 pair.2).bind childNext)) childBefore →
          execute childFuel (.code (requestNode request.domain pair.1 pair.2)) childBefore =
            .done childValue childAfter →
          childValue = input (replacement (.interned sourceName)
            (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))) pair.1 := by
        intro stepsBefore childFuel positive room smaller pair member childNext childBefore childAfter childValue
          childPrefix childDone
        have appended := childPrefix.bind _ _ _ _ _ next
        have actualChildPrefix : Steps (1 + stepsBefore)
            (.code (requestEdge request.domain request.left request.right)) before
            (.code ((requestNode request.domain pair.1 pair.2).bind
              (fun value => (childNext value).bind next))) childBefore := by
          simpa only [Control.bind, Code.bind, Code.bind_assoc] using
            origin.trans _ _ _ _ _ _ _ _ appended
        exact childrenReplay (1 + stepsBefore) childFuel (by omega) (by omega) (by omega)
          pair member (fun value => (childNext value).bind next) childBefore childAfter childValue
          actualChildPrefix childDone
      obtain ⟨_loaded, _combined, values, _workMiddle, _workCount, _load, _allocation, _combinedTop,
          _walkBound, _walked, ordered, _workPhysical, _workExtension, _valuesAvailable,
          _throughWork, resultChildren, resultKey, _resultEq, _afterEq⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.open_row_physical_readback_of_children
          sourceName cutoffLeft cutoffRight request first middle (bodySteps + 1) bodySteps value
          firstPhysical.1 self sourceTop firstValid firstOrigin rawDone matchingBody replayAtBody
      exact ⟨resultChildren.trans ordered, by simpa only [ordered] using resultKey⟩)
  exact queryLaw rfl

end MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowQuery

#check MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowQuery.open_row_query_readback_of_children
#print axioms MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowQuery.open_row_query_readback_of_children
