import MicroCFTA.SourcePruningEnumerationNativeQueryPrefixArity
import MicroCFTA.SourcePruningEnumerationNativeCheckedProjectable
import MicroCFTA.SourceCurrentNativeGuardCode
import MicroCFTA.SourceEqualityAnnotationStoredSyntax

/-!
# Projectable guards through generated native query prefixes

The current physical heap supplies support for its existing edge records.
Actual generated requests preserve that support at every yielded prefix.
Checked bodies use the ready guard or the Top sentinel.
Node compilation emits safe local work and copies stored binder guards.
The result does not apply to arbitrary unchecked Code work.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeGeneratedProjectable
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
open SourceCurrentNativeTracePrefixBind (bind_prefix_cases)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun guard : Guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes)
local notation "GuardFields" => SourceCurrentNativeGuardCode.Fields
  (fun guard : Guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {A B : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem pure_prefix_heap (first : A) (before after : Checked width)
    (remaining : Control A) (fuel : Nat)
    (trace : Trace fuel (.code (.pure first)) before remaining after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail => cases one

private theorem finish_node_prefix_heap (handle : Nat) (first : Value Symbol Guard)
    (before after : Checked width) (remaining : Control (Value Symbol Guard)) (fuel : Nat)
    (trace : Trace fuel (.code (.finishNode handle first (.pure first))) before remaining after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail =>
      cases one
      exact pure_prefix_heap first _ after remaining count tail heap

private theorem finish_edge_prefix_heap (handle : Nat) (first : EdgeValue Symbol Guard)
    (before after : Checked width) (remaining : Control (EdgeValue Symbol Guard)) (fuel : Nat)
    (trace : Trace fuel (.code (.finishEdge handle first (.pure first))) before remaining after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail =>
      cases one
      exact pure_prefix_heap first _ after remaining count tail heap


private theorem walk_heap (limit : Nat) (call : A → Code Symbol Constraint B)
    (calls : ∀ (input : A) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (value : B), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (call input)) before (.code (.pure value)) after →
        Heap after.native.machine.heap)
    (fields : ∀ (input : A) (state : Checked width), Fields (.code (call input)) state)
    (inputs : List A) (values : List B) (before after : Checked width) (fuel : Nat)
    (bounded : fuel ≤ limit) (initial : Good before) (heap : Heap before.native.machine.heap)
    (actual : Walk call inputs before values after fuel) : Heap after.native.machine.heap := by
  revert bounded initial heap
  induction actual with
  | nil state => intro _ _ heap; exact heap
  | cons first rest before middle after value values firstFuel restFuel called tail ih =>
      intro bounded initial heap
      have firstHeap := calls first firstFuel (by omega) before middle value initial heap called
      have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects called initial (fields first before)
      exact ih (by omega) reached.1 firstHeap


private theorem walk_prefix_heap (limit : Nat) (call : A → Code Symbol Constraint B)
    (completed : ∀ (input : A) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (value : B), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (call input)) before (.code (.pure value)) after → Heap after.native.machine.heap)
    (prefixes : ∀ (input : A) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control B), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (call input)) before remaining after → Heap after.native.machine.heap)
    (fields : ∀ (input : A) (state : Checked width), Fields (.code (call input)) state)
    (inputs : List A) (fuel : Nat) (before after : Checked width) (remaining : Control (List B))
    (bounded : fuel ≤ limit) (initial : Good before) (heap : Heap before.native.machine.heap)
    (actual : Trace fuel (.code (walk call inputs)) before remaining after) : Heap after.native.machine.heap := by
  have bound : Trace fuel ((.code (walk call inputs) : Control (List B)).bind .pure)
      before remaining after := by
    simpa only [Control.bind, code_bind_pure] using actual
  rcases SourceCurrentNativeWalkPrefix.walk_prefix_cases call inputs .pure fuel before after remaining bound with
    ⟨index, input, values, entry, earlierFuel, currentFuel, inner,
      _selected, earlier, total, current, _nonpure, _same⟩ |
    ⟨walkFuel, outerFuel, values, middle, total, earlier, later⟩
  · have entryHeap := walk_heap limit call completed fields
      (inputs.take index) values before entry earlierFuel (by omega) initial heap earlier
    have entryFields : Fields (.code (walk call (inputs.take index))) before :=
      SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations call (inputs.take index)
        (fun input _ => fields input before)
    have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects earlier.trace initial entryFields
    exact prefixes input currentFuel (by omega) entry after inner reached.1 entryHeap current
  · have middleHeap := walk_heap limit call completed fields
      inputs values before middle walkFuel (by omega) initial heap earlier
    exact pure_prefix_heap values middle after remaining outerFuel later middleHeap


private theorem step_optionalBinder_heap (key : Nat × Nat) (body : Value Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (state : Checked width)
    (facts : InternedNestedFacts.Facts state.native.machine.heap)
    (heap : Heap state.native.machine.heap) (available : Available state.native.machine.heap body) :
    Heap (step (.code (.optionalBinder key body next)) state).state.native.machine.heap := by
  have retained := SourceEqualityAnnotationStoredSyntax.optionalBinder _ key body
    state.native.machine.heap heap facts available
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.native.machine.heap with
  | done value after =>
      simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state,
        advance, InternedNestedConstruction.Outcome.state] using retained
  | pending pending after =>
      simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state,
        advance, InternedNestedConstruction.Outcome.state] using retained

private theorem yielded_prefix_heap (limit : Nat) (control next : Control A)
    (before middle after : Checked width) (remaining : Control A) (fuel : Nat)
    (bounded : fuel ≤ limit) (initial : Good before) (initialHeap : Heap before.native.machine.heap)
    (fields : Fields control before) (actual : Trace fuel control before remaining after)
    (one : step control before = .yielded next middle) (heap : Heap middle.native.machine.heap)
    (rest : ∀ count, count ≤ limit → Good middle → Heap middle.native.machine.heap → Fields next middle →
      Trace count next middle remaining after → Heap after.native.machine.heap) : Heap after.native.machine.heap := by
  cases actual with
  | refl => exact initialHeap
  | cons control state resumed current final result count inputs observed tail =>
      have same := Outcome.yielded.inj (one.symm.trans observed)
      rcases same.1 with rfl
      rcases same.2 with rfl
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before initial inputs fields
      rw [one] at checked
      exact rest count (by omega) checked.1 heap checked.2.2.2.2.2 tail

private theorem guardFields_prefix_heap (limit : Nat)
    (nodes : ∀ (request : NodeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control (Value Symbol Constraint)), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.node request .pure)) before remaining after → Heap after.native.machine.heap)
    (edges : ∀ (request : EdgeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control (EdgeValue Symbol Constraint)), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.edge request .pure)) before remaining after → Heap after.native.machine.heap)
    (code : Code Symbol Constraint A) (checked : GuardFields code)
    (before after : Checked width) (remaining : Control A) (fuel : Nat) (bounded : fuel ≤ limit)
    (initial : Good before) (heap : Heap before.native.machine.heap) (fields : Fields (.code code) before)
    (actual : Trace fuel (.code code) before remaining after) : Heap after.native.machine.heap := by
  induction code generalizing before after remaining fuel with
  | pure value | fail failure =>
      cases actual with
      | refl => exact heap
      | cons control state next middle final result count inputs one tail => cases one
  | work job next ih =>
      let result := run job before.native.machine.heap
      let middle : Checked width := {before with native := advance before.native {before.native.machine with heap := result.2}}
      have one : step (.code (.work job next)) before = .yielded (.code (next result.1)) middle := rfl
      apply yielded_prefix_heap limit _ _ before middle after remaining fuel bounded initial heap fields actual one
        (SourceEqualityAnnotationHeap.run _ job checked.1 before.native.machine.heap heap)
      intro count bound good middleHeap retained tail
      exact ih result.1 (checked.2 result.1) middle after remaining count bound good middleHeap retained tail
  | enter domain left right first second next ih =>
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second
      let middle : Checked width := {before with native := advance before.native {before.native.machine with domains := entered.2}}
      have one : step (.code (.enter domain left right first second next)) before =
          .yielded (.code (next entered.1)) middle := rfl
      apply yielded_prefix_heap limit _ _ before middle after remaining fuel bounded initial heap fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih entered.1 (checked entered.1) middle after remaining count bound good middleHeap retained tail
  | read name next ih =>
      let found := SourcePreparedSharedRows.read before.native.machine.heap name
      have one : step (.code (.read name next)) before = .yielded (.code (next found)) before := rfl
      apply yielded_prefix_heap limit _ _ before before after remaining fuel bounded initial heap fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih found (checked found) before after remaining count bound good middleHeap retained tail
  | optionalBinder key body next ih =>
      cases actual with
      | refl => exact heap
      | cons control state rest middle final result count inputs one tail =>
          have currentHeap := step_optionalBinder_heap key body next
            before initial.native.machine.1 heap inputs
          rw [one, Outcome.state] at currentHeap
          have currentGood := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before initial inputs fields
          rw [one] at currentGood
          cases built : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
          | done value finalHeap =>
              simp only [step, SourceRecursiveIntersectionNative.step, built, lift] at one
              cases one
              exact ih value (checked value) _ after remaining count (by omega)
                currentGood.1 currentHeap currentGood.2.2.2.2.2 tail
          | pending pending finalHeap =>
              simp only [step, SourceRecursiveIntersectionNative.step, built, lift] at one
              cases one
  | node request next ih =>
      rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases fuel (.code (.node request .pure)) next
        before after remaining actual with
        ⟨inner, first, _nonpure, _same⟩ | ⟨innerFuel, outerFuel, value, middle, total, first, rest⟩
      · exact nodes request fuel bounded before after inner initial heap first
      · have middleHeap := nodes request innerFuel (by omega) before middle (.code (.pure value))
          initial heap first
        have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects (first.bind next) initial fields
        exact ih value (checked value) middle after remaining outerFuel (by omega)
          reached.1 middleHeap reached.2.2.2.2 rest
  | edge request next ih =>
      rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases fuel (.code (.edge request .pure)) next
        before after remaining actual with
        ⟨inner, first, _nonpure, _same⟩ | ⟨innerFuel, outerFuel, value, middle, total, first, rest⟩
      · exact edges request fuel bounded before after inner initial heap first
      · have middleHeap := edges request innerFuel (by omega) before middle (.code (.pure value))
          initial heap first
        have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects (first.bind next) initial fields
        exact ih value (checked value) middle after remaining outerFuel (by omega)
          reached.1 middleHeap reached.2.2.2.2 rest
  | finishNode handle value next ih =>
      let middle : Checked width := {before with native := SourceRecursiveIntersectionThunks.finishNode handle value before.native}
      have one : step (.code (.finishNode handle value next)) before = .yielded (.code next) middle := rfl
      apply yielded_prefix_heap limit _ _ before middle after remaining fuel bounded initial heap fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih checked middle after remaining count bound good middleHeap retained tail
  | finishEdge handle value next ih =>
      let middle : Checked width := {before with native := SourceRecursiveIntersectionThunks.finishEdge handle value before.native}
      have one : step (.code (.finishEdge handle value next)) before = .yielded (.code next) middle := rfl
      apply yielded_prefix_heap limit _ _ before middle after remaining fuel bounded initial heap fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih checked middle after remaining count bound good middleHeap retained tail

/-- Generated node compilation retains support at each actual prefix endpoint. -/
private theorem compileNode_prefix_heap (limit : Nat)
    (nodes : ∀ (request : NodeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control (Value Symbol Constraint)), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.node request .pure)) before remaining after → Heap after.native.machine.heap)
    (edges : ∀ (request : EdgeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control (EdgeValue Symbol Constraint)), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.edge request .pure)) before remaining after → Heap after.native.machine.heap)
    (request : NodeRequest Symbol Constraint) (before after : Checked width)
    (remaining : Control (Value Symbol Constraint)) (fuel : Nat) (bounded : fuel ≤ limit)
    (initial : Good before) (heap : Heap before.native.machine.heap)
    (actual : Trace fuel (.code (compileNode request)) before remaining after) : Heap after.native.machine.heap :=
  guardFields_prefix_heap limit nodes edges (compileNode request) (SourceCurrentNativeGuardCode.compileNode_fields _ request)
    before after remaining fuel bounded initial heap
    (SourceCurrentAllocatedNativeCodeFields.compileNode_fields before.operations request) actual


private theorem edge_work_prefix_heap (symbol : Symbol) (constraint : Guard)
    (children : List (Value Symbol Guard)) (fuel : Nat) (before after : Checked width)
    (remaining : Control (EdgeValue Symbol Guard))
    (heap : Heap before.native.machine.heap) (checked : ∃ classes, SourceCompactGuards.sourceEqualities constraint = some classes)
    (actual : Trace fuel (.code (.work (makeEdge symbol constraint children) .pure)) before remaining after) :
    Heap after.native.machine.heap := by
  cases actual with
  | refl => exact heap
  | cons control state next middle final result count inputs one tail =>
      cases one
      exact pure_prefix_heap _ _ after remaining count tail
        (SourceEqualityAnnotationHeap.run _ _
          (SourceEqualityAnnotationHeap.makeEdge _ symbol constraint children checked)
          before.native.machine.heap heap)

/-- An actual checked body prefix retains support at its exact remaining control. -/
private theorem body_prefix_heap
    (limit : Nat)
    (calls : ∀ (request : NodeRequest Symbol Guard) (count : Nat), count ≤ limit →
      ∀ (start final : Checked width) (remaining : Control (Value Symbol Guard)), Good start →
        Heap start.native.machine.heap →
        Trace count (.code (requestNode request.domain request.left request.right)) start remaining final →
        Heap final.native.machine.heap)
    (request : EdgeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (remaining : Control (EdgeValue Symbol Guard)) (bounded : fuel ≤ limit)
    (valid : Good before) (inputs : EdgeReady before.native.machine request)
    (heap : Heap before.native.machine.heap)
    (actual : Trace fuel (.edgeBody request .pure) before remaining after) :
    Heap after.native.machine.heap := by
  cases actual with
  | refl => exact heap
  | cons control state next started final result rest _operands one tail =>
      obtain ⟨code, same⟩ := SourceEqualityNativeDemandBodyYield.pure_yielded_code
        request before started next one
      subst next
      have firstTrace : Trace 1 (.edgeBody request .pure) before (.code code) started :=
        .cons _ _ _ _ _ _ 0 (by trivial) one (.refl _ _)
      have startedEffects := SourceCurrentAllocatedNativeSemanticTraceReadback.effects firstTrace valid
        (show Fields (.edgeBody request .pure) before from ⟨inputs, fun _ => trivial⟩)
      obtain ⟨nativeSame, branch⟩ :=
        SourcePruningEnumerationNativeCheckedOriginArity.body_choice_checked request before started code one
      have startedHeap : Heap started.native.machine.heap := by rw [nativeSame]; exact heap
      rcases branch with sentinelSame | ⟨first, second, combined, left, right, accepted, codeSame⟩
      · have workTrace : Trace rest
            (.code (.work (makeEdge request.left.entry.key.symbol top [.empty]) .pure)) started remaining after := by
          simpa only [sentinelSame, SourceEqualityNativeCheckedCode.sentinel] using tail
        exact edge_work_prefix_heap request.left.entry.key.symbol top [.empty] rest started after remaining
          startedHeap ⟨[], rfl⟩ workTrace
      · let call := fun pair : Value Symbol Guard × Value Symbol Guard =>
          requestNode request.domain pair.1 pair.2
        let children := request.left.children.zip request.right.children
        let finish : List (Value Symbol Guard) → Code Symbol Guard (EdgeValue Symbol Guard) := fun values =>
          .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure
        have childTrace : Trace rest ((.code (walk call children) : Control (List (Value Symbol Guard))).bind finish)
            started remaining after := by
          simpa only [codeSame, SourceEqualityNativeCheckedCode.children, Control.bind, call, children, finish] using tail
        have completed : ∀ (pair : Value Symbol Guard × Value Symbol Guard) (count : Nat), count ≤ limit →
            ∀ (start final : Checked width) (value : Value Symbol Guard), Good start →
              Heap start.native.machine.heap → Trace count (.code (call pair)) start (.code (.pure value)) final →
              Heap final.native.machine.heap := by
          intro pair count _bounded start final value good current called
          exact calls ⟨request.domain, pair.1, pair.2⟩ count _bounded
            start final (.code (.pure value)) good current called
        have fields : ∀ (pair : Value Symbol Guard × Value Symbol Guard) (state : Checked width),
            Fields (.code (call pair)) state := fun _ _ => fun _ => trivial
        rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases rest (.code (walk call children)) finish
            started after remaining childTrace with
          ⟨inner, walked, _nonpure, _same⟩ |
          ⟨walkFuel, outerFuel, values, middle, total, walked, later⟩
        · exact walk_prefix_heap limit call completed
            (fun pair count bound start final rest good current called =>
              calls ⟨request.domain, pair.1, pair.2⟩ count bound start final rest good current called)
            fields children rest started after inner (by omega) startedEffects.1 startedHeap walked
        · have earlier := SourceCurrentAllocatedNativeSemanticTraceReadback.walk_readback
            call children walkFuel started middle values walked
          have middleHeap := walk_heap limit call completed fields
            children values started middle walkFuel (by omega) startedEffects.1 startedHeap earlier
          have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.operations.constraints
            (valid.fields _ _ inputs.2.1).1 first left).1
          have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.operations.constraints
            (valid.fields _ _ inputs.2.2).1 second right).1
          obtain ⟨_accepted, classes, source, _projection, _validTries, _fits⟩ :=
            SourcePruningEnumerationNativeCheckedProjectable.ready_projectable
              GuardStructuralOrder.le first second combined request.left.children.length request.right.children.length
              before.operations valid.operations firstReady secondReady accepted
          exact edge_work_prefix_heap request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
            values outerFuel middle after remaining middleHeap ⟨classes, source⟩ later


/-- An actual node-request prefix uses only its shorter actual body prefix or a warm hit. -/
private theorem node_request_prefix_heap (request : NodeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (Value Symbol Guard)) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before remaining after)
    (bodies : ∀ (count : Nat) (original : NodeRequest Symbol Guard)
      (start final : Checked width) (rest : Control (Value Symbol Guard)), count < fuel →
      Good start → Heap start.native.machine.heap →
      Trace count (.code (compileNode original)) start rest final → Heap final.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before valid inputs (fun _ => trivial)
      have currentGood : Good current := by simpa only [one, Outcome.state] using checked.1
      have unchanged := SourcePruningEnumerationNativeRequestArity.node_step_heap request
        (.pure : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) before
      rw [show step (.code (.node request .pure)) before = .yielded next current from one, Outcome.state] at unchanged
      have currentHeap : Heap current.native.machine.heap := by rw [unchanged]; exact heap
      cases selected : lookupNode width request before.native with
      | mk selection chosen =>
          cases selection with
          | direct original =>
              simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, lift, code_bind_pure] at one
              cases one
              exact bodies count original _ after remaining (Nat.lt_succ_self _) currentGood currentHeap tail
          | memoized handle =>
              cases demanded : demandNode handle chosen with
              | mk observation running =>
                  cases observation with
                  | absent | busy =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                  | ready result =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                      exact pure_prefix_heap result _ after remaining count tail currentHeap
                  | evaluate original =>
                      simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                      rcases bind_prefix_cases count (.code (compileNode original))
                          (fun result => .finishNode handle result (.pure result)) _ after remaining tail with
                        ⟨inner, body, _nonpure, _same⟩ | ⟨inner, outer, result, middle, total, body, finish⟩
                      · exact bodies count original _ after inner (Nat.lt_succ_self _) currentGood currentHeap body
                      · have bodyHeap := bodies inner original _ middle (.code (.pure result)) (by omega) currentGood currentHeap body
                        exact finish_node_prefix_heap handle result middle after remaining outer finish bodyHeap

/-- An actual edge-request prefix retains the heap before, inside or after its checked body. -/
private theorem edge_request_prefix_heap (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (EdgeValue Symbol Guard)) (fuel : Nat)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before remaining after)
    (bodies : ∀ (count : Nat) (original : EdgeRequest Symbol Guard)
      (start final : Checked width) (rest : Control (EdgeValue Symbol Guard)), count < fuel →
      Good start → EdgeReady start.native.machine original → Heap start.native.machine.heap →
      Trace count (.edgeBody original .pure) start rest final → Heap final.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases trace with
  | refl => exact heap
  | cons control state next current final reached count inputs one tail =>
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before valid inputs (fun _ => trivial)
      have currentGood : Good current := by simpa only [one, Outcome.state] using checked.1
      have currentFields := checked.2.2.2.2.2
      rw [one] at currentFields
      have unchanged := SourceEqualityNativeDemandHeap.step_edge_heap request
        (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) before
      rw [show step (.code (.edge request .pure)) before = .yielded next current from one, Outcome.state] at unchanged
      have currentHeap : Heap current.native.machine.heap := by rw [unchanged]; exact heap
      cases selected : lookupEdge width request before.native with
      | mk handle chosen =>
          cases demanded : demandEdge handle chosen with
          | mk observation running =>
              cases observation with
              | absent | busy =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
              | ready result =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
                  exact pure_prefix_heap result _ after remaining count tail currentHeap
              | evaluate original =>
                  simp only [requestEdge, step, selected, demanded] at one
                  cases one
                  rcases bind_prefix_cases count (.edgeBody original .pure)
                      (fun result => .finishEdge handle result (.pure result)) _ after remaining tail with
                    ⟨inner, body, _nonpure, _same⟩ | ⟨inner, outer, result, middle, total, body, finish⟩
                  · exact bodies count original _ after inner (Nat.lt_succ_self _) currentGood currentFields.1 currentHeap body
                  · have bodyHeap := bodies inner original _ middle (.code (.pure result)) (by omega)
                      currentGood currentFields.1 currentHeap body
                    exact finish_edge_prefix_heap handle result middle after remaining outer finish bodyHeap


private theorem query_prefix_heaps (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before after : Checked width)
      (remaining : Control (Value Symbol Guard)), Good before → Heap before.native.machine.heap →
      Trace fuel (.code (requestNode request.domain request.left request.right)) before remaining after →
      Heap after.native.machine.heap) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before after : Checked width)
      (remaining : Control (EdgeValue Symbol Guard)), Good before → Heap before.native.machine.heap →
      Trace fuel (.code (requestEdge request.domain request.left request.right)) before remaining after →
      Heap after.native.machine.heap) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      constructor
      · intro request before after remaining valid heap trace
        apply node_request_prefix_heap request before after remaining fuel valid heap trace
        intro count original start final rest smaller good current actual
        apply compileNode_prefix_heap count
          (fun requested used bounded initial output resume checked origin called =>
            (ih used (by omega)).1 requested initial output resume checked origin called)
          (fun requested used bounded initial output resume checked origin called =>
            (ih used (by omega)).2 requested initial output resume checked origin called)
          original start final rest count (Nat.le_refl _) good current actual
      · intro request before after remaining valid heap trace
        apply edge_request_prefix_heap request before after remaining fuel valid heap trace
        intro count original start final rest smaller good ready current actual
        apply body_prefix_heap count
          (fun requested used bounded initial output resume checked origin called =>
            (ih used (by omega)).1 requested initial output resume checked origin called)
          original count start final rest (Nat.le_refl _) good ready current actual

/-- Every generated node-query prefix retains support for all current edge records. -/
theorem node_query_prefix_projectable (request : NodeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (Value Symbol Guard)) (fuel : Nat)
    (initial : Good before) (current : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before remaining after) :
    Heap after.native.machine.heap :=
  (query_prefix_heaps fuel).1 request before after remaining initial current trace

/-- Every generated edge-query prefix retains support, including warm hits and checked rejection. -/
theorem edge_query_prefix_projectable (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (EdgeValue Symbol Guard)) (fuel : Nat)
    (initial : Good before) (current : Heap before.native.machine.heap)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before remaining after) :
    Heap after.native.machine.heap :=
  (query_prefix_heaps fuel).2 request before after remaining initial current trace

/-- A checked edge-body prefix derives its own ready or sentinel support. -/
theorem body_prefix_projectable (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (remaining : Control (EdgeValue Symbol Guard)) (fuel : Nat)
    (initial : Good before) (inputs : EdgeReady before.native.machine request)
    (current : Heap before.native.machine.heap)
    (trace : Trace fuel (.edgeBody request .pure) before remaining after) :
    Heap after.native.machine.heap := by
  apply body_prefix_heap fuel _ request fuel before after remaining (Nat.le_refl _) initial inputs current trace
  intro requested count _bounded start final rest good known actual
  exact node_query_prefix_projectable requested start final rest count good known actual

/-- The observed physical execution ends at the same state before its final pure step. -/
private theorem checked_done_trace (fuel : Nat) (control : Control A)
    (before after : Checked width) (value : A)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel control before)
    (done : SourceEqualityNativeDemand.execute fuel control before = .done value after) :
    ∃ count, count < fuel ∧ Trace count control before (.code (.pure value)) after := by
  induction fuel generalizing control before with
  | zero => cases done
  | succ fuel ih =>
      cases one : SourceEqualityNativeDemand.step control before with
      | done result current =>
          have same := SourceEqualityNativeDemand.Outcome.done.inj
            (by simpa only [SourceEqualityNativeDemand.execute, one] using done)
          rcases same.1 with rfl
          rcases same.2 with rfl
          have pure := (SourceEqualityNativeDemand.step_done_iff control before current result).mp one
          rcases pure.1 with rfl
          rcases pure.2 with rfl
          exact ⟨0, by omega, .refl _ _⟩
      | yielded next current =>
          have restInputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel next current := by
            simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough, one] using inputs.2
          obtain ⟨count, bounded, trace⟩ :=
            ih next current restInputs (by simpa only [SourceEqualityNativeDemand.execute, one] using done)
          exact ⟨count + 1, by omega, .cons _ _ _ _ _ _ _ inputs.1 one trace⟩
      | failed | constraintError | blocked =>
          simp only [SourceEqualityNativeDemand.execute, one] at done
          cases done

/-- An observed successful node query retains support at its exact returned state. -/
theorem node_query_done_projectable (request : NodeRequest Symbol Guard)
    (before after : Checked width) (value : Value Symbol Guard) (fuel : Nat)
    (initial : Good before) (current : Heap before.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel
      (.code (requestNode request.domain request.left request.right)) before)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before =
      .done value after) :
    Heap after.native.machine.heap := by
  obtain ⟨count, _bounded, trace⟩ := checked_done_trace fuel _ before after value inputs done
  exact node_query_prefix_projectable request before after (.code (.pure value)) count initial current trace

/-- An observed successful edge query retains support at its exact returned state. -/
theorem edge_query_done_projectable (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (value : EdgeValue Symbol Guard) (fuel : Nat)
    (initial : Good before) (current : Heap before.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel
      (.code (requestEdge request.domain request.left request.right)) before)
    (done : execute fuel (.code (requestEdge request.domain request.left request.right)) before =
      .done value after) :
    Heap after.native.machine.heap := by
  obtain ⟨count, _bounded, trace⟩ := checked_done_trace fuel _ before after value inputs done
  exact edge_query_prefix_projectable request before after (.code (.pure value)) count initial current trace

/-- An observed successful checked body retains support at its exact returned state. -/
theorem body_done_projectable (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (value : EdgeValue Symbol Guard) (fuel : Nat)
    (initial : Good before) (operands : EdgeReady before.native.machine request)
    (current : Heap before.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel (.edgeBody request .pure) before)
    (done : execute fuel (.edgeBody request .pure) before = .done value after) :
    Heap after.native.machine.heap := by
  obtain ⟨count, _bounded, trace⟩ := checked_done_trace fuel _ before after value inputs done
  exact body_prefix_projectable request before after (.code (.pure value)) count initial operands current trace

end MicroCFTA.SourcePruningEnumerationNativeGeneratedProjectable
