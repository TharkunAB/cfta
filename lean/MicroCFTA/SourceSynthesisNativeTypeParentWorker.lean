import MicroCFTA.SourceSynthesisNativeTypeLocalSlotWorker
import MicroCFTA.SourceSynthesisNativeTypeLocalTrivialWorker
import MicroCFTA.SourceSynthesisNativeTypeParentHeap
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual
import MicroCFTA.SourceCurrentAllocatedLocalWorkerActual

/-!
# Type fields at actual application and filter Parent returns

The initial resident row supplies its actual stored-field load. Precheck
derives its branch receipt. Literal local work retains every mixed slot.
The same constructor test selects the original guard and layout together,
or Top and the single Empty sentinel. Actual caller facts derive the
returned Parent graph, source reads and caller postcondition.
Program guards need no Type annotation. Initial source roles, successful
execution and reached range plans remain premises. All reached roles,
failed prefixes, completion and global bounds remain separate obligations.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeParentWorker
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "callerAdvance" => SourceCurrentAllocatedPartialState.advance
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory

/-- Program slots retain their first fields; other slots retain full Type annotations. -/
def MixedSlots (lib : Library) (assigned : Nat → Prop) (values : List Node) : Prop :=
  ∀ index value, values[index]? = some value →
    (assigned index → AnnotationFields (Origin lib) value) ∧
      (¬ assigned index → Annotated (Origin lib) value)

/-- One source check retains the guard and arity together or returns the exact sentinel. -/
def Coupled (original result : EdgeValue Symbol Guard) : Prop :=
  result.entry.key.symbol = original.entry.key.symbol ∧
    ((result.entry.key.constraint = original.entry.key.constraint ∧ result.children.length = original.children.length) ∨
      (result.entry.key.constraint = top ∧ result.children = [.empty]))

private theorem empty_slots (lib : Library) (assigned : Nat → Prop) : MixedSlots lib assigned [.empty] := by
  intro index value found
  cases List.mem_singleton.mp (List.mem_of_getElem? found)
  exact ⟨fun _ => .empty, fun _ => .empty⟩

variable {width : Nat}

private theorem bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {result : B} {after : Checked width} {fourth : Fourth} {memo : Memo}
    (actual : first.bind next = .done result after fourth memo) :
    ∃ value middle saved warm, first = .done value middle saved warm ∧
      next value middle saved warm = .done result after fourth memo := by
  cases first with
  | done value middle saved warm => exact ⟨value, middle, saved, warm, rfl, actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem reduce_return {g s r e p h m c n budget loaded inherited children before fourth memo results after saved warm}
    (actual : SourceCurrentAllocatedParentWorker.reduceChildren (width := width) g s r e p h m c n budget
      loaded inherited children before fourth memo = .done results after saved warm) :
    SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited children before fourth memo =
      .done results after saved warm := by
  cases observed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited children before fourth memo with
  | failed => simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at actual; cases actual
  | done value checked completed current =>
      simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at actual
      cases actual
      rfl

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem build_return {symbol loaded children before fourth memo result after saved warm}
    (actual : SourceCurrentAllocatedParentWorker.build (width := width) symbol loaded children before fourth memo =
      .done result after saved warm) :
    SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result, after) ∧
      saved = fourth ∧ warm = memo := by
  cases observed : SourceCurrentAllocatedMkEdge.build symbol loaded children before with
  | mk built checked =>
      cases built with
      | error => simp only [SourceCurrentAllocatedParentWorker.build, observed] at actual; cases actual
      | ok value =>
          simp only [SourceCurrentAllocatedParentWorker.build, observed] at actual
          cases actual
          exact ⟨rfl, rfl, rfl⟩

section SourceCaller
variable (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {before : Caller width} {memos : Memos} {request : Request}
variable {g s r e p h m c n budget : Nat} {after : Checked width}
variable {result : EdgeValue Symbol Guard} {savedFourth : Fourth} {saved : Memo}
variable (context : Context formulas solver inventory before memos)
variable (ready : Ready lib (initialShared before.checked before.merge))
variable (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
variable (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
variable (resident : Resident before.checked.native.machine.heap request.value)
variable (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before)
variable (closed : ClosedValues request.value.children)

include context inheritedReady ranges in
private theorem finish (assigned : Nat → Prop) {loaded : Allocated}
    {children : List Node} {middle : Checked width} {fourth : Fourth} {memo : Memo}
    (cached : SourceEqualityGuardReadback.Cached request.value.entry.key.constraint.equalities)
    (found : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
      .ok (some loaded)) (live : contradictory request.value.entry.key.constraint = false)
    (available : Values before.checked.native.machine.heap request.value.children)
    (reduced : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded request.inherited
      request.value.children before.checked before.fourth before.merge = .done children middle fourth memo)
    (middleReady : Ready lib (initialShared middle memo))
    (first : Extension before.checked.native.machine middle.native.machine)
    (middleClosed : ClosedValues children) (middleGuards : GuardHeap (Origin lib) middle.native.machine.heap)
    (slots : MixedSlots lib assigned children)
    (built : SourceCurrentAllocatedMkEdge.build request.value.entry.key.symbol loaded children middle = (.ok result, after)) :
    Ready lib (initialShared after memo) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Coupled request.value result ∧ MixedSlots lib assigned result.children := by
  have loadedReady := SourceEqualityConstraintFieldLookup.load_ready request.value.entry.key.constraint
    before.checked.operations.constraints context.ready.good.operations.constraints cached loaded found
  obtain ⟨next, final, _graph, _reads, localReceipt⟩ := SourceCurrentAllocatedLocalWorkerActual.sound formulas solver
    context cached found inheritedReady available (ranges live loaded found) reduced
  have storedReady := loadedReady.1.grows localReceipt.effects.grows.constraint_growth
  have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations
      (SourceEqualityConjoinAllocation.readback loaded) := by
    rw [loadedReady.2]
    exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations request.value.entry.key.constraint
      from ⟨cached, loaded, found⟩).grows localReceipt.effects.grows
  obtain ⟨chosen, reached, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next
    request.value.entry.key.symbol loaded children middle localReceipt.ready localReceipt.admitted storedReady field localReceipt.available
  have same := Prod.mk.inj (constructor.actual.symm.trans built)
  cases Except.ok.inj same.1
  cases same.2
  obtain ⟨nextReady, last, present, resultClosed, afterGuards⟩ :=
    SourceSynthesisNativeTypeParentHeap.build lib constructor middleReady middleGuards middleClosed
  refine ⟨nextReady, first.trans last, present, resultClosed, afterGuards, ⟨constructor.symbol, ?_⟩, ?_⟩
  · cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
    | true =>
        have childrenEq : result.children = children := by simpa only [keep, ite_true] using constructor.children
        have guardEq : result.entry.key.constraint = SourceEqualityConjoinAllocation.readback loaded := by
          simpa only [keep, ite_true] using constructor.guard
        exact Or.inl ⟨guardEq.trans loadedReady.2,
          (congrArg List.length childrenEq).trans localReceipt.length⟩
    | false =>
        exact Or.inr ⟨by simpa only [keep, Bool.false_eq_true, ite_false,
            SourceEqualityConstraintConstructors.top, SourceSynthesisGeneralizeSyntax.top] using constructor.guard,
          by simpa only [keep, Bool.false_eq_true, ite_false] using constructor.children⟩
  · rw [constructor.children]
    split
    · exact slots
    · exact empty_slots lib assigned

section Application
variable (types function argument : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : SourceSynthesisFirstOrderConstruction.application types function argument =
  .node [.mk sourceName request.value.entry.key.constraint sourceChildren])
variable (typed : ∀ index value, request.value.children[index]? = some value →
  ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
variable (fields : ∀ index value, request.value.children[index]? = some value →
  (index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value)

include context ready guards inheritedReady ranges closed occurrence typed fields in
private theorem application_local {loaded : Allocated} {children : List Node}
    {middle : Checked width} {fourth : Fourth} {memo : Memo}
    (cached : SourceEqualityGuardReadback.Cached request.value.entry.key.constraint.equalities)
    (found : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
      .ok (some loaded)) (live : contradictory request.value.entry.key.constraint = false)
    (available : Values before.checked.native.machine.heap request.value.children)
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded request.inherited
      request.value.children before.checked before.fourth before.merge = .done children middle fourth memo) :
    Ready lib (initialShared middle memo) ∧ Extension before.checked.native.machine middle.native.machine ∧
      Values middle.native.machine.heap children ∧ ClosedValues children ∧
      GuardHeap (Origin lib) middle.native.machine.heap ∧ MixedSlots lib (fun index => index = 2 ∨ index = 3) children := by
  obtain ⟨own, branch, receipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before.checked context.ready context.admitted request.value.entry.key.constraint cached loaded found request.inherited inheritedReady
  cases branch with
  | classes records =>
      obtain ⟨next, extension, known, resultClosed, afterGuards, _routes, slots⟩ :=
        SourceSynthesisNativeTypeLocalSlotWorker.application_reduce
          (lib := lib) (formulas := formulas) (solver := solver) (receipt := receipt) (ready := ready)
          (available := available) (closed := closed) (guards := guards)
          (ranges := ranges live loaded found records receipt.actual)
          (types := types) (function := function) (argument := argument) (sourceName := sourceName)
          (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) actual
      exact ⟨next, extension, known, resultClosed, afterGuards, slots⟩
  | unchanged =>
      obtain ⟨literal, next, extension, known, resultClosed, afterGuards, _, slots⟩ :=
        SourceSynthesisNativeTypeLocalTrivialWorker.unchanged lib g s r e p h m c n budget before.fourth
          receipt ready available closed guards
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ := SourceCurrentAllocatedLocalWorker.Outcome.done.inj (literal.symm.trans actual)
      cases sameValues
      cases sameState
      cases sameFourth
      cases sameMemo
      exact ⟨next, extension, known, resultClosed, afterGuards,
        slots _ (fun index value found => ⟨fields index value found, typed index value found⟩)⟩
  | emptyChildren =>
      obtain ⟨literal, next, extension, known, resultClosed, afterGuards, _, slots⟩ :=
        SourceSynthesisNativeTypeLocalTrivialWorker.emptyChildren lib g s r e p h m c n budget before.fourth receipt ready guards
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ := SourceCurrentAllocatedLocalWorker.Outcome.done.inj (literal.symm.trans actual)
      cases sameValues
      cases sameState
      cases sameFourth
      cases sameMemo
      exact ⟨next, extension, known, resultClosed, afterGuards, slots _⟩

include context ready guards inheritedReady resident ranges closed occurrence typed fields in
/-- Literal application Parent work returns its actual caller and coupled Type fields. -/
theorem application
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge =
        .done result after savedFourth saved) :
    ∃ next final, ∃ body : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
        (callerAdvance before after savedFourth saved),
      SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver body memos final ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
        (callerAdvance before after savedFourth saved) final ∧
      Post formulas solver next before (callerAdvance before after savedFourth saved) final ∧
      Ready lib (initialShared after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Coupled request.value result ∧
      MixedSlots lib (fun index => index = 2 ∨ index = 3) result.children := by
  obtain ⟨next, final, body, reads, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.resident_verified
    formulas solver context inheritedReady resident ranges actual
  refine ⟨next, final, body, reads, receipt, post, ?_⟩
  cases rejected : contradictory request.value.entry.key.constraint with
  | true =>
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, ite_true] at actual
      cases actual
      have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
        request.value.entry.key.symbol before.checked context.ready context.admitted
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards⟩ :=
        SourceSynthesisNativeTypeParentHeap.reject lib constructor ready guards
      refine ⟨nextReady, extension, present, resultClosed, afterGuards,
        ⟨constructor.symbol, Or.inr ⟨constructor.guard, constructor.children⟩⟩, ?_⟩
      rw [constructor.children]
      exact empty_slots lib _
  | false =>
      obtain ⟨cached, loaded, found⟩ := context.ready.good.fields request.value.entry.key request.value resident
      have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, Bool.false_eq_true, ite_false, found] at actual
      obtain ⟨children, middle, fourth, memo, reduced, built⟩ := bind_done _ _ actual
      have reduced := reduce_return reduced
      obtain ⟨constructed, sameFourth, sameMemo⟩ := build_return built
      subst fourth
      subst memo
      obtain ⟨middleReady, first, _, middleClosed, middleGuards, slots⟩ :=
        application_local (lib := lib) (formulas := formulas) (solver := solver) (context := context)
          (ready := ready) (guards := guards) (inheritedReady := inheritedReady) (ranges := ranges)
          (closed := closed) (types := types) (function := function) (argument := argument) (sourceName := sourceName)
          (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields)
          cached found rejected available reduced
      exact finish lib formulas solver context inheritedReady ranges (fun index => index = 2 ∨ index = 3)
        cached found rejected available reduced middleReady first middleClosed middleGuards slots constructed
end Application

section Filter
variable (candidates goal : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : SourceSynthesisFirstOrderConstruction.ofType candidates goal =
  .node [.mk sourceName request.value.entry.key.constraint sourceChildren])
variable (typed : ∀ index value, request.value.children[index]? = some value → index ≠ 1 → Annotated (Origin lib) value)
variable (fields : ∀ index value, request.value.children[index]? = some value → index = 1 → AnnotationFields (Origin lib) value)

include context ready guards inheritedReady ranges closed occurrence typed fields in
private theorem filter_local {loaded : Allocated} {children : List Node}
    {middle : Checked width} {fourth : Fourth} {memo : Memo}
    (cached : SourceEqualityGuardReadback.Cached request.value.entry.key.constraint.equalities)
    (found : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
      .ok (some loaded)) (live : contradictory request.value.entry.key.constraint = false)
    (available : Values before.checked.native.machine.heap request.value.children)
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded request.inherited
      request.value.children before.checked before.fourth before.merge = .done children middle fourth memo) :
    Ready lib (initialShared middle memo) ∧ Extension before.checked.native.machine middle.native.machine ∧
      Values middle.native.machine.heap children ∧ ClosedValues children ∧
      GuardHeap (Origin lib) middle.native.machine.heap ∧ MixedSlots lib (fun index => index = 1) children := by
  obtain ⟨own, branch, receipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before.checked context.ready context.admitted request.value.entry.key.constraint cached loaded found request.inherited inheritedReady
  cases branch with
  | classes records =>
      obtain ⟨next, extension, known, resultClosed, afterGuards, _routes, slots⟩ :=
        SourceSynthesisNativeTypeLocalSlotWorker.filter_reduce
          (lib := lib) (formulas := formulas) (solver := solver) (receipt := receipt) (ready := ready)
          (available := available) (closed := closed) (guards := guards)
          (ranges := ranges live loaded found records receipt.actual) (candidates := candidates) (goal := goal)
          (sourceName := sourceName) (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) actual
      exact ⟨next, extension, known, resultClosed, afterGuards, slots⟩
  | unchanged =>
      obtain ⟨literal, next, extension, known, resultClosed, afterGuards, _, slots⟩ :=
        SourceSynthesisNativeTypeLocalTrivialWorker.unchanged lib g s r e p h m c n budget before.fourth
          receipt ready available closed guards
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ := SourceCurrentAllocatedLocalWorker.Outcome.done.inj (literal.symm.trans actual)
      cases sameValues
      cases sameState
      cases sameFourth
      cases sameMemo
      exact ⟨next, extension, known, resultClosed, afterGuards,
        slots _ (fun index value found => ⟨fields index value found, typed index value found⟩)⟩
  | emptyChildren =>
      obtain ⟨literal, next, extension, known, resultClosed, afterGuards, _, slots⟩ :=
        SourceSynthesisNativeTypeLocalTrivialWorker.emptyChildren lib g s r e p h m c n budget before.fourth receipt ready guards
      obtain ⟨sameValues, sameState, sameFourth, sameMemo⟩ := SourceCurrentAllocatedLocalWorker.Outcome.done.inj (literal.symm.trans actual)
      cases sameValues
      cases sameState
      cases sameFourth
      cases sameMemo
      exact ⟨next, extension, known, resultClosed, afterGuards, slots _⟩

include context ready guards inheritedReady resident ranges closed occurrence typed fields in
/-- Literal filter Parent work returns its actual caller and coupled Type fields. -/
theorem filter
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge =
        .done result after savedFourth saved) :
    ∃ next final, ∃ body : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
        (callerAdvance before after savedFourth saved),
      SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver body memos final ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
        (callerAdvance before after savedFourth saved) final ∧
      Post formulas solver next before (callerAdvance before after savedFourth saved) final ∧
      Ready lib (initialShared after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Coupled request.value result ∧
      MixedSlots lib (fun index => index = 1) result.children := by
  obtain ⟨next, final, body, reads, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.resident_verified
    formulas solver context inheritedReady resident ranges actual
  refine ⟨next, final, body, reads, receipt, post, ?_⟩
  cases rejected : contradictory request.value.entry.key.constraint with
  | true =>
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, ite_true] at actual
      cases actual
      have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
        request.value.entry.key.symbol before.checked context.ready context.admitted
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards⟩ :=
        SourceSynthesisNativeTypeParentHeap.reject lib constructor ready guards
      refine ⟨nextReady, extension, present, resultClosed, afterGuards,
        ⟨constructor.symbol, Or.inr ⟨constructor.guard, constructor.children⟩⟩, ?_⟩
      rw [constructor.children]
      exact empty_slots lib _
  | false =>
      obtain ⟨cached, loaded, found⟩ := context.ready.good.fields request.value.entry.key request.value resident
      have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, Bool.false_eq_true, ite_false, found] at actual
      obtain ⟨children, middle, fourth, memo, reduced, built⟩ := bind_done _ _ actual
      have reduced := reduce_return reduced
      obtain ⟨constructed, sameFourth, sameMemo⟩ := build_return built
      subst fourth
      subst memo
      obtain ⟨middleReady, first, _, middleClosed, middleGuards, slots⟩ :=
        filter_local (lib := lib) (formulas := formulas) (solver := solver) (context := context)
          (ready := ready) (guards := guards) (inheritedReady := inheritedReady) (ranges := ranges)
          (closed := closed) (candidates := candidates) (goal := goal) (sourceName := sourceName)
          (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields)
          cached found rejected available reduced
      exact finish lib formulas solver context inheritedReady ranges (fun index => index = 1)
        cached found rejected available reduced middleReady first middleClosed middleGuards slots constructed
end Filter
end SourceCaller
end MicroCFTA.SourceSynthesisNativeTypeParentWorker
