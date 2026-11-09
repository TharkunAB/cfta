import MicroCFTA.SourceSynthesisNativeTypeHereditarySharedLocalWorker
import MicroCFTA.SourceSynthesisNativeTypeLocalTrivialWorker
import MicroCFTA.SourceSynthesisNativeTypeParentHeap
import MicroCFTA.SourceSynthesisNativeTypeParentWorker
import MicroCFTA.SourceCurrentSharedParentNumeric

/-!
# Coupled recursive fields at shared Parent returns

The given numeric receipt retains the actual shared local reads.
The current resident field supplies precheck. The same constructor keeps
its full guard and child layout together. Program slots retain their
recursive fields. A rejected constructor returns the exact Empty sentinel.
No future field, range plan or completed old worker is an input.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedParentWorker
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "Coupled" => SourceSynthesisNativeTypeParentWorker.Coupled
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Precheck" => SourceCurrentAllocatedPrecheck.Receipt
variable {width : Nat}

private def Slots (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop) (values : List Node) : Prop :=
  ∀ index value, values[index]? = some value →
    (assigned index → ValueFields (Origin lib) literal value) ∧
      (¬ assigned index → Annotated (Origin lib) value)

private theorem empty_slots (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop)
    (values : List Node) : Slots lib literal assigned (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  intro index value found
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? found)
  exact ⟨fun _ => .empty, fun _ => .empty⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem local_fields (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop)
    {formulas solver entryInventory inventory profile budget guard loaded inherited values before memos final}
    {children : List Node} {middle : Checked width} {fourth : Fourth} {memo : Memo}
    (lower : SourceCurrentSharedLocalNumeric.Receipt formulas solver inventory profile budget guard loaded inherited
      values before memos children middle fourth memo final)
    (context : Context formulas solver entryInventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (cached : SourceEqualityGuardReadback.Cached guard.equalities)
    (found : SourceEqualityConstraintFieldLookup.load guard before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values) (closed : ClosedValues values)
    (inputs : Slots lib literal assigned values)
    (classes : ∀ own records,
      Precheck formulas solver entryInventory guard loaded inherited before.checked own (.classes records) →
      Ready lib (initial middle memo) ∧ Extension before.checked.native.machine middle.native.machine ∧
        ClosedValues children ∧ GuardHeap (Origin lib) middle.native.machine.heap ∧ Slots lib literal assigned children) :
    Ready lib (initial middle memo) ∧ Extension before.checked.native.machine middle.native.machine ∧
      ClosedValues children ∧ GuardHeap (Origin lib) middle.native.machine.heap ∧ Slots lib literal assigned children := by
  obtain ⟨own, branch, precheck⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver entryInventory
    before.checked context.ready context.admitted guard cached loaded found inherited inheritedReady
  cases branch with
  | classes records => exact classes own records precheck
  | unchanged =>
      let bound := SourceCurrentSharedLocalForecast.fuel budget values.length loaded inherited before.checked profile
      have ran := lower.run bound bound bound bound bound bound bound bound bound
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      simp only [SourceCurrentAllocatedSharedLocalWorker.reduce, precheck.actual] at ran
      cases ran
      obtain ⟨_literal, next, extension, _present, resultClosed, retained, _routes, _slots⟩ :=
        SourceSynthesisNativeTypeLocalTrivialWorker.unchanged lib 0 0 0 0 0 0 0 0 0 budget before.fourth
          precheck ready available closed guards
      exact ⟨next, extension, resultClosed, retained, inputs⟩
  | emptyChildren =>
      let bound := SourceCurrentSharedLocalForecast.fuel budget values.length loaded inherited before.checked profile
      have ran := lower.run bound bound bound bound bound bound bound bound bound
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      simp only [SourceCurrentAllocatedSharedLocalWorker.reduce, precheck.actual] at ran
      cases ran
      obtain ⟨_literal, next, extension, _present, resultClosed, retained, _routes, _slots⟩ :=
        SourceSynthesisNativeTypeLocalTrivialWorker.emptyChildren lib 0 0 0 0 0 0 0 0 0 budget before.fourth
          precheck ready guards
      exact ⟨next, extension, resultClosed, retained, empty_slots lib literal assigned values⟩

section Parent
variable (lib : Library) (literal : String → Symbol)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {entryInventory inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {profile : SourceCurrentAllocatedNativeResourceForecast.Profile} {budget : Nat}
variable {before : Caller width} {memos final : Memos} {request : Request} {loaded : Allocated}
variable {after : Checked width} {result : Edge} {savedFourth : Fourth} {saved : Memo}
variable (numeric : SourceCurrentSharedParentNumeric.Receipt formulas solver inventory profile budget
  request.value.entry.key.symbol request.value.entry.key.constraint loaded request.inherited
  request.value.children before memos result after savedFourth saved final)
variable (context : Context formulas solver entryInventory before memos)
variable (ready : Ready lib (initial before.checked before.merge))
variable (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
variable (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
variable (resident : Resident before.checked.native.machine.heap request.value)
variable (closed : ClosedValues request.value.children)

include numeric context ready guards resident in
private theorem parent_fields (assigned : Nat → Prop)
    (preserve : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
      ∀ {children middle fourth memo final},
      SourceCurrentSharedLocalNumeric.Receipt formulas solver inventory profile budget request.value.entry.key.constraint loaded
        request.inherited request.value.children before memos children middle fourth memo final →
      Ready lib (initial middle memo) ∧ Extension before.checked.native.machine middle.native.machine ∧
        ClosedValues children ∧ GuardHeap (Origin lib) middle.native.machine.heap ∧ Slots lib literal assigned children) :
    Ready lib (initial after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Coupled request.value result ∧ Slots lib literal assigned result.children := by
  cases reads : numeric.reads with
  | rejected test =>
      have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver entryInventory
        request.value.entry.key.symbol before.checked context.ready context.admitted
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards⟩ :=
        SourceSynthesisNativeTypeParentHeap.reject lib constructor ready guards
      refine ⟨nextReady, extension, present, resultClosed, afterGuards,
        ⟨constructor.symbol, Or.inr ⟨constructor.guard, constructor.children⟩⟩, ?_⟩
      rw [constructor.children]
      intro index value found
      cases List.mem_singleton.mp (List.mem_of_getElem? found)
      exact ⟨fun _ => .empty, fun _ => .empty⟩
  | @live children middle after savedFourth saved final result test lower built =>
      have cached := (context.ready.good.fields request.value.entry.key request.value resident).1
      have found := numeric.field test
      obtain ⟨middleReady, first, middleClosed, middleGuards, slots⟩ := preserve test lower
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready request.value.entry.key.constraint
        before.checked.operations.constraints context.ready.good.operations.constraints cached loaded found
      have storedReady := loadedReady.1.grows lower.semantic.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations
          (SourceEqualityConjoinAllocation.readback loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations request.value.entry.key.constraint
          from ⟨cached, loaded, found⟩).grows lower.semantic.effects.grows
      obtain ⟨chosen, reached, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver inventory
        request.value.entry.key.symbol loaded children middle lower.semantic.ready lower.semantic.admitted
        storedReady field lower.semantic.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      cases Except.ok.inj same.1
      cases same.2
      obtain ⟨nextReady, last, present, resultClosed, afterGuards⟩ :=
        SourceSynthesisNativeTypeParentHeap.build lib constructor middleReady middleGuards middleClosed
      refine ⟨nextReady, first.trans last, present, resultClosed, afterGuards, ⟨constructor.symbol, ?_⟩, ?_⟩
      · cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
        | true =>
            have guardEq := constructor.guard
            simp only [keep, ite_true] at guardEq
            have childrenEq := constructor.children
            simp only [keep, ite_true] at childrenEq
            exact Or.inl ⟨guardEq.trans loadedReady.2,
              (congrArg List.length childrenEq).trans lower.semantic.length⟩
        | false =>
            exact Or.inr ⟨by simpa only [keep, Bool.false_eq_true, ite_false,
                SourceEqualityConstraintConstructors.top, SourceSynthesisGeneralizeSyntax.top] using constructor.guard,
              by simpa only [keep, Bool.false_eq_true, ite_false] using constructor.children⟩
      · rw [constructor.children]
        split
        · exact slots
        · intro index value found
          cases List.mem_singleton.mp (List.mem_of_getElem? found)
          exact ⟨fun _ => .empty, fun _ => .empty⟩

section Application
variable (types function argument : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : SourceSynthesisFirstOrderConstruction.application types function argument =
  .node [.mk sourceName request.value.entry.key.constraint sourceChildren])
variable (typed : ∀ index value, request.value.children[index]? = some value →
  ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
variable (fields : ∀ index value, request.value.children[index]? = some value →
  (index = 2 ∨ index = 3) → ValueFields (Origin lib) literal value)
include numeric context ready guards inheritedReady resident closed occurrence typed fields in
/-- The shared application Parent retains the exact coupled guard and recursive slots. -/
theorem application_fields :
    Ready lib (initial after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Coupled request.value result ∧
      ∀ index value, result.children[index]? = some value →
        ((index = 2 ∨ index = 3) → ValueFields (Origin lib) literal value) ∧
          (¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value) := by
  apply parent_fields lib literal formulas solver numeric context ready guards resident (fun index => index = 2 ∨ index = 3)
  intro test children middle fourth memo final lower
  have cached := (context.ready.good.fields request.value.entry.key request.value resident).1
  have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  apply local_fields lib literal (fun index => index = 2 ∨ index = 3) lower context ready guards
    cached (numeric.field test)
    inheritedReady available closed (fun index value found => ⟨fields index value found, typed index value found⟩)
  intro own records precheck
  obtain ⟨next, extension, _known, resultClosed, retained, _routes, slots⟩ :=
    SourceSynthesisNativeTypeHereditarySharedLocalWorker.application_reduce
      (lib := lib) (literal := literal) (formulas := formulas) (solver := solver) (receipt := precheck)
      (ready := ready) (available := available) (closed := closed) (guards := guards)
      (types := types) (function := function) (argument := argument) (sourceName := sourceName)
      (sourceChildren := sourceChildren) (occurrence := occurrence) (typed := typed) (fields := fields) lower.reads
  exact ⟨next, extension, resultClosed, retained, slots⟩
end Application

section Filter
variable (candidates goal : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : SourceSynthesisFirstOrderConstruction.ofType candidates goal =
  .node [.mk sourceName request.value.entry.key.constraint sourceChildren])
variable (typed : ∀ index value, request.value.children[index]? = some value → index ≠ 1 → Annotated (Origin lib) value)
variable (fields : ∀ index value, request.value.children[index]? = some value →
  index = 1 → ValueFields (Origin lib) literal value)
include numeric context ready guards inheritedReady resident closed occurrence typed fields in
/-- The shared filter Parent retains the exact coupled guard and recursive slots. -/
theorem filter_fields :
    Ready lib (initial after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Coupled request.value result ∧
      ∀ index value, result.children[index]? = some value →
        (index = 1 → ValueFields (Origin lib) literal value) ∧ (index ≠ 1 → Annotated (Origin lib) value) := by
  apply parent_fields lib literal formulas solver numeric context ready guards resident (fun index => index = 1)
  intro test children middle fourth memo final lower
  have cached := (context.ready.good.fields request.value.entry.key request.value resident).1
  have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  apply local_fields lib literal (fun index => index = 1) lower context ready guards
    cached (numeric.field test)
    inheritedReady available closed (fun index value found => ⟨fields index value found, typed index value found⟩)
  intro own records precheck
  obtain ⟨next, extension, _known, resultClosed, retained, _routes, slots⟩ :=
    SourceSynthesisNativeTypeHereditarySharedLocalWorker.filter_reduce
      (lib := lib) (literal := literal) (formulas := formulas) (solver := solver) (receipt := precheck)
      (ready := ready) (available := available) (closed := closed) (guards := guards)
      (candidates := candidates) (goal := goal) (sourceName := sourceName) (sourceChildren := sourceChildren)
      (occurrence := occurrence) (typed := typed) (fields := fields) lower.reads
  exact ⟨next, extension, resultClosed, retained, slots⟩
end Filter
end Parent
end MicroCFTA.SourceSynthesisNativeTypeSharedParentWorker
