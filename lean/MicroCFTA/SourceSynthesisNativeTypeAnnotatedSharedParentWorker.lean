import MicroCFTA.SourceSynthesisNativeTypeAnnotatedSharedLocalWorker
import MicroCFTA.SourceSynthesisNativeTypeParentHeap
import MicroCFTA.SourceSynthesisNativeTypeParentWorker
import MicroCFTA.SourceSynthesisHereditaryMemoFields
import MicroCFTA.SourceCurrentSharedParentNumeric

/-!
# Complete Type rows at shared Parent returns

The given numeric receipt retains the shared local reads and the exact
checked constructor. The current Context supplies the resident field and
precheck. The result retains the original full guard and adjusted children,
or the literal Top and Empty sentinel.

The receipt keeps its canonical read schedule. This proof does not change
that schedule to the bounds of another observed execution. Initial Context,
Type state, closed annotated children, and the given successful receipt
remain premises. These laws do not prove all reached inputs or completion.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeAnnotatedSharedParentWorker
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisNativeTypeTrace (Origin origin_top)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryMemoFields (TypeRow)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Coupled" => SourceSynthesisNativeTypeParentWorker.Coupled
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- The same shared Parent receipt retains every Type child and the full row guard. -/
theorem receipt_fields (lib : Library)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {entryInventory inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {profile : SourceCurrentAllocatedNativeResourceForecast.Profile} {budget : Nat}
    {before : Caller width} {memos final : Memos} {request : Request}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {after : Checked width} {result : Edge} {savedFourth : Fourth} {saved : Memo}
    (numeric : SourceCurrentSharedParentNumeric.Receipt formulas solver inventory profile budget
      request.value.entry.key.symbol request.value.entry.key.constraint loaded request.inherited
      request.value.children before memos result after savedFourth saved final)
    (context : Context formulas solver entryInventory before memos)
    (ready : Ready lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (closed : ClosedValues request.value.children) (inputTypeRow : TypeRow lib request.value) :
    Ready lib (initialShared after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ TypeRow lib result ∧ Coupled request.value result := by
  cases reads : numeric.reads with
  | rejected test =>
      have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver entryInventory
        request.value.entry.key.symbol before.checked context.ready context.admitted
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards⟩ :=
        SourceSynthesisNativeTypeParentHeap.reject lib constructor ready guards
      refine ⟨nextReady, extension, present, resultClosed, afterGuards, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [constructor.guard]
          exact origin_top lib
        · rw [constructor.children]
          intro child member
          cases List.mem_singleton.mp member
          exact .empty
      · exact ⟨constructor.symbol, Or.inr ⟨constructor.guard, constructor.children⟩⟩
  | @live children middle after savedFourth saved final result test lower built =>
      obtain ⟨cached, _stored, _storedLoad⟩ :=
        context.ready.good.fields request.value.entry.key request.value resident
      have found := numeric.field test
      have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
      obtain ⟨own, branch, precheck⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver entryInventory
        before.checked context.ready context.admitted request.value.entry.key.constraint cached loaded found
        request.inherited inheritedReady
      obtain ⟨middleReady, first, _middleAvailable, middleClosed, middleGuards, middleTyped⟩ :=
        SourceSynthesisNativeTypeAnnotatedSharedLocalWorker.reduce lib formulas solver precheck ready available
          closed guards inputTypeRow.2 lower.reads
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
      refine ⟨nextReady, first.trans last, present, resultClosed, afterGuards, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [constructor.guard]
          split
          · rw [loadedReady.2]
            exact inputTypeRow.1
          · exact origin_top lib
        · rw [constructor.children]
          split
          · exact middleTyped
          · intro child member
            cases List.mem_singleton.mp member
            exact .empty
      · refine ⟨constructor.symbol, ?_⟩
        cases keep : SourceEqualityMkEdgeAllocation.accepted
            (SourceEqualityConjoinAllocation.readback loaded) children.length with
        | true =>
            have guardEq : result.entry.key.constraint = SourceEqualityConjoinAllocation.readback loaded := by
              simpa only [keep, ite_true] using constructor.guard
            have sameChildren : result.children = children := by
              simpa only [keep, ite_true] using constructor.children
            exact Or.inl ⟨guardEq.trans loadedReady.2,
              (congrArg List.length sameChildren).trans lower.semantic.length⟩
        | false =>
            exact Or.inr ⟨by simpa only [keep, Bool.false_eq_true, ite_false,
                SourceEqualityConstraintConstructors.top, SourceSynthesisGeneralizeSyntax.top] using constructor.guard,
              by simpa only [keep, Bool.false_eq_true, ite_false] using constructor.children⟩

end MicroCFTA.SourceSynthesisNativeTypeAnnotatedSharedParentWorker
