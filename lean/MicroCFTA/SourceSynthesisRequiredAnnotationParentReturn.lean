import MicroCFTA.SourceSynthesisRequiredAnnotationPreparationPass
import MicroCFTA.SourceSynthesisNativeTypeSharedParentWorker

/-!
# Ordinary annotation heads at the selected Parent return

The demand predicates name a completed cut of the given current reads.
They retain one actual selected annotation descendant. They do not assert
that unchanged or skipped scans establish that descendant. Current caller
facts derive Precheck and the warm state at the literal Scan return.
The same Required and pass results reach the checked Parent constructor.
Its exact children equation transfers the ordinary-head property.
-/
namespace MicroCFTA.SourceSynthesisRequiredAnnotationParentReturn
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression application)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisRequiredAnnotationClassPass (AtFunction)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceEqualityClassOrder (Record)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Coupled" => SourceSynthesisNativeTypeParentWorker.Coupled
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A completed class cut retains a descendant of the function annotation. -/
inductive ClassDemand (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {records : List Record} → {values results : List Node} →
    {before after : Checked width} → {fourth savedFourth : Fourth} → {memo saved : Memo} →
    {outcome : Option EqualityNormalize.Class} →
    {execution : SourceCurrentSharedClassesNumeric.Execution budget records values before fourth memo
      outcome results after savedFourth saved} → {memos final : Memos} →
    SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final → Prop where
  | completed {budget records values before fourth memo kept prepared middle savedFourth results after saved}
      {preparation : SourceCurrentSharedScanRequiredNumeric.Execution budget records values before fourth
        none kept prepared middle savedFourth}
      {passed : SourceCurrentAllocatedClassPass.Pass kept prepared middle memo results after saved}
      {memos current final}
      (first : SourceCurrentSharedScanRequiredNumeric.Reads preparation memos current)
      (last : SourceCurrentAllocatedClassPass.PassReads formulas solver passed current final)
      {descendant : Int} {tail : List Int}
      (included : (2 :: 0 :: descendant :: tail : List Int) ∈
        SourceEqualitySelectedRequired.paths (kept.map Record.paths)) :
      ClassDemand formulas solver (SourceCurrentSharedClassesNumeric.Reads.completed first last)

/-- The selected demand belongs to the given local classes continuation. -/
inductive LocalDemand (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {loaded : Allocated} → {inherited : EqValue} → {values results : List Node} →
    {before after : Checked width} → {fourth savedFourth : Fourth} → {memo saved : Memo} →
    {execution : SourceCurrentSharedLocalNumeric.Execution budget loaded inherited values before fourth memo
      results after savedFourth saved} → {memos final : Memos} →
    SourceCurrentSharedLocalNumeric.Reads formulas solver execution memos final → Prop where
  | classes {budget loaded inherited values before fourth memo records outcome results after savedFourth saved}
      (observed : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records))
      {continuation : SourceCurrentSharedClassesNumeric.Execution budget records values
        (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved}
      {memos final}
      (calls : SourceCurrentSharedClassesNumeric.Reads formulas solver continuation memos final)
      (selected : ClassDemand formulas solver calls) :
      LocalDemand formulas solver (SourceCurrentSharedLocalNumeric.Reads.classes (actual := observed) calls)

/-- The demand is captured by the same live Parent reads and constructor. -/
inductive ParentDemand (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (profile : SourceCurrentAllocatedNativeResourceForecast.Profile) (budget : Nat)
    (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List Node) (before : Caller width) (memos : Memos) :
    {result : Edge} → {after : Checked width} → {fourth : Fourth} → {memo : Memo} → {final : Memos} →
    SourceCurrentSharedParentNumeric.Reads formulas solver inventory profile budget symbol original loaded inherited
      values before memos result after fourth memo final → Prop where
  | live {children middle after fourth memo final result}
      (test : SourceEqualityMkEdgeAllocation.contradictory original = false)
      (lower : SourceCurrentSharedLocalNumeric.Receipt formulas solver inventory profile budget original loaded inherited
        values before memos children middle fourth memo final)
      (built : SourceCurrentAllocatedMkEdge.build symbol loaded children middle = (.ok result, after))
      (selected : LocalDemand formulas solver lower.reads) :
      ParentDemand formulas solver inventory profile budget symbol original loaded inherited values before memos
        (SourceCurrentSharedParentNumeric.Reads.live test lower built)

omit [DecidableEq Node] in
private theorem pass_graph
    {formulas solver records values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Pass (width := width) records values before memo results after saved}
    (_reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final) :
    SourceCurrentAllocatedClassPass.Pass records values before memo results after saved := actual

private theorem classes_annotation (lib : Library)
    {formulas solver inventory guard loaded inherited before own records memo budget values fourth}
    {outcome results after savedFourth saved memos final}
    {execution : SourceCurrentSharedClassesNumeric.Execution (width := width) budget records values
      (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved}
    (precheck : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (actual : SourceCurrentSharedClassesNumeric.Reads formulas solver execution memos final)
    (selected : ClassDemand formulas solver actual)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (types function argument : Expression) (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value) :
    AtFunction results := by
  cases selected with
  | completed first last included =>
      cases first with
      | prepared scan _requiredReads =>
          rename_i r read _ _ required _
          have prefixChecked : SourceSynthesisNativeTypeClosedRequests.Ready lib (prefixState before loaded inherited) :=
            ⟨precheck.ready.good, precheck.ready.semantic, ready.checked.scopes, ready.checked.idle,
              ⟨ready.checked.stored.constructors, ready.checked.stored.native⟩⟩
          have entry : Ready lib (initial (prefixState before loaded inherited) memo) :=
            SourceSynthesisNativeTypeSharedState.initial lib _ _ prefixChecked precheck.ready.costs
              ready.physicalMemo ready.typedMemo
          have sourcePaths := (SourceSynthesisGuardRegions.application_guard_endpoints types function argument
            sourceName guard sourceChildren occurrence).2
          have original := SourceSynthesisActualSelectedProgramFootprints.precheck_regions precheck
            SourceSynthesisGuardRegions.applicationRegion sourcePaths
          have inputSlots := fun index value found => And.intro (fields index value found) (typed index value found)
          have recordPaths := fun record member path included =>
            SourceSynthesisTypeRequiredRoutes.application_paths (Origin lib) (fun index => index = 2 ∨ index = 3)
              values (by decide) inputSlots path ((original record member).2 path included)
          obtain ⟨checked, costs, extension, _scanGuards, known⟩ :=
            SourceSynthesisNativeTypeSharedScan.scan lib scan entry.checked entry.costs available closed recordPaths guards
          have kept : SourceEqualityRequiredCache.Keeps _ _ :=
            ⟨checked.semantic.ready, extension.heap, extension.history⟩
          have scannedReady := SourceSynthesisNativeTypeSharedState.initial lib _ _ checked costs
            (entry.physicalMemo.grows kept) entry.typedMemo
          exact SourceSynthesisRequiredAnnotationPreparationPass.application lib types function argument sourceName sourceChildren
            occurrence precheck scan scannedReady known closed typed fields required (pass_graph last) included

private theorem local_annotation (lib : Library)
    {formulas solver entryInventory guard loaded inherited before memos}
    {budget values results after fourth memo final}
    {execution : SourceCurrentSharedLocalNumeric.Execution (width := width) budget loaded inherited values
      before.checked before.fourth before.merge results after fourth memo}
    (actual : SourceCurrentSharedLocalNumeric.Reads formulas solver execution memos final)
    (selected : LocalDemand formulas solver actual)
    (context : Context formulas solver entryInventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (cached : SourceEqualityGuardReadback.Cached guard.equalities)
    (found : SourceEqualityConstraintFieldLookup.load guard before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values) (closed : ClosedValues values)
    (types function argument : Expression) (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (typed : ∀ index value, values[index]? = some value → ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → (index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value) :
    AtFunction results := by
  cases selected with
  | classes observed calls selected =>
      obtain ⟨own, branch, precheck⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver entryInventory
        before.checked context.ready context.admitted guard cached loaded found inherited inheritedReady
      have same := Except.ok.inj (precheck.actual.symm.trans observed)
      cases branch with
      | unchanged => cases same
      | emptyChildren => cases same
      | classes records =>
          cases same
          exact classes_annotation lib precheck calls selected ready available closed guards
            types function argument sourceName sourceChildren occurrence typed fields

section Parent
variable (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {entryInventory inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {profile : SourceCurrentAllocatedNativeResourceForecast.Profile} {budget : Nat}
variable {before : Caller width} {memos final : Memos} {request : Request} {loaded : Allocated}
variable {result : Edge} {after : Checked width} {savedFourth : Fourth} {saved : Memo}
variable (numeric : SourceCurrentSharedParentNumeric.Receipt formulas solver inventory profile budget
  request.value.entry.key.symbol request.value.entry.key.constraint loaded request.inherited
  request.value.children before memos result after savedFourth saved final)
variable (selected : ParentDemand formulas solver inventory profile budget request.value.entry.key.symbol
  request.value.entry.key.constraint loaded request.inherited request.value.children before memos numeric.reads)
variable (context : Context formulas solver entryInventory before memos)
variable (ready : Ready lib (initial before.checked before.merge))
variable (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
variable (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
variable (resident : Resident before.checked.native.machine.heap request.value)
variable (closed : ClosedValues request.value.children)
variable (types function argument : Expression) (sourceName : String) (sourceChildren : List Expression)
variable (occurrence : application types function argument = .node [.mk sourceName request.value.entry.key.constraint sourceChildren])
variable (typed : ∀ index value, request.value.children[index]? = some value →
  ¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)

include numeric selected context ready guards inheritedReady resident closed occurrence typed in
/-- A branch-pinned selected Required descendant reaches the same physical Parent children. -/
theorem selected_annotation
    (fields : ∀ index value, request.value.children[index]? = some value →
      (index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value) : AtFunction result.children := by
  cases selected with
  | live test lower built demanded =>
      rename_i children middle
      have cached := (context.ready.good.fields request.value.entry.key request.value resident).1
      have found := numeric.field test
      have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
      have localShape := local_annotation lib lower.reads demanded context ready guards cached found inheritedReady
        available closed types function argument sourceName sourceChildren occurrence typed fields
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready request.value.entry.key.constraint
        before.checked.operations.constraints context.ready.good.operations.constraints cached loaded found
      have storedReady := loadedReady.1.grows lower.semantic.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (SourceEqualityConjoinAllocation.readback loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations request.value.entry.key.constraint
          from ⟨cached, loaded, found⟩).grows lower.semantic.effects.grows
      obtain ⟨chosen, reached, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver inventory
        request.value.entry.key.symbol loaded _ _ lower.semantic.ready lower.semantic.admitted
        storedReady field lower.semantic.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      cases Except.ok.inj same.1
      cases same.2
      rw [constructor.children]
      split
      · exact localShape
      · intro value found
        cases found

include numeric selected context ready guards inheritedReady resident closed occurrence typed in
/-- The same Parent receipt retains its full field packet and the ordinary function annotation. -/
theorem application_fields (literal : String → Symbol)
    (fields : ∀ index value, request.value.children[index]? = some value →
      (index = 2 ∨ index = 3) → ValueFields (Origin lib) literal value) :
    Ready lib (initial after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Coupled request.value result ∧
      (∀ index value, result.children[index]? = some value →
        ((index = 2 ∨ index = 3) → ValueFields (Origin lib) literal value) ∧
          (¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value)) ∧ AtFunction result.children := by
  obtain ⟨next, extension, present, resultClosed, finalGuards, coupled, slots⟩ :=
    SourceSynthesisNativeTypeSharedParentWorker.application_fields lib literal formulas solver numeric context ready guards
      inheritedReady resident closed types function argument sourceName sourceChildren occurrence typed fields
  exact ⟨next, extension, present, resultClosed, finalGuards, coupled, slots,
    selected_annotation lib formulas solver numeric selected context ready guards inheritedReady resident closed
      types function argument sourceName sourceChildren occurrence typed
      (fun index value found assigned => (fields index value found assigned).fields)⟩

end Parent
end MicroCFTA.SourceSynthesisRequiredAnnotationParentReturn
