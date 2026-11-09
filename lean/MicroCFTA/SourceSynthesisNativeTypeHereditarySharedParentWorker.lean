import MicroCFTA.SourceSynthesisNativeTypeSharedParentWorker
import MicroCFTA.SourceSynthesisNativeTypeAnnotatedSharedParentWorker
import MicroCFTA.SourceSynthesisHereditaryProgramFields

/-!
# Recursive Program fields at the actual shared Parent return

The given shared receipt retains its actual local reduction and constructor.
The source row fixes its full guard, layout and recursive input fields.
The same return retains that layout or has Top with one Empty child.
The constructor choice and returned fields remain coupled.

Initial caller and Type facts remain current premises. These laws do not
prove completion, failed-prefix safety or all reached classifications.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeHereditarySharedParentWorker
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library arrowMarker)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPrecheck (Receipt)
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
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory

private def Slots (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop) (values : List Node) : Prop :=
  ∀ index value, values[index]? = some value →
    (assigned index → ValueFields (Origin lib) literal value) ∧
      (¬ assigned index → Annotated (Origin lib) value)

private theorem application_slots (lib : Library) (literal : String → Symbol) (types marker function argument : Node)
    (typesTyped : Annotated (Origin lib) types) (markerTyped : Annotated (Origin lib) marker)
    (functionFields : ValueFields (Origin lib) literal function) (argumentFields : ValueFields (Origin lib) literal argument) :
    Slots lib literal (fun index => index = 2 ∨ index = 3) [types, marker, function, argument] := by
  intro index value found
  cases index with
  | zero => cases Option.some.inj found; exact ⟨by intro assigned; omega, fun _ => typesTyped⟩
  | succ index =>
      cases index with
      | zero => cases Option.some.inj found; exact ⟨by intro assigned; omega, fun _ => markerTyped⟩
      | succ index =>
          cases index with
          | zero => cases Option.some.inj found; exact ⟨fun _ => functionFields, by intro absent; exact False.elim (absent (Or.inl rfl))⟩
          | succ index =>
              cases index with
              | zero => cases Option.some.inj found; exact ⟨fun _ => argumentFields, by intro absent; exact False.elim (absent (Or.inr rfl))⟩
              | succ index => simp only [List.getElem?_cons_succ, List.getElem?_nil] at found; cases found

private theorem filter_slots (lib : Library) (literal : String → Symbol) (goal candidates : Node)
    (goalTyped : Annotated (Origin lib) goal) (candidateFields : ValueFields (Origin lib) literal candidates) :
    Slots lib literal (fun index => index = 1) [goal, candidates] := by
  intro index value found
  cases index with
  | zero => cases Option.some.inj found; exact ⟨by intro assigned; omega, fun _ => goalTyped⟩
  | succ index =>
      cases index with
      | zero => cases Option.some.inj found; exact ⟨fun _ => candidateFields, by intro absent; exact False.elim (absent rfl)⟩
      | succ index => simp only [List.getElem?_cons_succ, List.getElem?_nil] at found; cases found

private theorem application_fields (lib : Library) (literal : String → Symbol) (result : Edge)
    (symbol : result.entry.key.symbol = literal "app")
    (guard : result.entry.key.constraint = eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
    (count : result.children.length = 4) (slots : Slots lib literal (fun index => index = 2 ∨ index = 3) result.children) :
    EdgeFields (Origin lib) literal result := by
  generalize shape : result.children = children at count slots
  cases children with
  | nil => simp only [List.length_nil] at count; omega
  | cons types children =>
      cases children with
      | nil => simp only [List.length_cons, List.length_nil] at count; omega
      | cons marker children =>
          cases children with
          | nil => simp only [List.length_cons, List.length_nil] at count; omega
          | cons function children =>
              cases children with
              | nil => simp only [List.length_cons, List.length_nil] at count; omega
              | cons argument children =>
                  cases children with
                  | nil =>
                      exact .application result types marker function argument symbol guard shape
                        ((slots 0 types rfl).2 (by omega)) ((slots 1 marker rfl).2 (by omega))
                        ((slots 2 function rfl).1 (Or.inl rfl)) ((slots 3 argument rfl).1 (Or.inr rfl))
                  | cons extra rest => simp only [List.length_cons] at count; omega

private theorem filter_fields (lib : Library) (literal : String → Symbol) (result : Edge)
    (symbol : result.entry.key.symbol = literal "filter")
    (guard : result.entry.key.constraint = eqGuard [[[0], [1, 0]]])
    (count : result.children.length = 2) (slots : Slots lib literal (fun index => index = 1) result.children) :
    EdgeFields (Origin lib) literal result := by
  generalize shape : result.children = children at count slots
  cases children with
  | nil => simp only [List.length_nil] at count; omega
  | cons goal children =>
      cases children with
      | nil => simp only [List.length_cons, List.length_nil] at count; omega
      | cons candidates children =>
          cases children with
          | nil =>
              exact .filter result goal candidates symbol guard shape
                ((slots 0 goal rfl).2 (by omega)) ((slots 1 candidates rfl).1 rfl)
          | cons extra rest => simp only [List.length_cons] at count; omega

private theorem annotated_fields (lib : Library) (literal : String → Symbol) (result : Edge)
    (guard : result.entry.key.constraint = top) (count : result.children.length = 1)
    (typed : ∀ child ∈ result.children, Annotated (Origin lib) child) :
    EdgeFields (Origin lib) literal result := by
  generalize shape : result.children = children at count typed
  cases children with
  | nil => simp only [List.length_nil] at count; omega
  | cons annotation rest =>
      cases rest with
      | nil => exact .annotated result annotation guard shape (typed annotation List.mem_cons_self)
      | cons child tail => simp only [List.length_cons] at count; omega

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- The same shared Parent receipt retains every recursive Program field. -/
theorem receipt_fields (lib : Library) (literal : String → Symbol)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {entryInventory inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {profile : SourceCurrentAllocatedNativeResourceForecast.Profile} {budget : Nat}
    {before : Caller width} {memos final : Memos} {source result : Edge} {inherited : EqValue}
    {loaded : Allocated} {after : Checked width} {savedFourth : Fourth} {saved : Memo}
    (numeric : SourceCurrentSharedParentNumeric.Receipt formulas solver inventory profile budget
      source.entry.key.symbol source.entry.key.constraint loaded inherited source.children
      before memos result after savedFourth saved final)
    (context : Context formulas solver entryInventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (resident : Resident before.checked.native.machine.heap source)
    (closed : ClosedValues source.children) (fields : EdgeFields (Origin lib) literal source) :
    Ready lib (initial after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ EdgeFields (Origin lib) literal result := by
  cases fields with
  | annotated source annotation guard children typed =>
      have inputTypeRow : SourceSynthesisHereditaryMemoFields.TypeRow lib source := by
        refine ⟨?_, ?_⟩
        · rw [guard]
          exact SourceSynthesisNativeTypeTrace.origin_top lib
        · rw [children]
          intro child member
          cases List.mem_singleton.mp member
          exact typed
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards, resultTypeRow, coupled⟩ :=
        SourceSynthesisNativeTypeAnnotatedSharedParentWorker.receipt_fields lib formulas solver
          (request := ⟨inherited, source⟩) numeric context ready guards inheritedReady resident closed inputTypeRow
      refine ⟨nextReady, extension, present, resultClosed, afterGuards, ?_⟩
      rcases coupled.2 with retained | sentinel
      · apply annotated_fields lib literal result (retained.1.trans guard)
        · simpa only [children, List.length_cons, List.length_nil] using retained.2
        · exact resultTypeRow.2
      · exact .annotated result .empty sentinel.1 sentinel.2 .empty
  | application source types marker function argument symbol guard children typesTyped markerTyped functionFields argumentFields =>
      have inputs : Slots lib literal (fun index => index = 2 ∨ index = 3) source.children := by
        rw [children]
        exact application_slots lib literal types marker function argument typesTyped markerTyped functionFields argumentFields
      have occurrence : application .empty .empty .empty = .node [.mk "app" source.entry.key.constraint
          [.empty, arrowMarker top, .empty, .empty]] := by rw [guard]; rfl
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards, coupled, slots⟩ :=
        SourceSynthesisNativeTypeSharedParentWorker.application_fields lib literal formulas solver
          (request := ⟨inherited, source⟩) numeric context ready guards inheritedReady resident closed
          (types := .empty) (function := .empty) (argument := .empty) (sourceName := "app")
          (sourceChildren := [.empty, arrowMarker top, .empty, .empty]) (occurrence := occurrence)
          (typed := fun index value found assigned => (inputs index value found).2 assigned)
          (fields := fun index value found assigned => (inputs index value found).1 assigned)
      refine ⟨nextReady, extension, present, resultClosed, afterGuards, ?_⟩
      rcases coupled with ⟨own, retained | sentinel⟩
      · apply application_fields lib literal result (own.trans symbol) (retained.1.trans guard)
        · simpa only [children, List.length_cons, List.length_nil] using retained.2
        · exact slots
      · exact .annotated result .empty sentinel.1 sentinel.2 .empty
  | filter source goal candidates symbol guard children goalTyped candidateFields =>
      have inputs : Slots lib literal (fun index => index = 1) source.children := by
        rw [children]
        exact filter_slots lib literal goal candidates goalTyped candidateFields
      have occurrence : ofType .empty .empty = .node [.mk "filter" source.entry.key.constraint [.empty, .empty]] := by
        rw [guard]
        rfl
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards, coupled, slots⟩ :=
        SourceSynthesisNativeTypeSharedParentWorker.filter_fields lib literal formulas solver
          (request := ⟨inherited, source⟩) numeric context ready guards inheritedReady resident closed
          (candidates := .empty) (goal := .empty) (sourceName := "filter") (sourceChildren := [.empty, .empty])
          (occurrence := occurrence)
          (typed := fun index value found assigned => (inputs index value found).2 assigned)
          (fields := fun index value found assigned => (inputs index value found).1 assigned)
      refine ⟨nextReady, extension, present, resultClosed, afterGuards, ?_⟩
      rcases coupled with ⟨own, retained | sentinel⟩
      · apply filter_fields lib literal result (own.trans symbol) (retained.1.trans guard)
        · simpa only [children, List.length_cons, List.length_nil] using retained.2
        · exact slots
      · exact .annotated result .empty sentinel.1 sentinel.2 .empty

end MicroCFTA.SourceSynthesisNativeTypeHereditarySharedParentWorker
