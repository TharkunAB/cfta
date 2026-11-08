import MicroCFTA.SourceSynthesisNativeTypeHereditaryLocalWorker
import MicroCFTA.SourceSynthesisNativeTypeParentWorker
import MicroCFTA.SourceSynthesisNativeTypeParentAnnotatedWorker
import MicroCFTA.SourceSynthesisLocalReduceProgramRoles

/-!
# Recursive Program fields at the actual Parent return

The complete input row fixes its source guard, layout and recursive fields.
The same stored-field load and precheck select the actual local branch.
The constructor retains that layout or returns Top with one Empty child.
Both cases retain the full recursive field certificate.

The existing caller supplies physical facts and reached range plans.
The successful execution supplies its own graph, reads and postcondition.
These laws do not prove completion, failed-prefix safety, or all reached
classifications.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeHereditaryParentWorker
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

private theorem erased_slots (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop) (values : List Node) :
    Slots lib literal assigned (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  intro index value found
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? found)
  exact ⟨fun _ => .empty, fun _ => .empty⟩

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

variable {width : Nat}

private theorem bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {result : B} {after : Checked width} {fourth : Fourth} {memo : Memo}
    (actual : first.bind next = .done result after fourth memo) :
    ∃ value middle saved warm, first = .done value middle saved warm ∧ next value middle saved warm = .done result after fourth memo := by
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
  | done value checked completed current => simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at actual; cases actual; rfl

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem build_return {symbol loaded children before fourth memo result after saved warm}
    (actual : SourceCurrentAllocatedParentWorker.build (width := width) symbol loaded children before fourth memo =
      .done result after saved warm) :
    SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result, after) := by
  cases observed : SourceCurrentAllocatedMkEdge.build symbol loaded children before with
  | mk built checked =>
      cases built with
      | error => simp only [SourceCurrentAllocatedParentWorker.build, observed] at actual; cases actual
      | ok value => simp only [SourceCurrentAllocatedParentWorker.build, observed] at actual; cases actual; rfl

section CallerProofs
variable (lib : Library) (literal : String → Symbol)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {before : Caller width} {memos : Memos}
variable {source result : Edge} {inherited : EqValue} {g s r e p h m c n budget : Nat}
variable {after : Checked width} {savedFourth : Fourth} {saved : Memo}
variable (context : Context formulas solver inventory before memos)
variable (ready : Ready lib (initial before.checked before.merge))
variable (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
variable (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
variable (resident : Resident before.checked.native.machine.heap source)
variable (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget ⟨inherited, source⟩ before)
variable (closed : ClosedValues source.children)

include context inheritedReady in
private theorem local_slots (assigned : Nat → Prop) {loaded : Allocated} {children : List Node}
    {middle : Checked width} {fourth : Fourth} {memo : Memo}
    (cached : SourceEqualityGuardReadback.Cached source.entry.key.constraint.equalities)
    (found : SourceEqualityConstraintFieldLookup.load source.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
    (inputs : Slots lib literal assigned source.children)
    (classes : ∀ own records, Receipt formulas solver inventory source.entry.key.constraint loaded inherited before.checked own (.classes records) →
      Slots lib literal assigned children)
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited source.children
      before.checked before.fourth before.merge = .done children middle fourth memo) : Slots lib literal assigned children := by
  obtain ⟨own, branch, receipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before.checked context.ready context.admitted source.entry.key.constraint cached loaded found inherited inheritedReady
  cases branch with
  | classes records => exact classes own records receipt
  | unchanged => simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual] at actual; cases actual; exact inputs
  | emptyChildren => simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual] at actual; cases actual; exact erased_slots lib literal assigned _

include context inheritedReady resident ranges in
private theorem parent_fields (assigned : Nat → Prop)
    (inputs : Slots lib literal assigned source.children)
    (rebuild : ∀ output : Edge, output.entry.key.symbol = source.entry.key.symbol →
      output.entry.key.constraint = source.entry.key.constraint → output.children.length = source.children.length →
      Slots lib literal assigned output.children → EdgeFields (Origin lib) literal output)
    (classes : ∀ (loaded : Allocated) children middle fourth memo,
      SourceEqualityGuardReadback.Cached source.entry.key.constraint.equalities →
      SourceEqualityConstraintFieldLookup.load source.entry.key.constraint before.checked.operations.constraints = .ok (some loaded) →
      contradictory source.entry.key.constraint = false →
      ∀ own records, Receipt formulas solver inventory source.entry.key.constraint loaded inherited before.checked own (.classes records) →
      SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited source.children
        before.checked before.fourth before.merge = .done children middle fourth memo → Slots lib literal assigned children)
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget source.entry.key.symbol
      source.entry.key.constraint inherited source.children before.checked before.fourth before.merge = .done result after savedFourth saved) :
    EdgeFields (Origin lib) literal result := by
  cases rejected : contradictory source.entry.key.constraint with
  | true =>
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, ite_true] at actual
      cases actual
      have receipt := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory source.entry.key.symbol
        before.checked context.ready context.admitted
      exact .annotated _ .empty receipt.guard receipt.children .empty
  | false =>
      obtain ⟨cached, loaded, found⟩ := context.ready.good.fields source.entry.key source resident
      have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ source resident
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, Bool.false_eq_true, ite_false, found] at actual
      obtain ⟨children, middle, fourth, memo, reduced, built⟩ := bind_done _ _ actual
      have reduced := reduce_return reduced
      have built := build_return built
      have slots := local_slots lib literal formulas solver context inheritedReady assigned cached found inputs
        (fun own records receipt => classes loaded children middle fourth memo cached found rejected own records receipt reduced) reduced
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready source.entry.key.constraint
        before.checked.operations.constraints context.ready.good.operations.constraints cached loaded found
      obtain ⟨next, final, _graph, _reads, localReceipt⟩ := SourceCurrentAllocatedLocalWorkerActual.sound formulas solver
        context cached found inheritedReady available (ranges rejected loaded found) reduced
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (SourceEqualityConjoinAllocation.readback loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations source.entry.key.constraint
          from ⟨cached, loaded, found⟩).grows localReceipt.effects.grows
      obtain ⟨chosen, reached, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next
        source.entry.key.symbol loaded children middle localReceipt.ready localReceipt.admitted
        (loadedReady.1.grows localReceipt.effects.grows.constraint_growth) field localReceipt.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      cases Except.ok.inj same.1
      cases same.2
      cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
      | true =>
          have childrenEq : result.children = children := by simpa only [keep, ite_true] using constructor.children
          apply rebuild result constructor.symbol
          · exact (show result.entry.key.constraint = SourceEqualityConjoinAllocation.readback loaded from by
              simpa only [keep, ite_true] using constructor.guard).trans loadedReady.2
          · exact (congrArg List.length childrenEq).trans (SourceSynthesisLocalReduceProgramRoles.reduce_length reduced)
          · rw [childrenEq]; exact slots
      | false =>
          exact .annotated result .empty
            (by simpa only [keep, Bool.false_eq_true, ite_false, SourceEqualityConstraintConstructors.top,
              SourceSynthesisGeneralizeSyntax.top] using constructor.guard)
            (by simpa only [keep, Bool.false_eq_true, ite_false] using constructor.children) .empty

include context ready guards inheritedReady resident ranges closed in
/-- The same actual Parent execution retains every recursive Program field and its full caller postcondition. -/
theorem edge
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget source.entry.key.symbol
      source.entry.key.constraint inherited source.children before.checked before.fourth before.merge = .done result after savedFourth saved)
    (fields : EdgeFields (Origin lib) literal source) :
    ∃ next final, ∃ body : SourceCurrentAllocatedPartialGraph.EdgeBody budget ⟨inherited, source⟩ before result
        (SourceCurrentAllocatedPartialState.advance before after savedFourth saved),
      SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver body memos final ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next ⟨inherited, source⟩ before result
        (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
      Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
      Ready lib (initial after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧ GuardHeap (Origin lib) after.native.machine.heap ∧
      EdgeFields (Origin lib) literal result := by
  cases fields with
  | annotated source annotation guard children typed =>
      obtain ⟨next, final, body, reads, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.resident_verified
        formulas solver context inheritedReady resident ranges actual
      obtain ⟨nextReady, extension, present, resultClosed, afterGuards, _symbol, resultGuard, shape, _typed⟩ :=
        SourceSynthesisNativeTypeParentAnnotatedWorker.annotated lib formulas solver actual context ready guards
          inheritedReady resident guard children typed (closed annotation (by rw [children]; exact List.mem_cons_self))
      refine ⟨next, final, body, reads, receipt, post, nextReady, extension, present, resultClosed, afterGuards, ?_⟩
      rcases shape with original | empty
      · exact .annotated result annotation resultGuard original typed
      · exact .annotated result .empty resultGuard empty .empty
  | application source types marker function argument symbol guard children typesTyped markerTyped functionFields argumentFields =>
      have inputs : Slots lib literal (fun index => index = 2 ∨ index = 3) source.children := by
        rw [children]; exact application_slots lib literal types marker function argument typesTyped markerTyped functionFields argumentFields
      have occurrence : application .empty .empty .empty = .node [.mk "app" source.entry.key.constraint
          [.empty, arrowMarker top, .empty, .empty]] := by rw [guard]; rfl
      obtain ⟨next, final, body, reads, receipt, post, nextReady, extension, present, resultClosed, afterGuards, _coupled, _slots⟩ :=
        SourceSynthesisNativeTypeParentWorker.application (lib := lib) (formulas := formulas) (solver := solver)
          (request := ⟨inherited, source⟩)
          (context := context) (ready := ready) (guards := guards) (inheritedReady := inheritedReady) (resident := resident)
          (ranges := ranges) (closed := closed) (types := .empty) (function := .empty) (argument := .empty)
          (sourceName := "app") (sourceChildren := [.empty, arrowMarker top, .empty, .empty]) (occurrence := occurrence)
          (typed := fun index value found assigned => (inputs index value found).2 assigned)
          (fields := fun index value found assigned => ((inputs index value found).1 assigned).fields) actual
      refine ⟨next, final, body, reads, receipt, post, nextReady, extension, present, resultClosed, afterGuards, ?_⟩
      apply parent_fields lib literal formulas solver context inheritedReady resident ranges
        (fun index => index = 2 ∨ index = 3) inputs ?_ ?_ actual
      · intro output own constraint count slots
        apply application_fields lib literal output (own.trans symbol) (constraint.trans guard)
        · simpa only [children, List.length_cons, List.length_nil] using count
        · exact slots
      · intro loaded values middle fourth memo _cached _found live own records branch observed
        exact (SourceSynthesisNativeTypeHereditaryLocalWorker.application_reduce
          (lib := lib) (literal := literal) (formulas := formulas) (solver := solver) (receipt := branch)
          (ready := ready) (available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ source resident)
          (closed := closed) (guards := guards) (ranges := ranges live loaded _found records branch.actual)
          (types := .empty) (function := .empty) (argument := .empty) (sourceName := "app")
          (sourceChildren := [.empty, arrowMarker top, .empty, .empty]) (occurrence := occurrence)
          (typed := fun index value found assigned => (inputs index value found).2 assigned)
          (fields := fun index value found assigned => (inputs index value found).1 assigned) observed).2.2.2.2.2.2
  | filter source goal candidates symbol guard children goalTyped candidateFields =>
      have inputs : Slots lib literal (fun index => index = 1) source.children := by
        rw [children]; exact filter_slots lib literal goal candidates goalTyped candidateFields
      have occurrence : ofType .empty .empty = .node [.mk "filter" source.entry.key.constraint [.empty, .empty]] := by rw [guard]; rfl
      obtain ⟨next, final, body, reads, receipt, post, nextReady, extension, present, resultClosed, afterGuards, _coupled, _slots⟩ :=
        SourceSynthesisNativeTypeParentWorker.filter (lib := lib) (formulas := formulas) (solver := solver)
          (request := ⟨inherited, source⟩)
          (context := context) (ready := ready) (guards := guards) (inheritedReady := inheritedReady) (resident := resident)
          (ranges := ranges) (closed := closed) (candidates := .empty) (goal := .empty)
          (sourceName := "filter") (sourceChildren := [.empty, .empty]) (occurrence := occurrence)
          (typed := fun index value found assigned => (inputs index value found).2 assigned)
          (fields := fun index value found assigned => ((inputs index value found).1 assigned).fields) actual
      refine ⟨next, final, body, reads, receipt, post, nextReady, extension, present, resultClosed, afterGuards, ?_⟩
      apply parent_fields lib literal formulas solver context inheritedReady resident ranges (fun index => index = 1) inputs ?_ ?_ actual
      · intro output own constraint count slots
        apply filter_fields lib literal output (own.trans symbol) (constraint.trans guard)
        · simpa only [children, List.length_cons, List.length_nil] using count
        · exact slots
      · intro loaded values middle fourth memo _cached _found live own records branch observed
        exact (SourceSynthesisNativeTypeHereditaryLocalWorker.filter_reduce
          (lib := lib) (literal := literal) (formulas := formulas) (solver := solver) (receipt := branch)
          (ready := ready) (available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ source resident)
          (closed := closed) (guards := guards) (ranges := ranges live loaded _found records branch.actual)
          (candidates := .empty) (goal := .empty) (sourceName := "filter") (sourceChildren := [.empty, .empty]) (occurrence := occurrence)
          (typed := fun index value found assigned => (inputs index value found).2 assigned)
          (fields := fun index value found assigned => (inputs index value found).1 assigned) observed).2.2.2.2.2.2
end CallerProofs
end MicroCFTA.SourceSynthesisNativeTypeHereditaryParentWorker
