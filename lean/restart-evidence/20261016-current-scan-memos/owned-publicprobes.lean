import MicroCFTA.SourceCurrentAllocatedNativeGlobalMemos
import MicroCFTA.SourceCurrentAllocatedSeededMemos

open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded)
open SourceCurrentAllocatedSeededMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

#print axioms SourceCurrentAllocatedNativeGlobalMemos.step_receipt
#print axioms SourceCurrentAllocatedNativeGlobalMemos.trace_receipt
#print axioms SourceCurrentAllocatedNativeGlobalMemos.trace_memos
#print axioms operand_memos
#print axioms fold_memos
#print axioms seeded_memos
#check @SourceCurrentAllocatedNativeGlobalMemos.step_receipt
#check @SourceCurrentAllocatedNativeGlobalMemos.trace_receipt
#check @SourceCurrentAllocatedNativeGlobalMemos.trace_memos
#check @operand_memos
#check @fold_memos
#check @seeded_memos

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def symbol : Symbol := ("a", .top)
private def job : Work Symbol Guard (EdgeValue Symbol Guard) := makeEdge symbol top []
private def result (before : Checked 8) := (run job before.native.machine.heap).1
private def after (before : Checked 8) : Checked 8 :=
  ⟨advance before.native {before.native.machine with heap := (run job before.native.machine.heap).2}, before.operations⟩
private def workControl : Control (EdgeValue Symbol Guard) := .code (.work job .pure)
private theorem actual (before : Checked 8) : step workControl before = .yielded (.code (.pure (result before))) (after before) := rfl
private theorem trace (before : Checked 8) : Trace 1 workControl before (.code (.pure (result before))) (after before) := by
  refine .cons _ _ _ _ _ _ _ ?_ (actual before) (.refl _ _)
  exact .edge symbol top [] (by intro value member; cases member)

example : (SourceConstructorGlobalUnfold.work job empty).2.length = 1 := by cbv

example (before : Checked 8) : step workControl before = .yielded (.code (.pure (result before))) (after before) := actual before

example (before : Checked 8) (memos : Memos) :
    ∃ events, SourceGlobalUnfold.Runs ⟨before.native.machine.heap, memos.unfolding⟩
      ⟨(after before).native.machine.heap, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events :=
  SourceCurrentAllocatedNativeGlobalMemos.trace_receipt (trace before) memos.unfolding

example : ¬SourceGlobalUnfold.NoGlobal
    [(SourceGlobalUnfold.Event.globalUnfold (Value.empty : Value Symbol Guard).referenceOf : SourceGlobalUnfold.Event Symbol Guard)] := by
  intro quiet
  have impossible := quiet _ List.mem_cons_self
  cases impossible

private def external : Value Symbol Guard := .reference (.uninterned 999)
private def forest : List (Value Symbol Guard) := [.empty, external]
private def projected (before : Checked 8) : Checked 8 :=
  SourceCurrentAllocatedQueryMemo.advancePhysical before ⟨before.native.machine.heap, before.operations⟩
private theorem selectedProjection (before : Checked 8) : SourceEqualityProjectionGraph.Forest [0] forest
    before.native.machine.heap .empty before.native.machine.heap := .selected rfl .root
private theorem projectedTrace (before : Checked 8) : Operand [0] forest before .empty (projected before) :=
  .force .empty before.native.machine.heap (selectedProjection before)
private theorem projectedRead (before : Checked 8) (memos : Memos) : OperandReads (projectedTrace before) memos memos :=
  .force (projection := selectedProjection before) ⟨.selected (found := rfl) .root, rfl⟩

example (before : Checked 8) (memos : Memos) : OperandReads (projectedTrace before) memos memos :=
  projectedRead before memos

example (before : Checked 8) (memos : Memos) : FoldReads (.one (projectedTrace before)) memos memos :=
  .one (operand := projectedTrace before) (projectedRead before memos)

example (before : Checked 8) (memos : Memos) :
    SeededReads (.nonempty (rest := []) (seed := [0]) (.one (projectedTrace before))) memos memos :=
  .nonempty (actual := .one (projectedTrace before)) (.one (operand := projectedTrace before) (projectedRead before memos))

example (before : Checked 8) (memos : Memos) :
    SeededReads (Seeded.nil (values := forest) before) memos memos := .nil

example (before : Checked 8) (memos : Memos) : NativeReads (trace before) memos memos := by
  obtain ⟨events, runs, quiet⟩ := SourceCurrentAllocatedNativeGlobalMemos.trace_receipt (trace before) memos.unfolding
  exact .silent events runs quiet
