import MicroCFTA.SourceEqualityNativeDemandPrefixSplit

namespace MicroCFTA.CheckedPrefixSplitIndependentKernels

open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A checked mismatch yields the sentinel prefix before the appended continuation can run. -/
theorem pending_checked_edge_body (request : EdgeRequest Symbol Guard) (before : Checked width)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Unit) :
    let inner : Control (EdgeValue Symbol Guard) := .edgeBody request .pure
    let remaining : Control Unit := (.code (SourceEqualityNativeCheckedCode.sentinel request.left)).bind next
    let after := {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}
    ∃ pending, Steps 1 inner before pending after ∧
      (∀ value, pending ≠ .code (.pure value)) ∧ remaining = pending.bind next ∧
      after.native = before.native := by
  dsimp only
  have one : SourceEqualityNativeDemand.step (.edgeBody request Code.pure) before =
      .yielded (.code (SourceEqualityNativeCheckedCode.sentinel request.left))
        {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations} := by
    simp only [SourceEqualityNativeDemand.step]
    rw [body_mismatch request Code.pure before mismatch]
    simp only [sentinel, code_bind_pure]
  have innerTrace : Steps 1 (.edgeBody request Code.pure) before
      (.code (SourceEqualityNativeCheckedCode.sentinel request.left))
      {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations} :=
    .cons _ _ _ _ _ _ 0 one (.refl _ _)
  have boundTrace := innerTrace.bind 1 _ _ _ _ next
  rcases steps_bind_cases 1 (.edgeBody request Code.pure) next _ _ _ boundTrace with
      ⟨pending, trace, nonpure, same⟩ | ⟨inner, outer, value, middle, count, trace, tail⟩
  · exact ⟨pending, trace, nonpure, same, rfl⟩
  · have atLeastTwo : 2 ≤ inner := by
      cases trace with
      | cons control state rest current final result fuel first later =>
        obtain ⟨same, retained⟩ := Outcome.yielded.inj (first.symm.trans one)
        subst rest
        subst current
        cases later with
        | cons => omega
    omega

private def worked (job : Work Symbol Guard Unit) (before : Checked width) : Checked width :=
  {before with native := advance before.native {before.native.machine with heap :=
    (InternedConstructorTemplates.run job before.native.machine.heap).2}}

/-- The split detects a returned inner Work when the outer read has run and outer Work remains pending. -/
theorem crossed_return_pending_outer (before : Checked width) (job outerJob : Work Symbol Guard Unit) :
    let inner : Control Nat := .code (.work job (fun _ => .pure 7))
    let next : Nat → Code Symbol Guard Unit := fun name => .read name (fun _ => .work outerJob .pure)
    let after := worked job before
    let remaining : Control Unit := .code (.work outerJob .pure)
    (∃ innerCount outerCount value middle, innerCount + outerCount = 2 ∧
      Steps innerCount inner before (.code (.pure value)) middle ∧
      Steps outerCount (.code (next value)) middle remaining after) ∧
      after.operations = before.operations ∧ after.native.nodes = before.native.nodes ∧
      after.native.edges = before.native.edges := by
  dsimp only
  let inner : Control Nat := .code (.work job (fun _ => .pure 7))
  let next : Nat → Code Symbol Guard Unit := fun name => .read name (fun _ => .work outerJob .pure)
  have one : SourceEqualityNativeDemand.step inner before =
      .yielded (.code (.pure 7)) (worked job before) := rfl
  have complete : Steps 1 inner before (.code (.pure 7)) (worked job before) :=
    .cons _ _ _ _ _ _ 0 one (.refl _ _)
  have firstBound : SourceEqualityNativeDemand.step (inner.bind next) before =
      .yielded (.code (next 7)) (worked job before) := rfl
  have read : SourceEqualityNativeDemand.step (.code (next 7)) (worked job before) =
      .yielded (.code (.work outerJob Code.pure)) (worked job before) := rfl
  have actual : Steps 2 (inner.bind next) before (.code (.work outerJob Code.pure)) (worked job before) :=
    .cons _ _ _ _ _ _ 1 firstBound (.cons _ _ _ _ _ _ 0 read (.refl _ _))
  refine ⟨?_, rfl, rfl, rfl⟩
  rcases steps_bind_cases 2 inner next _ _ _ actual with
      ⟨pending, trace, nonpure, same⟩ | crossed
  · have impossible := complete.length_le_complete trace
    omega
  · exact crossed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms pending_checked_edge_body
#check @pending_checked_edge_body
#print axioms crossed_return_pending_outer
#check @crossed_return_pending_outer

end MicroCFTA.CheckedPrefixSplitIndependentKernels
