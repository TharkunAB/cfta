import MicroCFTA.SourcePruningEnumerationNativeCheckedOriginArity
import MicroCFTA.SourceEqualityNativeDemandBodyYield

/-!
# Checked arity from every actual completed native edge body

The physical receipt fixes the actual first instruction and final state.
The first instruction derives its real ready check or sentinel branch.
The accepted branch retains the actual ordered raw child executions.
The sentinel branch retains its actual constructor and full returned state.
No source-language or future-child result premise is required.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeCheckedOriginArity
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open EnumerationState EnumerationCorrectness
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- An actual yielded body retains its exact native state and the constructor check that selected its code. -/
theorem body_choice_checked (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    after.native = before.native ∧
      (code = SourceEqualityNativeCheckedCode.sentinel request.left ∨
        ∃ first second combined,
          SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first) ∧
          SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second) ∧
          (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
            request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined) ∧
          code = SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  have same := SourceEqualityNativeDemandOperations.body_native request .pure before
  have unchanged : after.native = before.native := by
    simpa only [yielded, Outcome.state] using same
  refine ⟨unchanged, ?_⟩
  by_cases mismatch : request.left.children.length ≠ request.right.children.length
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left mismatch, sentinel, code_bind_pure] at yielded
    cases yielded
    exact .inl rfl
  · simp only [SourceEqualityNativeDemand.body, ite_eq_right mismatch] at yielded
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at yielded; cases yielded
    | ok first =>
        cases first with
        | none => simp only [firstLoaded] at yielded; cases yielded
        | some first =>
            simp only [firstLoaded] at yielded
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
            | error message => simp only [secondLoaded] at yielded; cases yielded
            | ok second =>
                cases second with
                | none => simp only [secondLoaded] at yielded; cases yielded
                | some second =>
                    simp only [secondLoaded] at yielded
                    cases checked : SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
                      request.left.children.length request.right.children.length before.operations with
                    | mk result operations =>
                        simp only [checked] at yielded
                        cases result with
                        | error message => cases yielded
                        | ok branch =>
                            cases branch with
                            | mismatch | rejected =>
                                simp only [sentinel, code_bind_pure] at yielded
                                cases yielded
                                exact .inl rfl
                            | ready combined =>
                                simp only [code_bind_pure] at yielded
                                cases yielded
                                exact .inr ⟨first, second, combined, firstLoaded, secondLoaded,
                                  congrArg Prod.fst checked, rfl⟩

private theorem trace_body_first [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before after : Checked width) (result : EdgeValue Symbol Guard)
    (count : Nat)
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace count
      (.edgeBody request .pure) before (.code (.pure result)) after) :
    ∃ code middle rest,
      SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) middle ∧
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace rest
        (.code code) middle (.code (.pure result)) after := by
  cases trace with
  | cons start state next current final reached size inputs one tail =>
      obtain ⟨code, same⟩ := SourceEqualityNativeDemandBodyYield.pure_yielded_code request before current next one
      subst next
      exact ⟨code, current, size, one, tail⟩

/-- A completed rich body receipt derives returned arity and the actual accepted or sentinel origin. -/
theorem body_receipt_fits [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before : Checked width)
    (initial : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (inputs : EdgeReady before.native.machine request)
    {count : Nat} {result : EdgeValue Symbol Guard} {after : Checked width}
    {post : Machine Symbol Guard → EdgeValue Symbol Guard → Prop}
    (receipt : SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt count
      (.edgeBody request .pure) before result after post) :
    SourcePruningEnumerationArityOrigins.Fits result.entry.key.constraint result.children.length ∧
      ((∃ first second combined values middle childCount,
          SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first) ∧
          SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second) ∧
          (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
            request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined) ∧
          childCount + 1 < count + 1 ∧
          SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode request.domain pair.1 pair.2)
            (request.left.children.zip request.right.children)
            {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
              request.left.children.length request.right.children.length before.operations).2} values middle childCount ∧
          result = (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values)
            middle.native.machine.heap).1 ∧
          after = {middle with native := advance middle.native {middle.native.machine with heap :=
            (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values)
              middle.native.machine.heap).2}} ∧
          result.children.length = request.left.children.length) ∨
        ∃ middle rest,
          SourceEqualityNativeDemand.body request .pure before = .yielded (.code (SourceEqualityNativeCheckedCode.sentinel request.left)) middle ∧
          middle.native = before.native ∧
          SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace rest
            (.code (SourceEqualityNativeCheckedCode.sentinel request.left)) middle (.code (.pure result)) after ∧
          result = (run (makeEdge request.left.entry.key.symbol top [.empty]) middle.native.machine.heap).1 ∧
          after = {middle with native := advance middle.native {middle.native.machine with heap :=
            (run (makeEdge request.left.entry.key.symbol top [.empty]) middle.native.machine.heap).2}} ∧
          result.entry.key.constraint = top ∧ result.children = [.empty]) := by
  obtain ⟨code, middle, rest, one, tail⟩ := trace_body_first request before after result count receipt.trace
  obtain ⟨nativeSame, selected⟩ := body_choice_checked request before middle code one
  rcases selected with sentinelSame | ⟨first, second, combined, left, right, accepted, _codeSame⟩
  · subst code
    have done := trace_done rest _ middle after result tail.steps
    have observed : execute (rest + 1)
        (.code (.work (makeEdge request.left.entry.key.symbol top [.empty]) .pure)) middle = .done result after := by
      simpa only [SourceEqualityNativeCheckedCode.sentinel] using done
    obtain ⟨resultSame, afterSame⟩ := SourceEqualityNativeDemandAcceptedReadback.work_observation
      (makeEdge request.left.entry.key.symbol top [.empty]) (rest + 1) middle after result observed
    have middleReady : SourceEqualityRequiredCache.Ready middle.native.machine.heap := by
      simpa only [nativeSame] using initial.heap
    obtain ⟨_keeps, _resident, _symbol, guardSame, childrenSame, _rejects⟩ :=
      SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance
        request.left.entry.key.symbol middle.native.machine.heap middleReady
    have resultGuard : result.entry.key.constraint = top := by rw [resultSame]; exact guardSame
    have resultChildren : result.children = [.empty] := by rw [resultSame]; exact childrenSame
    refine ⟨?_, .inr ⟨middle, rest, one, nativeSame, tail, resultSame, afterSame, resultGuard, resultChildren⟩⟩
    intro tries residual projected start
    rw [resultGuard] at projected
    have topProjection : SourcePruningEnumerationConstraint.project (top : Guard) = some ([], none) := rfl
    rw [topProjection] at projected
    have triesSame : [] = tries := congrArg Prod.fst (Option.some.inj projected)
    subst tries
    rfl
  · obtain ⟨values, reached, childCount, bounded, walk, resultSame, afterSame, lengthSame, fits⟩ :=
      accepted_receipt_fits request before first second combined initial inputs left right accepted receipt
    exact ⟨fits, .inl ⟨first, second, combined, values, reached, childCount,
      left, right, accepted, bounded, walk, resultSame, afterSame, lengthSame⟩⟩

end MicroCFTA.SourcePruningEnumerationNativeCheckedOriginArity
