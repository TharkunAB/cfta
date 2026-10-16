import MicroCFTA.SourceEqualityNativeDemandBodyYield

namespace MicroCFTA.BodyYieldKernels

open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand SourceEqualityNativeDemandBodyYield
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
variable {width : Nat}

/-- Actual mismatch emits the same sentinel source code before and after appending a continuation. -/
theorem mismatch_code (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Unit) (before : State width)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    let after := {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}
    ∃ code, body request .pure before = .yielded (.code code) after ∧
      body request next before = .yielded (.code (code.bind next)) after ∧
      after.native = before.native := by
  dsimp only
  have one : body request next before =
      .yielded (.code ((SourceEqualityNativeCheckedCode.sentinel request.left).bind next))
      {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations} := by
    rw [body_mismatch request next before mismatch]
    rfl
  obtain ⟨code, pure, same⟩ := yielded_unbind request next before _ _ one
  exact ⟨code, pure, by simpa only [same] using one, rfl⟩

/-- Actual field loads and accepted conjunction emit the same checked child code at the same operation state. -/
theorem accepted_code (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Unit) (before : State width)
    (first second combined : Allocated)
    (arity : request.left.children.length = request.right.children.length)
    (firstFound : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first))
    (secondFound : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined)) :
    let after := {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations).2}
    ∃ code, body request .pure before = .yielded (.code code) after ∧
      body request next before = .yielded (.code (code.bind next)) after ∧
      after.native = before.native := by
  dsimp only
  have matched : ¬request.left.children.length ≠ request.right.children.length := by omega
  have one : body request next before =
      .yielded (.code ((SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined).bind next))
      {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length before.operations).2} := by
    simp only [body, if_neg matched, firstFound, secondFound, accepted]
  obtain ⟨code, pure, same⟩ := yielded_unbind request next before _ _ one
  exact ⟨code, pure, by simpa only [same] using one, rfl⟩

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms mismatch_code
#check @mismatch_code
#print axioms accepted_code
#check @accepted_code

end MicroCFTA.BodyYieldKernels
