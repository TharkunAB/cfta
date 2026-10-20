import MicroCFTA.SourceCurrentNativeWalkOptionalPrefix

/-!
# Actual checked edge-body prefixes select original child requests

A prefix to an optional instruction must pass the actual ready branch.
The resulting cut retains both loaded fields and the exact operation state.
The selected node request comes from the original ordered child zip.
-/
namespace MicroCFTA.SourceCurrentNativeEdgeOptionalPrefix
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionKernel
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem work_optional_false (job : Work Symbol Guard Edge)
    {fuel : Nat} {before after : Checked width} {pair : Nat × Nat} {siteBody : Node}
    {siteNext : Node → Code Symbol Guard Edge}
    (actual : Trace fuel (.code (.work job .pure)) before (.code (.optionalBinder pair siteBody siteNext)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one tail =>
      cases one
      cases tail with
      | cons _ _ _ _ _ _ _ _ one _ => cases one

/-- An actual checked edge-body optional prefix retains its accepted allocation and exact child cut. -/
theorem edge_body (request : EdgeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Edge)
    (actual : Trace fuel (.edgeBody request .pure) before (.code (.optionalBinder pair siteBody siteNext)) after) :
    ∃ first second combined operations index child values entry walkFuel childFuel innerNext,
      let middle : Checked width := {before with operations := operations}
      let call := fun child : Node × Node => requestNode request.domain child.1 child.2
      let finish := fun values => Code.work
        (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure
      let callNext := fun value => (walk call ((request.left.children.zip request.right.children).drop (index + 1))).bind
        (fun tail => finish (values ++ value :: tail))
      request.left.children.length = request.right.children.length ∧
      SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first) ∧
      SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second) ∧
      SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length before.operations = (.ok (.ready combined), operations) ∧
      step (.edgeBody request .pure) before =
        .yielded (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)) middle ∧
      (request.left.children.zip request.right.children)[index]? = some child ∧
      Walk call ((request.left.children.zip request.right.children).take index) middle values entry walkFuel ∧
      (walkFuel + 1) + childFuel = fuel ∧
      Trace (walkFuel + 1) (.edgeBody request .pure) before ((.code (call child) : Control Node).bind callNext) entry ∧
      Trace childFuel (.code (call child)) entry (.code (.optionalBinder pair siteBody innerNext)) after ∧
      siteNext = fun value => (innerNext value).bind callNext := by
  cases actual with
  | cons start initial next current final result count inputs actualStep tail =>
      have bodyStep := actualStep
      change SourceEqualityNativeDemand.body request .pure before = .yielded next current at actualStep
      by_cases arity : request.left.children.length = request.right.children.length
      · have matched : ¬request.left.children.length ≠ request.right.children.length := by omega
        simp only [SourceEqualityNativeDemand.body, ite_eq_right matched] at actualStep
        cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
        | error message => simp only [firstLoaded] at actualStep; cases actualStep
        | ok firstValue =>
          cases firstValue with
          | none => simp only [firstLoaded] at actualStep; cases actualStep
          | some first =>
            simp only [firstLoaded] at actualStep
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
            | error message => simp only [secondLoaded] at actualStep; cases actualStep
            | ok secondValue =>
              cases secondValue with
              | none => simp only [secondLoaded] at actualStep; cases actualStep
              | some second =>
                simp only [secondLoaded] at actualStep
                cases checked : SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
                    request.left.children.length request.right.children.length before.operations with
                | mk outcome operations =>
                  rw [checked] at actualStep
                  cases outcome with
                  | error message => cases actualStep
                  | ok branch =>
                    cases branch with
                    | mismatch | rejected =>
                        simp only [sentinel, SourceEqualityNativeCheckedCode.sentinel, Code.bind] at actualStep
                        cases actualStep
                        exact False.elim (work_optional_false _ tail)
                    | ready combined =>
                        cases actualStep
                        simp only [code_bind_pure] at bodyStep tail
                        let call := fun child : Node × Node => requestNode request.domain child.1 child.2
                        let finish := fun values => Code.work
                          (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure
                        have walked : Trace count
                            ((.code (walk call (request.left.children.zip request.right.children)) : Control (List Node)).bind finish)
                            {before with operations := operations} (.code (.optionalBinder pair siteBody siteNext)) after := tail
                        rcases SourceCurrentNativeWalkOptionalPrefix.cut call (request.left.children.zip request.right.children)
                            finish count {before with operations := operations} after pair siteBody siteNext walked with
                          ⟨walkFuel, outerFuel, outputs, middle, total, earlier, later⟩ |
                          ⟨index, child, values, entry, walkFuel, childFuel, innerNext,
                            selected, earlier, total, prefixTrace, called, same⟩
                        · exact False.elim (work_optional_false _ later)
                        · refine ⟨first, second, combined, operations, index, child, values, entry, walkFuel, childFuel,
                            innerNext, arity, rfl, rfl, checked, bodyStep, selected, earlier, by omega, ?_, called, same⟩
                          exact .cons _ _ _ _ _ _ _ inputs bodyStep prefixTrace
      · have mismatch : request.left.children.length ≠ request.right.children.length := arity
        simp only [SourceEqualityNativeDemand.body, ite_eq_left mismatch, sentinel, SourceEqualityNativeCheckedCode.sentinel, Code.bind] at actualStep
        cases actualStep
        exact False.elim (work_optional_false _ tail)

end MicroCFTA.SourceCurrentNativeEdgeOptionalPrefix

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentNativeEdgeOptionalPrefix.edge_body
#print MicroCFTA.SourceCurrentNativeEdgeOptionalPrefix.edge_body
#print axioms MicroCFTA.SourceCurrentNativeEdgeOptionalPrefix.edge_body
