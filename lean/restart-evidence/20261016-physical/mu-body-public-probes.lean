import MicroCFTA.SourceCurrentAllocatedNativeMuBodyMeaning

open MicroCFTA
#print axioms SourceCurrentAllocatedNativeMuBodyMeaning.mu_body
#check SourceCurrentAllocatedNativeMuBodyMeaning.mu_body

namespace MicroCFTA.MuBodyPhysicalExamples
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

example [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu) :
    compileNode request = compileMu request.domain request.left request.right := by
  simp only [compileNode, selected]

example [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu) :
    compileNode request = compileMu request.domain request.left request.right := by
  simp only [compileNode, selected]

example [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu) :
    compileNode request = compileMu request.domain request.left request.right := by
  simp only [compileNode, selected]

end MicroCFTA.MuBodyPhysicalExamples
