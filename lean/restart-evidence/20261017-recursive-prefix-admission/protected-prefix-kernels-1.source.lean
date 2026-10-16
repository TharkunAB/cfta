import MicroCFTA.SourceEqualityNativeDemandProtectedPrefix

namespace MicroCFTA.ProtectedPrefixKernels

open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand SourceEqualityNativeDemandProtectedPrefix
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def emptyRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩

/-- An actual Empty body reaches its own node finish, publishes its captured owner, and leaves the outer read pending. -/
theorem empty_node_publication (before : Checked width) (handle : Nat)
    (shape : SourceRecursiveIntersectionNative.Shape before.native)
    (running : before.native.nodes.cells handle = some ⟨emptyRequest, .evaluating⟩) :
    let next : Value Symbol Guard → Code Symbol Guard Unit := fun _ => .read 0 (fun _ => .pure ())
    let after := {before with native := SourceRecursiveIntersectionThunks.finishNode handle .empty before.native}
    Steps 1 ((.code (compileNode emptyRequest) : Control (Value Symbol Guard)).bind
      (fun value => .finishNode handle value (next value))) before (.code (next .empty)) after ∧
      after.native.nodes.cells handle = some ⟨emptyRequest, .returned .empty⟩ ∧
      after.operations = before.operations ∧ after.native.edges = before.native.edges ∧
      (∃ bodyFuel frameFuel value middle, bodyFuel + frameFuel = 1 ∧ bodyFuel < 2 ∧
        Steps bodyFuel (.code (compileNode emptyRequest)) before (.code (.pure value)) middle ∧
        middle.native.nodes.cells handle = some ⟨emptyRequest, .evaluating⟩) := by
  dsimp only
  let next : Value Symbol Guard → Code Symbol Guard Unit := fun _ => .read 0 (fun _ => .pure ())
  have body : Steps 0 (.code (compileNode emptyRequest)) before (.code (.pure .empty)) before :=
    .refl _ _
  have owner := node_body_owner 0 handle emptyRequest before before .empty shape running body
  have actual : Steps 1 ((.code (compileNode emptyRequest) : Control (Value Symbol Guard)).bind
      (fun value => .finishNode handle value (next value))) before (.code (next .empty))
      {before with native := SourceRecursiveIntersectionThunks.finishNode handle .empty before.native} :=
    .cons _ _ _ _ _ _ 0 rfl (.refl _ _)
  refine ⟨actual, owner.2, rfl, rfl, ?_⟩
  rcases node_cases 1 handle emptyRequest next before _ _ shape running actual with
      ⟨inner, trace, nonpure, same⟩ |
      ⟨bodyFuel, frameFuel, value, middle, count, smaller, trace, owner, published, rest⟩
  · have impossible := body.length_le_complete trace
    omega
  · exact ⟨bodyFuel, frameFuel, value, middle, count, smaller, trace, owner⟩

private def sentinelJob (request : EdgeRequest Symbol Guard) : Work Symbol Guard (EdgeValue Symbol Guard) :=
  makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]

private def checkedBefore (before : Checked width) : Checked width :=
  {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}

private def constructed (request : EdgeRequest Symbol Guard) (before : Checked width) : Checked width :=
  {checkedBefore before with native := advance before.native {before.native.machine with heap :=
    (InternedConstructorTemplates.run (sentinelJob request) before.native.machine.heap).2}}

/-- A checked mismatch constructs its actual sentinel, retains the evaluating edge owner, and publishes that exact result. -/
theorem checked_edge_publication (request : EdgeRequest Symbol Guard) (before : Checked width) (handle : Nat)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (shape : SourceRecursiveIntersectionNative.Shape before.native)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩) :
    let result := (InternedConstructorTemplates.run (sentinelJob request) before.native.machine.heap).1
    let next : EdgeValue Symbol Guard → Code Symbol Guard Unit := fun _ => .read 1 (fun _ => .pure ())
    let middle := constructed request before
    let after := {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle result middle.native}
    Steps 3 ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun value => .finishEdge handle value (next value))) before (.code (next result)) after ∧
      after.native.edges.cells handle = some ⟨request, .returned result⟩ ∧
      after.operations = SourceEqualityMkEdgeAllocation.emptyField before.operations ∧
      after.native.nodes = before.native.nodes ∧
      (∃ bodyFuel frameFuel value current, bodyFuel + frameFuel = 3 ∧ bodyFuel < 4 ∧
        Steps bodyFuel (.edgeBody request .pure) before (.code (.pure value)) current ∧
        current.native.edges.cells handle = some ⟨request, .evaluating⟩) := by
  dsimp only
  let result := (InternedConstructorTemplates.run (sentinelJob request) before.native.machine.heap).1
  let next : EdgeValue Symbol Guard → Code Symbol Guard Unit := fun _ => .read 1 (fun _ => .pure ())
  have first : SourceEqualityNativeDemand.step (.edgeBody request Code.pure) before =
      .yielded (.code (.work (sentinelJob request) Code.pure)) (checkedBefore before) := by
    simp only [SourceEqualityNativeDemand.step]
    rw [body_mismatch request Code.pure before mismatch]
    simp only [sentinel, code_bind_pure]
    rfl
  have work : SourceEqualityNativeDemand.step (.code (.work (sentinelJob request) Code.pure))
      (checkedBefore before) = .yielded (.code (.pure result)) (constructed request before) := rfl
  have body : Steps 2 (.edgeBody request Code.pure) before (.code (.pure result)) (constructed request before) :=
    .cons _ _ _ _ _ _ 1 first (.cons _ _ _ _ _ _ 0 work (.refl _ _))
  have owner := edge_body_owner 2 handle request before (constructed request before) result shape running body
  have lifted := body.bind 2 _ _ _ _ (fun value => .finishEdge handle value (next value))
  have finished : Steps 1 (.code (.finishEdge handle result (next result))) (constructed request before)
      (.code (next result))
      {constructed request before with native := SourceRecursiveIntersectionThunks.finishEdge handle result
        (constructed request before).native} := .cons _ _ _ _ _ _ 0 rfl (.refl _ _)
  have actual := lifted.trans 2 1 _ _ _ _ _ _ finished
  refine ⟨actual, owner.2, rfl, rfl, ?_⟩
  rcases edge_cases 3 handle request next before _ _ shape running actual with
      ⟨inner, trace, nonpure, same⟩ |
      ⟨bodyFuel, frameFuel, value, current, count, smaller, trace, owner, published, rest⟩
  · have impossible := body.length_le_complete trace
    omega
  · exact ⟨bodyFuel, frameFuel, value, current, count, smaller, trace, owner⟩

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms empty_node_publication
#check @empty_node_publication
#print axioms checked_edge_publication
#check @checked_edge_publication

end MicroCFTA.ProtectedPrefixKernels
