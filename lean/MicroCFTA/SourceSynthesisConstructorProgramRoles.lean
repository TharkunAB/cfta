import MicroCFTA.SourceCurrentActualParentRowOrigins
import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric

/-!
# Program roles through the actual checked edge constructor

The acceptance test selects the guard and children together. Acceptance
retains the original fields. Rejection returns Top with one Empty child.
Both branches retain the strict Program row certificate.
These laws require an actual completed constructor call.
-/
namespace MicroCFTA.SourceSynthesisConstructorProgramRoles
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentNativeOperationHeap (Good)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]
variable {literal : String → Symbol}

private theorem build_fields {symbol loaded children before result after}
    (actual : SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result, after))
    (good : Good (width := width) before) (loadedReady : EqReady before.operations.constraints loaded.stored)
    (available : Values before.native.machine.heap children) :
    result.entry.key.symbol = symbol ∧
      ((result.entry.key.constraint = raw loaded ∧ result.children = children) ∨
        (result.entry.key.constraint = top ∧ result.children = [.empty])) := by
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol loaded.stored loaded.guard children
    before.operations before.native.machine.heap good.operations loadedReady
  have returned := congrArg Prod.fst actual
  simp only [SourceCurrentAllocatedMkEdge.build, built.1] at returned
  cases Except.ok.inj returned
  cases keep : SourceEqualityMkEdgeAllocation.accepted (raw loaded) children.length with
  | true =>
      have selected : SourceEqualityMkEdgeAllocation.accepted
          (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = true := keep
      simp only [SourceEqualityMkEdgeAllocation.work, selected, ite_true]
      have fields := MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
        good.semantic.ready.semantic.1.normal.facts symbol (raw loaded) children available
      exact ⟨fields.1, Or.inl fields.2⟩
  | false =>
      have selected : SourceEqualityMkEdgeAllocation.accepted
          (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = false := keep
      simp only [SourceEqualityMkEdgeAllocation.work, selected, Bool.false_eq_true, ite_false]
      have fields := MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
        good.semantic.ready.semantic.1.normal.facts symbol top [.empty]
        (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
      exact ⟨fields.1, Or.inr fields.2⟩

/-- Every actual rejection sentinel has the strict annotated Program shape. -/
theorem reject_program (literal : String → Symbol) (symbol : Symbol)
    (before : Checked width) (good : Good before) :
    ProgramEdge literal (SourceCurrentAllocatedMkEdge.reject symbol before).1 := by
  have fields := MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
    good.semantic.ready.semantic.1.normal.facts symbol top [.empty]
    (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
  exact .annotated _ .empty fields.2.1 fields.2.2

/-- Actual application construction retains its source fields or the strict sentinel shape. -/
theorem build_application {loaded before result after} {types marker function argument : Node}
    (actual : SourceCurrentAllocatedMkEdge.build (literal "app") loaded
      [types, marker, function, argument] before = (.ok result, after))
    (good : Good (width := width) before) (loadedReady : EqReady before.operations.constraints loaded.stored)
    (available : Values before.native.machine.heap [types, marker, function, argument])
    (guard : raw loaded = eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
    (functionRole : ProgramValue literal function) (argumentRole : ProgramValue literal argument) :
    ProgramEdge literal result := by
  obtain ⟨symbol, fields⟩ := build_fields actual good loadedReady available
  rcases fields with ⟨constraint, children⟩ | ⟨constraint, children⟩
  · exact .application result types marker function argument symbol (constraint.trans guard)
      children functionRole argumentRole
  · exact .annotated result .empty constraint children

/-- Actual filter construction retains its source fields or the strict sentinel shape. -/
theorem build_filter {loaded before result after} {goal candidates : Node}
    (actual : SourceCurrentAllocatedMkEdge.build (literal "filter") loaded [goal, candidates] before =
      (.ok result, after))
    (good : Good (width := width) before) (loadedReady : EqReady before.operations.constraints loaded.stored)
    (available : Values before.native.machine.heap [goal, candidates])
    (guard : raw loaded = eqGuard [[[0], [1, 0]]]) (candidateRole : ProgramValue literal candidates) :
    ProgramEdge literal result := by
  obtain ⟨symbol, fields⟩ := build_fields actual good loadedReady available
  rcases fields with ⟨constraint, children⟩ | ⟨constraint, children⟩
  · exact .filter result goal candidates symbol (constraint.trans guard) children candidateRole
  · exact .annotated result .empty constraint children

/-- A source annotation row and a rejected row both retain the strict annotated shape. -/
theorem build_annotated {symbol loaded before result after} {annotation : Node}
    (actual : SourceCurrentAllocatedMkEdge.build symbol loaded [annotation] before = (.ok result, after))
    (good : Good (width := width) before) (loadedReady : EqReady before.operations.constraints loaded.stored)
    (available : Values before.native.machine.heap [annotation]) (guard : raw loaded = top) :
    ProgramEdge literal result := by
  obtain ⟨_symbol, fields⟩ := build_fields actual good loadedReady available
  rcases fields with ⟨constraint, children⟩ | ⟨constraint, children⟩
  · exact .annotated result annotation (constraint.trans guard) children
  · exact .annotated result .empty constraint children

end MicroCFTA.SourceSynthesisConstructorProgramRoles
