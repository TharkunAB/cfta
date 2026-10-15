import MicroCFTA.SourceRefusedClassDomainBoundary
import MicroCFTA.SourceEqualityOpenOrdinaryHead

/-!
# Ordinary exposure of the retained open Mu fixture

The actual stored unfolding starts from the heap returned by the primary
gate. The sequential secondary gate retains this heap. The unfolding returns
ordinary rows. Actual node reconstruction retains the same value and heap.
The reconstructed head satisfies the selected path domain while the original
Mu does not. These receipts use the existing open constructor environment.
They do not assert native readiness or completion of the outer caller.
-/
namespace MicroCFTA.SourceRefusedClassOpenHeadBoundary
open Language EqualityNormalize InternedConstructorTemplates InternedNestedConstruction
open SourceObservations SourceSymbolicIndex
open SourceRefusedClassDomainBoundary (openMuFirst openMuPrimary openMuForest paths)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

attribute [local cbv_eval] array_small

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- Unfold the original open Mu from the actual caller heap after both gate checks. -/
noncomputable def unfolded : Outcome Symbol Guard (Value Symbol Guard) :=
  InternedFreshOrdinaryStoredSubstitution.unfold openMuFirst openMuPrimary.state

/-- Retain the actual unfolded value; unfold_complete excludes the pending fallback. -/
noncomputable def value : Value Symbol Guard :=
  match unfolded with
  | .done result _ => result
  | .pending .. => .empty

/-- Retain the complete constructor heap returned by the actual unfolding. -/
noncomputable def heap : State Symbol Guard := unfolded.state

/-- Read the original rows of the actual unfolded ordinary node. -/
noncomputable def edges : List (EdgeValue Symbol Guard) :=
  match value with
  | .node _ rows _ _ => rows
  | _ => []

/-- Execute the actual node constructor on the unfolded rows and returned heap. -/
noncomputable def rebuilt : Value Symbol Guard × State Symbol Guard := run (makeNode edges) heap

/-- The actual stored unfolding completes with the retained value and exact heap. -/
theorem unfold_complete : unfolded = .done value heap := by cbv

/-- The actual unfolded value has an ordinary node tag. -/
theorem unfolded_node : (match value with | .node .. => True | _ => False) := by cbv

/-- Actual node reconstruction returns the same complete value and constructor heap. -/
theorem rebuild_exact : rebuilt = (value, heap) := by cbv

/-- The complete row read and actual reconstruction form the existing source head graph. -/
theorem head_receipt :
    SourceEqualityRequiredHead.Head openMuFirst openMuPrimary.state rebuilt.1 rebuilt.2 :=
  .read 0 edges heap (by cbv) rfl

/-- The reconstructed ordinary head still retains the unrelated external reference. -/
theorem rebuilt_free : rebuilt.1.free = [.uninterned 999] := by cbv

/-- Actual ordinary reconstruction does not close the whole head. -/
theorem rebuilt_not_closed : rebuilt.1.free ≠ [] := by
  rw [rebuilt_free]
  intro impossible
  cases impossible

/-- The selected ordinary child is closed even though the reconstructed head remains open. -/
theorem rebuilt_domain : SourceEqualityProjectionPathDomain.NodeClosed [0] rebuilt.1 := by
  cbv
  simp [SourceEqualityProjectionGraph.select, SourceEqualityProjectionPathDomain.NodeClosed.eq_1,
    EdgeValue.children, Value.free]

/-- The original Mu remains outside the conservative nonempty-path domain. -/
theorem original_domain_fails : ¬SourceEqualityProjectionPathDomain.NodeClosed [0] openMuFirst :=
  SourceRefusedClassDomainBoundary.open_mu_node_domain_fails

/-- Replace only the first forest value with its actual ordinary head for the domain comparison. -/
noncomputable def exposedForest : List (Value Symbol Guard) := rebuilt.1 :: openMuForest.drop 1

/-- Retain the second value from the original forest. -/
noncomputable def originalSecond : Value Symbol Guard := (openMuForest[1]?).getD .empty

/-- The comparison forest retains the exact selected head and original second value in order. -/
theorem exposed_positions :
    exposedForest[0]? = some rebuilt.1 ∧ exposedForest[1]? = some originalSecond := by cbv

/-- The retained second original endpoint is closed. -/
theorem second_closed : originalSecond.free = [] := by cbv

private theorem forest_selected (values : List (Value Symbol Guard)) (index : Nat) (path : List Int)
    (selected : Value Symbol Guard) (found : values[index]? = some selected)
    (domain : SourceEqualityProjectionPathDomain.NodeClosed path selected) :
    SourceEqualityProjectionPathDomain.ForestClosed (Int.ofNat index :: path) values := by
  intro actual selectedAt
  have original : SourceEqualityProjectionGraph.select values (Int.ofNat index) = some selected := by
    simpa [SourceEqualityProjectionGraph.select] using found
  have same : selected = actual := Option.some.inj (original.symm.trans selectedAt)
  subst actual
  exact domain

/-- The entire original class satisfies the path domain after this single actual head exposure. -/
theorem exposed_class_domain :
    ∀ path ∈ paths true,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) exposedForest := by
  intro path member
  simp only [paths, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact forest_selected exposedForest 0 [0] rebuilt.1 exposed_positions.1 rebuilt_domain
  · exact forest_selected exposedForest 1 [] originalSecond exposed_positions.2
      (by simpa only [SourceEqualityProjectionPathDomain.NodeClosed.eq_1] using second_closed)

/-- Actual ordinary exposure admits the class domain that excludes the original Mu head. -/
theorem open_head_boundary :
    SourceEqualityRequiredHead.Head openMuFirst openMuPrimary.state rebuilt.1 rebuilt.2 ∧
    SourceEqualityProjectionPathDomain.NodeClosed [0] rebuilt.1 ∧
    ¬SourceEqualityProjectionPathDomain.NodeClosed [0] openMuFirst ∧
    ∀ path ∈ paths true,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) exposedForest :=
  ⟨head_receipt, rebuilt_domain, original_domain_fails, exposed_class_domain⟩

end MicroCFTA.SourceRefusedClassOpenHeadBoundary
