import MicroCFTA.EndpointStatefulGate
import MicroCFTA.SourceEndpointReachability
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceEqualityPCSNativeEdge
import MicroCFTA.MergedColdReaderClosedInputs
import MicroCFTA.SourceEqualityProjectionPathDomain

/-!
# Clear secondary gates do not close the original forest

Both fixtures use actual source constructor computations. Each selected
endpoint is closed and contains a constrained raw Mu below its ordinary
root. The current primary gate refuses the class. The secondary gate clears
it. One fixture has an unrelated open top child. The other has an open
selected top child whose unvisited sibling contains the free reference.
These are domain boundaries, not source soundness counterexamples.
-/
namespace MicroCFTA.SourceRefusedClassDomainBoundary
open Language EqualityNormalize InternedConstructorTemplates InternedNestedConstruction
open MergedColdReaderClosedInputs (ClosedValues)
open SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "source" => SourceMemoGate.unconstrained

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

attribute [local cbv_eval] array_small

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- The caller environment contains one explicit external reference. -/
def external : Value Symbol Guard := .reference (.uninterned 999)

/-- Both fixtures use one nontrivial original class. -/
def paths : Bool → Class
  | false => [[0], [1]]
  | true => [[0, 0], [1]]

/-- Each selected closed endpoint wraps a raw Mu with a constrained binary body. -/
def endpoint : Syntax Symbol Guard :=
  .node [.mk ("w", .top) top [.binder false
    (.node [.mk ("p", .top) ⟨some [[[0], [1]]], .top⟩
      [.node [.mk ("a", .top) top []], .node [.mk ("a", .top) top []]]])]]

/-- The free reference is outside the class, or outside the selected deeper path. -/
def expression (deeper : Bool) : Syntax Symbol Guard :=
  .node [.mk ("root", .top) ⟨some [paths deeper], .top⟩
    (if deeper then [.node [.mk ("pair", .top) top [endpoint, .var 0]], endpoint]
     else [endpoint, endpoint, .var 0])]

/-- Retain the actual source construction from the open caller environment. -/
noncomputable def built (deeper : Bool) : Outcome Symbol Guard (Value Symbol Guard) :=
  InternedFreshOrdinaryConstruction.build (expression deeper) [external] empty

/-- Keep the complete actual returned constructor heap. -/
noncomputable def heap (deeper : Bool) : State Symbol Guard := (built deeper).state

/-- Read the actual root value; the pending fallback is excluded by source_return. -/
noncomputable def root (deeper : Bool) : Value Symbol Guard :=
  match built deeper with
  | .done value _ => value
  | .pending .. => .empty

/-- Read the original ordered children of the actual root edge. -/
noncomputable def forest (deeper : Bool) : List (Value Symbol Guard) :=
  match root deeper with
  | .node _ (edge :: _) _ _ => edge.children
  | _ => []

/-- Both source constructor computations complete with their exact retained values and heaps. -/
theorem source_return (deeper : Bool) : built deeper = .done (root deeper) (heap deeper) := by
  cases deeper <;> cbv

/-- The tested class is the literal stored equality class of the actual original root edge. -/
theorem original_class (deeper : Bool) :
    (match root deeper with
      | .node _ (edge :: _) _ _ => edge.entry.key.constraint.equalities
      | _ => none) = some [paths deeper] := by
  cases deeper <;> cbv

/-- Read the first actual top child. -/
noncomputable def first (deeper : Bool) : Value Symbol Guard := ((forest deeper)[0]?).getD .empty

/-- Read the second actual top child. -/
noncomputable def second (deeper : Bool) : Value Symbol Guard := ((forest deeper)[1]?).getD .empty

/-- Read the selected deeper endpoint from the first top child's original edge. -/
noncomputable def deeperEndpoint : Value Symbol Guard :=
  match first true with
  | .node _ (edge :: _) _ _ => (edge.children[0]?).getD .empty
  | _ => .empty

/-- The primary policy tests constrained descendants at each ordinary endpoint. -/
noncomputable def primary (deeper : Bool) : Outcome Symbol Guard (Option Bool) :=
  EndpointStatefulGate.classMeets source (SourceEndpointReachability.reaches source)
    2 (forest deeper) (paths deeper) (heap deeper)

/-- The secondary policy omits the endpoint descendant test. -/
noncomputable def secondary (deeper : Bool) : Outcome Symbol Guard (Option Bool) :=
  InternedFreshOrdinaryStatefulGate.classMeets source 2 (forest deeper) (paths deeper) (heap deeper)

/-- Every fixture class contains two distinct original paths. -/
theorem active (deeper : Bool) : Nontrivial (paths deeper) := by
  cases deeper
  · exact ⟨[0], by simp [paths], [1], by simp [paths], by decide⟩
  · exact ⟨[0, 0], by simp [paths], [1], by simp [paths], by decide⟩

/-- Both classes are actually refused by the current endpoint-aware primary gate. -/
theorem primary_refuses (deeper : Bool) : primary deeper = .done (some true) (heap deeper) := by
  cases deeper <;> cbv

/-- Both actual secondary gate checks return false with the entire constructor heap unchanged. -/
theorem secondary_clears (deeper : Bool) : secondary deeper = .done (some false) (heap deeper) := by
  cases deeper <;> cbv

/-- The first fixture selects two closed endpoints. -/
theorem unrelated_endpoints_closed : (first false).free = [] ∧ (second false).free = [] := by cbv

/-- Both selected top positions are present in each actual original forest. -/
theorem selected_top_present (deeper : Bool) :
    (forest deeper)[0]? = some (first deeper) ∧ (forest deeper)[1]? = some (second deeper) := by
  cases deeper <;> cbv

/-- The unrelated third original child is the actual open external reference. -/
theorem unrelated_external : (forest false)[2]? = some external := by cbv

/-- A clear secondary class does not imply that the whole original forest is closed. -/
theorem unrelated_not_closed : ¬ClosedValues (forest false) := by
  intro closed
  have impossible := closed external (List.mem_of_getElem? unrelated_external)
  change [InternedBinderProtocol.Reference.uninterned 999] = [] at impossible
  cases impossible

/-- The deeper fixture also selects two closed endpoints. -/
theorem deeper_endpoints_closed : deeperEndpoint.free = [] ∧ (second true).free = [] := by cbv

/-- The first deeper endpoint is present at the exact selected child index. -/
theorem deeper_endpoint_present :
    (match first true with
      | .node _ (edge :: _) _ _ => edge.children[0]?
      | _ => none) = some deeperEndpoint := by cbv

/-- The selected top child is open only because its unvisited sibling retains the external reference. -/
theorem selected_top_free : (first true).free = [.uninterned 999] := by cbv

/-- Even the selected top child need not be closed when the secondary gate clears its deeper path. -/
theorem selected_top_not_closed : (first true).free ≠ [] := by
  rw [selected_top_free]
  intro impossible
  cases impossible

/-- The missing whole-forest premise already fails on an active class refused by the primary gate. -/
theorem whole_forest_boundary : Nontrivial (paths false) ∧
    primary false = .done (some true) (heap false) ∧
    secondary false = .done (some false) (heap false) ∧
    (first false).free = [] ∧ (second false).free = [] ∧ ¬ClosedValues (forest false) :=
  ⟨active false, primary_refuses false, secondary_clears false, unrelated_endpoints_closed.1,
    unrelated_endpoints_closed.2, unrelated_not_closed⟩

/-- Restricting closure to selected top children still excludes this actual deeper-path fixture. -/
theorem selected_top_boundary : Nontrivial (paths true) ∧
    primary true = .done (some true) (heap true) ∧
    secondary true = .done (some false) (heap true) ∧
    deeperEndpoint.free = [] ∧ (second true).free = [] ∧ (first true).free ≠ [] :=
  ⟨active true, primary_refuses true, secondary_clears true, deeper_endpoints_closed.1,
    deeper_endpoints_closed.2, selected_top_not_closed⟩

private theorem forest_selected (values : List (Value Symbol Guard)) (index : Nat) (path : List Int)
    (value : Value Symbol Guard) (found : values[index]? = some value)
    (domain : SourceEqualityProjectionPathDomain.NodeClosed path value) :
    SourceEqualityProjectionPathDomain.ForestClosed (Int.ofNat index :: path) values := by
  intro selected actual
  have original : SourceEqualityProjectionGraph.select values (Int.ofNat index) = some value := by
    simpa [SourceEqualityProjectionGraph.select] using found
  have same : value = selected := Option.some.inj (original.symm.trans actual)
  subst selected
  exact domain

/-- The selected ordinary step admits the closed endpoint while its sibling remains open. -/
theorem deeper_node_domain : SourceEqualityProjectionPathDomain.NodeClosed [0] (first true) := by
  have shape : (match first true with | .node _ [_] _ _ => True | _ => False) := by cbv
  cases ordinary : first true with
  | empty | reference | union | mu => simp only [ordinary] at shape
  | node entry edges depth free =>
      cases edges with
      | nil => simp only [ordinary] at shape
      | cons edge rest =>
          cases rest with
          | cons => simp only [ordinary] at shape
          | nil =>
              simp only [SourceEqualityProjectionPathDomain.NodeClosed.eq_3, List.mem_singleton, forall_eq]
              intro child found
              have selected : edge.children[0]? = some deeperEndpoint := by
                simpa only [ordinary] using deeper_endpoint_present
              have actual : edge.children[0]? = some child := by simpa [SourceEqualityProjectionGraph.select] using found
              have same : deeperEndpoint = child := Option.some.inj (selected.symm.trans actual)
              subst child
              simpa only [SourceEqualityProjectionPathDomain.NodeClosed.eq_1] using deeper_endpoints_closed.1

/-- Both actual fixtures satisfy the selected path domain for every original class path. -/
theorem path_domain (deeper : Bool) :
    ∀ path ∈ paths deeper,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) (forest deeper) := by
  cases deeper
  · intro path member
    simp only [paths, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact forest_selected (forest false) 0 [] (first false) (selected_top_present false).1
        (by simpa only [SourceEqualityProjectionPathDomain.NodeClosed.eq_1] using unrelated_endpoints_closed.1)
    · exact forest_selected (forest false) 1 [] (second false) (selected_top_present false).2
        (by simpa only [SourceEqualityProjectionPathDomain.NodeClosed.eq_1] using unrelated_endpoints_closed.2)
  · intro path member
    simp only [paths, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact forest_selected (forest true) 0 [0] (first true) (selected_top_present true).1 deeper_node_domain
    · exact forest_selected (forest true) 1 [] (second true) (selected_top_present true).2
        (by simpa only [SourceEqualityProjectionPathDomain.NodeClosed.eq_1] using deeper_endpoints_closed.2)

/-- An unconstrained Mu retains its self reference and an unrelated external reference. -/
def openMuExpression : Syntax Symbol Guard :=
  .node [.mk ("root", .top) ⟨some [paths true], .top⟩
    [.binder true (.node [.mk ("pair", .top) top
      [.node [.mk ("a", .top) top []], .var 0, .var 1]]), endpoint]]

/-- Retain the actual source construction of the open Mu fixture. -/
noncomputable def openMuBuilt : Outcome Symbol Guard (Value Symbol Guard) :=
  InternedFreshOrdinaryConstruction.build openMuExpression [external] empty

/-- Keep the complete constructor heap returned by the open Mu construction. -/
noncomputable def openMuHeap : State Symbol Guard := openMuBuilt.state

/-- Read the actual constructed root of the open Mu fixture. -/
noncomputable def openMuRoot : Value Symbol Guard :=
  match openMuBuilt with
  | .done value _ => value
  | .pending .. => .empty

/-- Read the original ordered forest that contains the open Mu and closed endpoint. -/
noncomputable def openMuForest : List (Value Symbol Guard) :=
  match openMuRoot with
  | .node _ (edge :: _) _ _ => edge.children
  | _ => []

/-- Read the original first child, before gate unfolding. -/
noncomputable def openMuFirst : Value Symbol Guard := (openMuForest[0]?).getD .empty

/-- Execute the primary gate on the actual original class and heap. -/
noncomputable def openMuPrimary : Outcome Symbol Guard (Option Bool) :=
  EndpointStatefulGate.classMeets source (SourceEndpointReachability.reaches source)
    3 openMuForest (paths true) openMuHeap

/-- Execute the secondary gate, including the actual open Mu unfolding. -/
noncomputable def openMuSecondary : Outcome Symbol Guard (Option Bool) :=
  InternedFreshOrdinaryStatefulGate.classMeets source 3 openMuForest (paths true) openMuHeap

/-- The original source construction completes with the exact retained value and heap. -/
theorem open_mu_source_return : openMuBuilt = .done openMuRoot openMuHeap := by cbv

/-- The tested class is the literal equality class of the actual original root edge. -/
theorem open_mu_original_class :
    (match openMuRoot with
      | .node _ (edge :: _) _ _ => edge.entry.key.constraint.equalities
      | _ => none) = some [paths true] := by cbv

/-- The first selected top child is an actual Mu, not a missing-child fallback. -/
theorem open_mu_head : (match openMuFirst with | .mu .. => True | _ => False) := by cbv

/-- The open Mu retains exactly the caller's external reference. -/
theorem open_mu_free : openMuFirst.free = [.uninterned 999] := by cbv

/-- The actual source predicate classifies this open Mu as unconstrained. -/
theorem open_mu_unconstrained : source openMuFirst = true := by cbv

/-- The actual primary gate refuses the class after the same constructor effects as the secondary gate. -/
theorem open_mu_primary_refuses :
    openMuPrimary = .done (some true) openMuSecondary.state := by cbv

/-- The actual secondary gate clears the class after its completed Mu unfolding. -/
theorem open_mu_secondary_clears :
    openMuSecondary = .done (some false) openMuSecondary.state := by cbv

/-- The conservative path domain excludes a nonempty path at this open Mu head. -/
theorem open_mu_node_domain_fails :
    ¬SourceEqualityProjectionPathDomain.NodeClosed [0] openMuFirst := by
  cbv
  intro impossible
  cases impossible

/-- A false secondary gate does not imply the conservative selected path domain. -/
theorem open_mu_path_domain_fails :
    ¬SourceEqualityProjectionPathDomain.ForestClosed [0, 0] openMuForest := by
  intro domain
  have selected : SourceEqualityProjectionGraph.select openMuForest 0 = some openMuFirst := by cbv
  exact open_mu_node_domain_fails (domain openMuFirst selected)

/-- The original active class fails the selected path domain at its first member. -/
theorem open_mu_class_domain_fails :
    ¬(∀ path ∈ paths true,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) openMuForest) := by
  intro domain
  exact open_mu_path_domain_fails (domain [0, 0] (by simp [paths]))

/-- An active refused class can clear the secondary gate and still fail the Mu path domain. -/
theorem open_mu_boundary : Nontrivial (paths true) ∧
    openMuPrimary = .done (some true) openMuSecondary.state ∧
    openMuSecondary = .done (some false) openMuSecondary.state ∧
    source openMuFirst = true ∧
    ¬SourceEqualityProjectionPathDomain.ForestClosed [0, 0] openMuForest :=
  ⟨active true, open_mu_primary_refuses, open_mu_secondary_clears,
    open_mu_unconstrained, open_mu_path_domain_fails⟩

/-- Run the secondary gate from the actual heap returned by the primary gate. -/
noncomputable def openMuSequentialSecondary : Outcome Symbol Guard (Option Bool) :=
  InternedFreshOrdinaryStatefulGate.classMeets source 3 openMuForest (paths true) openMuPrimary.state

/-- The sequential secondary gate returns false and retains the whole primary result heap. -/
theorem open_mu_sequential_secondary_clears :
    openMuSequentialSecondary = .done (some false) openMuPrimary.state := by cbv

end MicroCFTA.SourceRefusedClassDomainBoundary
