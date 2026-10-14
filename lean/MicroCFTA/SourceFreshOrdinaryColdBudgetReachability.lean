import MicroCFTA.SourceFreshOrdinaryColdGuardedSoundness
import MicroCFTA.MergedFreshOrdinaryExposureInputs

/-!
# Closed physical values reached from final shared rows

The final table supplies available closed roots and exact replayed reads.
Their epsilon paths retain available closed values. Constructor children
start another declared row. These facts do not assume semantic completeness.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdBudgetReachability
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows Supported row_child)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)
open SourcePreparedSharedRows (reference)
open MergedFreshOrdinaryGraph
open Productivity (Reachable)

/-- A physical value lies on an epsilon path from an available closed declared row. -/
def Reached [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (rows : Rows Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ root, Available state root ∧ root.free = [] ∧ Supported rows root ∧
    Reachable (successors state) [root] value

/-- Each available closed supported root starts a declared epsilon path. -/
theorem root [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (rows : Rows Symbol Guard)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = [])
    (supported : Supported rows value) : Reached state rows value :=
  ⟨value, available, closed, supported, .seed List.mem_cons_self⟩

/-- A declared row has an exact allocation-free read, including the empty root. -/
theorem supported_read [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (rows : Rows Symbol Guard) (replayed : ReplayedRows state rows)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) (supported : Supported rows value) :
    ∃ fuel edges, MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges state := by
  cases same : reference value with
  | none =>
      have empty : value = .empty := by
        cases value <;> simp only [reference] at same <;> first | contradiction | rfl
      subst value
      exact ⟨0, [], rfl⟩
  | some identity =>
      obtain ⟨edges, present⟩ := supported identity same
      obtain ⟨fuel, done⟩ := SourceFreshOrdinaryColdGuardedSoundness.row_replay state semantic.1.normal.facts
        rows replayed value available identity same edges present
      exact ⟨fuel, edges, done⟩

/-- Every reached value is available and closed in the exact final cache. -/
theorem inputs [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (rows : Rows Symbol Guard) (replayed : ReplayedRows state rows)
    (value : Value Symbol Guard) (reached : Reached state rows value) : Available state value ∧ value.free = [] := by
  obtain ⟨root, available, closed, supported, path⟩ := reached
  obtain ⟨fuel, edges, done⟩ := supported_read state semantic rows replayed root available closed supported
  exact MergedFreshOrdinaryExposureInputs.nodeEdges_reachable fuel state semantic covered root available closed edges done value path

/-- Each actual epsilon successor stays on a declared row's epsilon path. -/
theorem next [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (rows : Rows Symbol Guard)
    (value : Value Symbol Guard) (reached : Reached state rows value) (child : Value Symbol Guard)
    (member : child ∈ successors state value) : Reached state rows child := by
  obtain ⟨root, available, closed, supported, path⟩ := reached
  exact ⟨root, available, closed, supported, .step path member⟩

/-- Each child of a reached constructor edge starts an available closed declared row. -/
theorem child [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (rows : Rows Symbol Guard) (replayed : ReplayedRows state rows)
    (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows)
    (value : Value Symbol Guard) (reached : Reached state rows value) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ InternedEdgeResidency.nodeEdges value) (child : Value Symbol Guard) (inside : child ∈ edge.children) :
    Reached state rows child := by
  obtain ⟨original, available, closed, supported, path⟩ := reached
  have origin : Origin state [original] edge := ⟨value, path, member⟩
  cases same : reference original with
  | none =>
      have empty : original = .empty := by
        cases original <;> simp only [reference] at same <;> first | contradiction | rfl
      subst original
      have impossible := MergedFreshOrdinaryExposureCoverage.origin_terminal state .empty rfl edge origin
      cases impossible
  | some identity =>
      obtain ⟨edges, present⟩ := supported identity same
      obtain ⟨fuel, done⟩ := SourceFreshOrdinaryColdGuardedSoundness.row_replay state semantic.1.normal.facts
        rows replayed original available identity same edges present
      have selected := MergedFreshOrdinaryExposureCoverage.nodeEdges_covers_fixed fuel state semantic covered original
        available closed edges done edge origin
      have provenance := row_child state semantic.1.normal.facts rows resident closedRows identity edges present edge selected child inside
      exact root state rows child provenance.1 provenance.2.1 provenance.2.2

end MicroCFTA.SourceFreshOrdinaryColdBudgetReachability
