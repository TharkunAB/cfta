import MicroCFTA.InternedReachableGateRank

/-!
# A ranked shallow query in a source cache with a deeper Mu

Actual nested source construction creates an outer Mu with positive body
Mu depth and an inner Mu with depth-zero body. The reachable-only carrier
accepts the inner query in that same cache. The whole-cache carrier cannot.
-/
namespace MicroCFTA.InternedReachableGateExample
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedUnionNormalForm InternedStoredSelfFilter InternedStoredBodyInvariant
open InternedShallowHeap InternedShallowValues InternedGateRank

/-- The inner body uses its own binder, the enclosing binder, and one external reference. -/
def program : Syntax Nat Unit :=
  .binder true (.binder true (.node [.mk 0 () [.var 0, .var 1, .var 2]]))

/-- The actual source caller provides one unresolved external reference. -/
def environment : List (Value Nat Unit) := [.reference (.uninterned 999)]

/-- Actual construction includes both probes for each dynamically nested binder. -/
def original : Outcome Nat Unit (Value Nat Unit) := build program environment empty

/-- Retain the exact actual final cache state. -/
def final : State Nat Unit := original.state

/-- Select the returned source record; the pending fallback is excluded below. -/
def outer : Value Nat Unit := match original with
  | .done value _ => value
  | .pending .. => .empty

/-- Select the actual stored body of the outer Mu. -/
def inner : Value Nat Unit := match outer with
  | .mu _ body _ _ => body
  | _ => .empty

/-- This particular source execution completes with its actual retained record. -/
theorem source_return : original = .done outer final := by cbv

/-- The actual source result is an outer Mu. -/
theorem outer_mu : (match outer with | .mu .. => True | _ => False) := by cbv

/-- The actual inner record is a Mu with cached body depth zero. -/
theorem inner_mu : (match inner with | .mu _ body _ _ => body.depth = 0 | _ => False) := by cbv

/-- The outer body has positive Mu depth, so this cache violates the former global restriction. -/
theorem inner_depth : inner.depth = 1 := by cbv

/-- All source inputs start with complete reference provenance. -/
theorem inputs_available : Values (empty (Symbol := Nat) (Guard := Unit)) environment := by
  intro value member
  have same : value = .reference (.uninterned 999) := by simpa [environment] using member
  subst value
  exact ordinary_available empty 999

/-- Source construction supplies full cache and returned-record provenance. -/
theorem checked : Verified empty original Available := build_verified program environment empty empty_facts inputs_available

/-- The inner Mu remains an actual canonical child of the returned source record. -/
theorem inner_available : Available final inner := by
  have outerAvailable := checked.result outer final source_return
  have actual := outer_mu
  cases shape : outer with
  | empty | reference | node | union => simp [shape] at actual
  | mu entry body depth ordinary =>
      have available : Available final (.mu entry body depth ordinary) := shape ▸ outerAvailable
      simpa only [inner, shape] using available.children body (by simp [InternedProbeProvenance.children])

/-- Its reachable property follows from the actual computed source body bound. -/
theorem inner_shallow : ShallowValue inner := by
  have actual := inner_mu
  cases shape : inner with
  | empty | reference | node | union => simp [shape] at actual
  | mu entry body depth ordinary => exact .mu entry body depth ordinary (by simpa [shape] using actual)

/-- The same source cache really contains a deeper Mu, not only a hypothetical one. -/
theorem deeper_cache : ¬ Shallow final := by
  have outerAvailable := checked.result outer final source_return
  have actual := outer_mu
  intro shallow
  cases shape : outer with
  | empty | reference | node | union => simp [shape] at actual
  | mu entry body depth ordinary =>
      have available : Available final (.mu entry body depth ordinary) := shape ▸ outerAvailable
      have zero := shallow entry.key entry body depth ordinary (available.resident entry rfl)
      have positive := inner_depth
      simp only [inner, shape, zero] at positive
      contradiction

/-- The reachable-only gate accepts this query without imposing a depth bound on its cache. -/
def certified : InternedReachableGateRank.Node Nat Unit := by
  have facts : Facts final := by simpa only [source_return, Outcome.state] using checked.facts
  have flat : Flat final := build_flat program environment empty empty_facts inputs_available empty_flat
  have clean : Clean final := build_clean program environment empty empty_facts inputs_available empty_flat empty_clean
  exact ⟨final, inner, facts, flat, clean, inner_shallow, inner_available⟩

/-- The source-selected inner query is open, so the gate takes its unfolding branch. -/
theorem actual_open : certified.value.free.isEmpty = false := by cbv

/-- Inspect the actual source adapter without evaluating proof fields of the certified carrier. -/
def unfolded := InternedStoredSubstitution.unfold inner final

def unfoldedValue : Value Nat Unit := match unfolded with
  | .done value _ => value
  | .pending .. => .empty

/-- The actual inner-body unfolding completes in the mixed source cache. -/
theorem actual_unfold : unfolded = .done unfoldedValue unfolded.state := by cbv

/-- The actual inner query unfolds from head rank one to zero in that same mixed cache. -/
theorem actual_ranks : headRank certified.value = 1 ∧
    headRank (InternedReachableGateRank.step certified).result.value = 0 := by
  have same := (InternedReachableGateRank.step certified).actual
  change unfolded = _ at same
  rw [actual_unfold] at same
  have equal := (Outcome.done.inj same).1
  constructor
  · cbv
  · rw [← equal]
    cbv

/-- This concrete query has a total gate despite the deeper unrelated cached Mu. -/
theorem mixed_ranked : ¬ Shallow certified.state ∧
    ∀ path, ∃ bound, ∀ extra, ConstrainedRecursionGate.nodeMeets (InternedReachableGateRank.read (fun _ => true))
      (bound + extra) path certified = some (InternedReachableGateRank.total (fun _ => true) path certified) :=
  ⟨deeper_cache, fun path => InternedReachableGateRank.eventually_exact (fun _ => true) path certified⟩

end MicroCFTA.InternedReachableGateExample
