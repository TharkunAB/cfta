import MicroCFTA.MergedPhysicalComparison
import MicroCFTA.InternedStoredMuOrigins

/-!
# A closed physical recursion needs a larger comparison cache

The source constructs the unary natural-number automaton. Its first
unfolding allocates a new ordinary record. The initial cache inventory
therefore does not already contain all comparison states. Actual warmup
derives a finite later inventory for the recurring physical comparison.
-/
namespace MicroCFTA.MergedPhysicalComparisonExample
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open MergedPhysicalWarmup MergedPhysicalComparison
open InternedBinderProtocol (NodeKey)

/-- A closed binder accepts zero and each unary successor of itself. -/
def program : Syntax Nat Unit := .binder true (.node [.mk 0 () [], .mk 1 () [.var 0]])

/-- Execute both source probes and the actual fresh body from empty caches. -/
def built := build program [] (empty (Symbol := Nat) (Guard := Unit))

/-- Retain the exact returned source value. -/
def root : Value Nat Unit := match built with | .done value _ => value | .pending .. => .empty

/-- Retain the actual source cache after construction. -/
def initial : State Nat Unit := built.state

/-- The source expression completes and its returned recursive value is closed. -/
theorem constructed : built = .done root initial ∧ root.free = [] := by cbv

/-- Construction derives both the complete cache facts and the root's availability. -/
theorem source_facts : Facts initial ∧ Available initial root := by
  have verified := build_verified program [] empty empty_facts (by simp [Values])
  have done : build program [] empty = .done root initial := constructed.1
  exact ⟨by simpa only [done, Outcome.state] using verified.facts, verified.result root initial done⟩

/-- The finite initial record inventory contains only Mu bodies that prepare no nested binder. -/
theorem source_prepared : Prepared initial := by
  intro key entry body depth ordinary stored
  have present := inventory_complete initial source_facts.1.coherent key _ stored
  have shallow : (nodeInventory initial).all (fun value => match value with
      | .mu _ body _ _ => decide (body.depth = 0)
      | _ => true) = true := by cbv
  have zero : body.depth = 0 := of_decide_eq_true (List.all_eq_true.mp shallow _ present)
  exact InternedStoredClosedMuCompletion.zero_prepared body initial source_facts.1.coherent
    ((source_facts.1.cached.nodes key _ stored).children body (by simp [children])) zero

/-- Execute the actual stored-body substitution for the first source exposure. -/
def unfolded := InternedStoredSubstitution.unfold root initial

/-- A closed source Mu can allocate a comparison state outside its initial cache inventory. -/
theorem first_exposure_allocates :
    (match unfolded with
    | .pending .. => none
    | .done value state => some (root.referenceOf, value.referenceOf, initial.nodes.next, state.nodes.next)) =
      some (.mu 2, .node 4, 4, 5) := by cbv

/-- The newly exposed ordinary identity is absent from the original complete record list. -/
theorem initial_inventory_incomplete :
    (match unfolded with
    | .pending .. => False
    | .done value _ => value.referenceOf ∉ (nodeInventory initial).map Value.referenceOf) := by
  cbv
  intro member
  cases member with
  | tail _ rest =>
      cases rest with
      | tail _ rest =>
          cases rest with
          | tail _ rest =>
              cases rest with
              | tail _ rest => cases rest

/-- The actual finite warmup completes with the new exposure record installed. -/
theorem warmup_completes :
    (match warmup (nodeInventory initial) initial with
    | .pending .. => none
    | .done _ state => some state.nodes.next) = some 5 := by cbv

/-- Structural source facts derive a later cache in which every complete Mu unfolds without allocation. -/
theorem source_ready :
    ∃ outputs after, warmup (nodeInventory initial) initial = .done outputs after ∧ Facts after ∧
      Grows initial after ∧ Extends initial.nodes.issued after.nodes.issued ∧
      InternedShallowHeap.NoNewMu initial after ∧ Values after outputs ∧ Ready after outputs :=
  prepare initial source_facts.1 source_prepared

end MicroCFTA.MergedPhysicalComparisonExample
