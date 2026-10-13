import MicroCFTA.MergedColdMergeCompletion

/-!
# One merged target need not be recursively normalized

The actual cold merge worker returns a singleton column unchanged. Five
parent rows with one identical five-row child therefore merge in two
changing calls. This is a target-normalization obstruction, not a cycle
of a fixed equality schedule.
-/
namespace MicroCFTA.EqualityMergedTargetDelay
open InternedConstructorTemplates MergedSourceComparison

/-- Build five distinct complete edges with the same children. -/
def guarded (children : List (Value Unit Nat)) : List Nat → Work Unit Nat (List (EdgeValue Unit Nat))
  | [] => .pure []
  | guard :: rest => (makeEdge () guard children).bind fun edge =>
      (guarded children rest).bind fun edges => .pure (edge :: edges)

/-- Construct five distinct parent guards over one identical five-row child. -/
def fixture : Work Unit Nat (Value Unit Nat) :=
  (guarded [] [1, 2, 3, 4, 5]).bind fun leaves => (makeNode leaves).bind fun child =>
    (guarded [child] [1, 2, 3, 4, 5]).bind makeNode

/-- Execute one actual source-shaped merge with no demanded recursive-cover comparisons. -/
def step (input : Value Unit Nat × State Unit Nat) : Option (Value Unit Nat × State Unit Nat) :=
  match MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => false) 0 0 input.1 input.2 with
  | .done result after => some (result, after)
  | .failed .. => none

/-- Retain actual runtime states through each successive merge invocation. -/
def rounds : Nat → Option (Value Unit Nat × State Unit Nat)
  | 0 => some (run fixture empty)
  | count + 1 => (rounds count).bind step

/-- Read the ordinary outgoing row count without unfolding any boundary. -/
def rowCount : Value Unit Nat → Nat
  | .node _ edges _ _ => edges.length
  | _ => 0

/-- Observe the parent row count and each immediate child's row count. -/
def shape : Value Unit Nat → Nat × List Nat
  | .node _ edges _ _ => (edges.length, (edges.flatMap EdgeValue.children).map rowCount)
  | _ => (0, [])

/-- The ordinary source syntax builds the same complete fixture from empty caches. -/
def sourceSyntax : InternedNestedConstruction.Syntax Unit Nat :=
  let child := InternedNestedConstruction.Syntax.node
    ([1, 2, 3, 4, 5].map fun guard => .mk () guard [])
  .node ([1, 2, 3, 4, 5].map fun guard => .mk () guard [child])

/-- The counterexample starts with derived cache facts, preparation, and an available closed input. -/
theorem source_valid :
    InternedNestedFacts.Facts (run fixture empty).2 ∧
      MergedPhysicalWarmup.Prepared (run fixture empty).2 ∧
      InternedProbeProvenance.Available (run fixture empty).2 (run fixture empty).1 ∧
      (run fixture empty).1.free = [] := by
  have constructed : InternedNestedConstruction.build sourceSyntax [] empty =
      .done (run fixture empty).1 (run fixture empty).2 := by cbv
  have verified := InternedNestedProvenance.build_verified sourceSyntax [] empty InternedNestedFacts.empty_facts
    (by simp [InternedNestedProvenance.Values])
  have facts : InternedNestedFacts.Facts (run fixture empty).2 := by
    simpa only [constructed, InternedNestedConstruction.Outcome.state] using verified.facts
  refine ⟨facts, ?_, verified.result _ _ constructed, by cbv⟩
  intro key entry body depth ordinary stored
  have member := MergedPhysicalWarmup.inventory_complete (run fixture empty).2 facts.coherent key _ stored
  have noMu : (InternedRecordCoherence.nodeInventory (run fixture empty).2).all (fun value => match value with
      | .mu .. => false
      | _ => true) = true := by cbv
  have impossible := List.all_eq_true.mp noMu _ member
  cases impossible

/-- The first invocation merges only the root because the retained column is a singleton. -/
theorem first_shape : (rounds 1).map (fun result => shape result.1) = some (1, [5]) := by
  cbv

/-- The original source value has five parent rows over the same five-row child. -/
theorem initial_shape : (rounds 0).map (fun result => shape result.1) = some (5, [5, 5, 5, 5, 5]) := by
  cbv

/-- This delayed target has exactly two ordinary layers. -/
theorem ordinary_height : MergedOrdinaryHeight.height (run fixture empty).1 = 2 := by
  cbv

/-- The initial parent-group merge changes the actual root identity. -/
theorem first_changes : (rounds 0).map (fun result => result.1.referenceOf) ≠
    (rounds 1).map (fun result => result.1.referenceOf) := by
  cbv
  decide

/-- The next invocation reaches and merges the formerly unchanged child. -/
theorem second_shape : (rounds 2).map (fun result => shape result.1) = some (1, [1]) := by
  cbv

/-- Consecutive completed merge calls can return different actual interned identities. -/
theorem second_changes : (rounds 1).map (fun result => result.1.referenceOf) ≠
    (rounds 2).map (fun result => result.1.referenceOf) := by
  cbv
  decide

/-- This concrete source trace then stabilizes at the same actual interned root identity. -/
theorem third_fixed : (rounds 3).map (fun result => result.1.referenceOf) =
    (rounds 2).map (fun result => result.1.referenceOf) := by
  cbv

/-- Two actual completed consecutive target merges can return distinct canonical root identities. -/
theorem two_completed_changes : ∃ first second,
    step (run fixture empty) = some first ∧ step first = some second ∧ first.1.referenceOf ≠ second.1.referenceOf := by
  cases first : rounds 1 with
  | none => have impossible := first_shape; simp [first] at impossible
  | some firstValue =>
      cases second : rounds 2 with
      | none => have impossible := second_shape; simp [second] at impossible
      | some secondValue =>
          refine ⟨firstValue, secondValue, first, ?_, ?_⟩
          · change (rounds 1).bind step = some secondValue at second
            simpa only [first, Option.bind_some] using second
          · intro equal
            apply second_changes
            simpa only [first, second, Option.map_some] using congrArg some equal

end MicroCFTA.EqualityMergedTargetDelay
