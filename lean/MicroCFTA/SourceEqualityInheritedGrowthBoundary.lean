import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceEqualityInheritedPayload
import MicroCFTA.SourceEqualityConstraintOrigins

/-!
# Fixed local constraints can produce longer inherited paths after descent

The fixture uses one normalized physical constraint at every step. Actual
source combination, trie reconstruction, and child descent produce the
observed payloads. A finite prefix refutes a bound by the local path length.
This does not assert that an outer recursive caller reaches all these steps
or that the infinite sequence has infinitely many distinct payloads.
-/
namespace MicroCFTA.SourceEqualityInheritedGrowthBoundary
open Language EqualityNormalize SourceEqualityClassOrder
local notation "Payload" => SourceEqualityPrecheck.Constraint
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "sourceTop" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

attribute [local cbv_eval] array_small

/-- The fixed local input uses two nontrivial path classes. -/
def raw : Constraints := [[[0], [1, 0, 0]], [[0, 1], [1, 0, 1]]]

/-- Store the actual completed source normalization with a Top guard. -/
noncomputable def localConstraint : Constraint := ⟨SourceCompactGuards.normalize raw, .top⟩

/-- The single original physical equality field has the cached source representation. -/
theorem local_cached : SourceEqualityGuardReadback.Cached localConstraint.equalities :=
  SourceEqualityGuardReadback.normalize_cached raw

/-- Read the same original complete local constraint at every step. -/
noncomputable def own : Except String Payload := SourceEqualityPhysicalPayload.own localConstraint

/-- Combine the actual inherited and local records, then descend through child one. -/
noncomputable def walk : Nat → Except String Payload
  | 0 => .ok (some [])
  | step + 1 => do
      let inherited ← walk step
      let localPayload ← own
      let combined ← SourceEqualityInheritedPayload.combine inherited localPayload
      pure (SourceEqualityDescend.descend combined 1)

/-- Every finite prefix has an actual completed physical payload with ascending coherent tries. -/
theorem finite (steps : Nat) : ∃ payload, walk steps = .ok payload ∧ SourceEqualityDescend.WellFormed payload := by
  have localRead : ∃ payload, own = .ok payload := by
    obtain ⟨payload, done, _, _⟩ := SourceEqualityInheritedPayload.read_complete (Symbol := Unit)
      localConstraint.equalities local_cached
    exact ⟨payload, done⟩
  induction steps with
  | zero => exact ⟨some [], rfl, by simp [SourceEqualityDescend.WellFormed]⟩
  | succ steps ih =>
      obtain ⟨inherited, reached, _⟩ := ih
      obtain ⟨localPayload, localDone⟩ := localRead
      obtain ⟨combined, combinedDone, valid, _⟩ :=
        SourceEqualityInheritedPayload.combine_complete (Symbol := Unit) inherited localPayload
      refine ⟨SourceEqualityDescend.descend combined 1, ?_, SourceEqualityDescend.descend_wellFormed combined valid 1⟩
      simp only [walk, reached, localDone, Bind.bind, Except.bind, combinedDone, pure, Except.pure]

/-- Read back complete physical path lists and retain source errors and contradiction. -/
noncomputable def observed (steps : Nat) : Except String (Option Constraints) :=
  (walk steps).map SourceEqualityInheritedPayload.classes

/-- Read the maximum path length without identifying failure with contradiction or empty constraints. -/
def pathLength (classes : Constraints) : Nat := (classes.flatten.map List.length).foldr Nat.max 0

/-- Observe the actual inherited path budget after a finite number of source steps. -/
noncomputable def lengthAt (steps : Nat) : Except String (Option Nat) :=
  (observed steps).map (Option.map pathLength)

/-- The actual fixed local accessor contains a path of maximum length four. -/
theorem own_length : own.map (fun payload => (SourceEqualityInheritedPayload.classes payload).map pathLength) = .ok (some 4) := by
  cbv

/-- Actual source combination and trie descent lengthen inherited paths in this finite prefix. -/
theorem actual_prefix : (List.range 5).map lengthAt =
    [.ok (some 0), .ok (some 3), .ok (some 4), .ok (some 5), .ok (some 6)] := by
  cbv

/-- Three actual combine-and-descend steps exceed the fixed own-payload path bound. -/
theorem third_length : lengthAt 3 = .ok (some 5) := by
  have selected := congrArg (fun rows => rows[3]?) actual_prefix
  simpa only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] using selected

/-- The maximum original local path length does not bound every inherited state of this source recurrence. -/
theorem not_local_length_bound : ¬ (∀ steps length, lengthAt steps = .ok (some length) → length ≤ 4) := by
  intro bounded
  have impossible := bounded 3 5 third_length
  omega

/-- Lift the first descended equality payload to a complete constraint with a Top guard. -/
def firstConstraint : Constraint := ⟨some [[[0, 0, 1], [0, 1]]], .top⟩

/-- The lifted equality field is the actual source readback after one step. -/
theorem first_observed : observed 1 = .ok firstConstraint.equalities := by cbv

/-- Source conjunction of the fixed normalized local constraint with itself is physically idempotent. -/
theorem local_idempotent : conjoin localConstraint localConstraint = localConstraint := by cbv

/-- Source Top on the left retains the fixed normalized local constraint. -/
theorem top_left : conjoin sourceTop localConstraint = localConstraint := by cbv

/-- Source Top on the right retains the fixed normalized local constraint. -/
theorem top_right : conjoin localConstraint sourceTop = localConstraint := by cbv

/-- The literal and Top closure contains only these two actual complete constraint values. -/
theorem literal_closure (constraint : Constraint)
    (derived : SourceEqualityConstraintOrigins.Derived [localConstraint] sourceTop conjoin constraint) :
    constraint = sourceTop ∨ constraint = localConstraint := by
  induction derived with
  | literal member => exact Or.inr (List.mem_singleton.mp member)
  | top => exact Or.inl rfl
  | conjunction _ _ firstIH secondIH =>
      rcases firstIH with rfl | rfl <;> rcases secondIH with rfl | rfl
      · exact Or.inl (by cbv)
      · exact Or.inr top_left
      · exact Or.inr top_right
      · exact Or.inr local_idempotent

/-- The lifted inherited readback can leave the conjunction closure of original edge constraints. -/
theorem first_not_literal_derived :
    ¬ SourceEqualityConstraintOrigins.Derived [localConstraint] sourceTop conjoin firstConstraint := by
  intro derived
  rcases literal_closure firstConstraint derived with top | literal
  · have lengths := congrArg (fun constraint => constraint.equalities.map pathLength) top
    cbv at lengths
    cases lengths
  · have lengths := congrArg (fun constraint => constraint.equalities.map pathLength) literal
    cbv at lengths
    cases lengths

end MicroCFTA.SourceEqualityInheritedGrowthBoundary
