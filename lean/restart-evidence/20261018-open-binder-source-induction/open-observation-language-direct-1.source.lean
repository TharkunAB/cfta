import MicroCFTA.SourceCurrentOpenPreorderSimulation
import MicroCFTA.MergedFreshOrdinaryExposureLanguage

/-!
# Guarded finite-tree language from finite open observations

Observation depth at least the tree height determines acceptance.
The proof retains complete guards and ordered child terms. Each epsilon
path uses actual unfolding at the same reader. This module does not
transport observations between readers or construct a source simulation.
-/
namespace MicroCFTA.SourceCurrentOpenObservationLanguage
open InternedConstructorTemplates Language
open MergedFreshOrdinaryGraph MergedFreshOrdinaryExposureLanguage
open SourceCurrentOpenObservations (Same)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem children (reader : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (depth : Nat)
    (step : ∀ first second term, Same depth reader [first] [second] → term.height ≤ depth →
      EpsilonUnion.Accepts (graph reader meaning) first term →
      EpsilonUnion.Accepts (graph reader meaning) second term)
    {first second : List (Value Symbol Guard)} {terms : List (Term Symbol)}
    (pairs : All₂ (fun a b => Same depth reader [a] [b]) first second)
    (accepted : All₂ (fun value term => EpsilonUnion.Accepts (graph reader meaning) value term ∧
      term.height ≤ depth) first terms) :
    All₂ (EpsilonUnion.Accepts (graph reader meaning)) second terms := by
  induction pairs generalizing terms with
  | nil => cases accepted; exact .nil
  | cons pair rest ih =>
      cases accepted with
      | cons current later =>
          exact .cons (step _ _ _ pair current.2 current.1) (ih later)

/-- Observations through a finite tree's height determine its guarded acceptance. -/
theorem finite (reader : State Symbol Guard) (meaning : Guard → Term Symbol → Bool)
    (depth : Nat) : ∀ first second term, term.height ≤ depth →
      Same depth reader [first] [second] →
      (EpsilonUnion.Accepts (graph reader meaning) first term ↔
        EpsilonUnion.Accepts (graph reader meaning) second term) := by
  induction depth with
  | zero =>
      intro first second term height same
      exact False.elim (Nat.not_le_of_gt term.height_pos height)
  | succ depth ih =>
      have forward (first second : Value Symbol Guard) (term : Term Symbol)
          (height : term.height ≤ depth + 1) (same : Same (depth + 1) reader [first] [second])
          (accepted : EpsilonUnion.Accepts (graph reader meaning) first term) :
          EpsilonUnion.Accepts (graph reader meaning) second term := by
        obtain ⟨row, origin, terms, rfl, runs, guard⟩ := accepts_origin reader meaning first term accepted
        obtain ⟨other, found, fields⟩ := same.2.1 row origin
        have bound : forestHeight terms ≤ depth := by
          change forestHeight terms + 1 ≤ depth + 1 at height
          omega
        have bounded := (all₂_height_iff (EpsilonUnion.Accepts (graph reader meaning))
          row.children terms depth).mpr ⟨runs, bound⟩
        have transported := children reader meaning depth
          (fun a b term pair height accepted => (ih a b term height pair).mp accepted) fields.2.2 bounded
        apply origin_accepts reader meaning second other found (.node row.entry.key.symbol terms)
        refine ⟨terms, ?_, transported, ?_⟩
        · exact congrArg (fun symbol => Term.node symbol terms) fields.1
        · rw [← fields.2.1]
          exact guard
      intro first second term height same
      exact ⟨forward first second term height same,
        forward second first term height same.symm⟩

/-- Agreement at every finite observation depth gives exact guarded finite-tree language. -/
theorem all_depths (reader : State Symbol Guard) (first second : Value Symbol Guard)
    (same : ∀ depth, Same depth reader [first] [second])
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph reader meaning) first term ↔
      EpsilonUnion.Accepts (graph reader meaning) second term :=
  finite reader meaning term.height first second term (Nat.le_refl _) (same term.height)

/-- Mutual roots in a directional simulation accept exactly the same guarded finite trees. -/
theorem directed (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (simulation : SourceCurrentOpenPreorderSimulation.Directed reader relation)
    (first second : Value Symbol Guard)
    (paired : SourceCurrentOpenPreorderSimulation.Mutual relation first second)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph reader meaning) first term ↔
      EpsilonUnion.Accepts (graph reader meaning) second term :=
  all_depths reader first second
    (fun depth => SourceCurrentOpenPreorderSimulation.same reader relation simulation depth first second paired)
    meaning term

end MicroCFTA.SourceCurrentOpenObservationLanguage
