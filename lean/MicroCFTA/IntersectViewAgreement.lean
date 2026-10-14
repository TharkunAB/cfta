import MicroCFTA.IntersectDomainEquivalence
import MicroCFTA.IntersectDomain

/-!
# Exact schedule execution on unchanged reachable payloads

Total graph views can differ outside the original input domain. Execution
reads only the input payloads, their children, and actual domain bindings.
Agreement on this closed set retains every finite result and failure.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- Two views retain every read on a closed set of original inputs. -/
structure ViewAgreement (before after : View Symbol) (valid : Input → Prop) : Prop where
  free : ∀ input, valid input → after.free input = before.free input
  copy : ∀ input, valid input → after.copy input = before.copy input
  body : ∀ name, valid (.mu name) → after.body name = before.body name
  rows : ∀ name, valid (.node name) → after.rows name = before.rows name
  members : ∀ name, valid (.union name) → after.members name = before.members name
  body_valid : ∀ name, valid (.mu name) → valid (before.body name)
  child_valid : ∀ name, valid (.node name) → ∀ row ∈ before.rows name, ∀ child ∈ row.children, valid child
  member_valid : ∀ name, valid (.union name) → ∀ child ∈ before.members name, valid child

/-- Every stored free binding belongs to the retained input domain. -/
def DomainInputs (valid : Input → Prop) (domain : Domain) : Prop :=
  ∀ entry ∈ domain.free, valid entry.2

/-- Resetting the source domain removes every binding obligation. -/
theorem DomainInputs.empty (valid : Input → Prop) : DomainInputs valid {} := by
  intro entry member
  cases member

/-- Domain extension adds only its actual original operands. -/
theorem DomainInputs.extend (valid : Input → Prop) (domain : Domain) (known : DomainInputs valid domain)
    (entries : List (Nat × Input)) (inputs : ∀ entry ∈ entries, valid entry.2) (key : Pair) :
    DomainInputs valid (extend domain entries key) := by
  intro entry member
  rcases List.mem_append.mp member with new | old
  · exact inputs entry (List.mem_reverse.mp new)
  · exact known entry old

/-- A completed free lookup selects an actual retained domain entry. -/
theorem DomainInputs.lookup (valid : Input → Prop) (domain : Domain) (known : DomainInputs valid domain)
    (name : Nat) (input : Input) (found : IntersectSchedule.lookup domain name = some input) : valid input := by
  obtain ⟨entry, selected, same⟩ := Option.map_eq_some_iff.mp found
  rw [← same]
  exact known entry (List.mem_of_find?_eq_some selected)

/-- Ordered traversal reads only members of its actual request list. -/
theorem walk_congr_on (before after : A → Except Error B) (inputs : List A)
    (same : ∀ input ∈ inputs, before input = after input) : walk before inputs = walk after inputs := by
  induction inputs with
  | nil => rfl
  | cons first rest ih =>
      simp only [walk, same first List.mem_cons_self,
        ih (fun input member => same input (List.mem_cons_of_mem first member))]

/-- Both schedule workers retain exact results under agreement on their closed input domain. -/
theorem view_agreement_workers [DecidableEq Symbol] (before after : View Symbol) (valid : Input → Prop)
    (same : ViewAgreement before after valid) (fuel : Nat) :
    (∀ domain, DomainInputs valid domain → ∀ left right, valid left → valid right →
      run after fuel domain left right = run before fuel domain left right) ∧
    (∀ domain, DomainInputs valid domain → ∀ left right,
      (∀ child ∈ left.children, valid child) → (∀ child ∈ right.children, valid child) →
      edge after fuel domain left right = edge before fuel domain left right) := by
  induction fuel with
  | zero => exact ⟨by intros; rfl, by intros; rfl⟩
  | succ fuel ih =>
      constructor
      · intro domain known left right leftValid rightValid
        rw [run.eq_def after (fuel + 1) domain left right, run.eq_def before (fuel + 1) domain left right]
        have leftClosed : closed after left = closed before left := congrArg List.isEmpty (same.free left leftValid)
        have rightClosed : closed after right = closed before right := congrArg List.isEmpty (same.free right rightValid)
        simp only [leftClosed, rightClosed]
        split
        · rfl
        · split
          · exact ih.1 _ (DomainInputs.empty valid) left right leftValid rightValid
          · split
            · rw [same.copy left leftValid]
            · split
              · exact ih.1 domain known right left rightValid leftValid
              · split
                · rfl
                · cases left <;> cases right <;> dsimp only
                  all_goals first
                    | rfl
                    | (rw [same.body _ leftValid, same.body _ rightValid]
                       apply congrArg _
                       apply ih.1
                       · apply DomainInputs.extend valid domain known
                         intro entry member
                         rcases List.mem_cons.mp member with rfl | member
                         · exact leftValid
                         · have equal := List.mem_singleton.mp member; subst entry; exact rightValid
                       · exact same.body_valid _ leftValid
                       · exact same.body_valid _ rightValid)
                    | (rw [same.body _ leftValid]
                       apply congrArg _
                       apply ih.1
                       · apply DomainInputs.extend valid domain known
                         intro entry member
                         have equal := List.mem_singleton.mp member; subst entry; exact leftValid
                       · exact same.body_valid _ leftValid
                       · exact rightValid)
                    | (rw [same.body _ rightValid]
                       apply congrArg _
                       apply ih.1
                       · apply DomainInputs.extend valid domain known
                         intro entry member
                         have equal := List.mem_singleton.mp member; subst entry; exact rightValid
                       · exact leftValid
                       · exact same.body_valid _ rightValid)
                    | (rw [same.members _ leftValid]
                       apply congrArg _
                       apply walk_congr_on
                       intro member present
                       exact ih.1 domain known member _ (same.member_valid _ leftValid member present) rightValid)
                    | (rw [same.members _ rightValid]
                       apply congrArg _
                       apply walk_congr_on
                       intro member present
                       exact ih.1 domain known _ member leftValid (same.member_valid _ rightValid member present))
                    | (rw [same.rows _ leftValid, same.rows _ rightValid]
                       apply congrArg _
                       apply walk_congr_on
                       intro rows present
                       have originals := joined_members _ _ rows present
                       exact ih.2 domain known rows.1 rows.2
                         (same.child_valid _ leftValid rows.1 originals.1)
                         (same.child_valid _ rightValid rows.2 originals.2))
                    | (split <;> first
                        | rfl
                        | exact ih.1 domain known _ _ (DomainInputs.lookup valid domain known _ _ (by assumption)) rightValid
                        | exact ih.1 domain known _ _ leftValid (DomainInputs.lookup valid domain known _ _ (by assumption)))
      · intro domain known left right leftValid rightValid
        rw [edge.eq_2 after domain left right fuel, edge.eq_2 before domain left right fuel]
        split
        · rfl
        · apply congrArg _
          apply walk_congr_on
          intro children present
          have originals := List.of_mem_zip present
          exact ih.1 domain known children.1 children.2 (leftValid _ originals.1) (rightValid _ originals.2)

/-- Changing unused total defaults cannot change a bounded source schedule outcome. -/
theorem run_view_agreement [DecidableEq Symbol] (before after : View Symbol) (valid : Input → Prop)
    (same : ViewAgreement before after valid) (fuel : Nat) (domain : Domain) (known : DomainInputs valid domain)
    (left right : Input) (leftValid : valid left) (rightValid : valid right) :
    run after fuel domain left right = run before fuel domain left right :=
  (view_agreement_workers before after valid same fuel).1 domain known left right leftValid rightValid

end MicroCFTA.IntersectSchedule
