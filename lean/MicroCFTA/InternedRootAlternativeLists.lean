import MicroCFTA.InternedBoundaryFilter

/-!
# Root reference removal commutes with source identity deduplication

The source union keeps the first operand with each identity. Removing a
selected reference before or after that operation gives the same ordered
remaining operands. The law retains exact payload order, not only sets.
-/
namespace MicroCFTA.InternedRootAlternativeLists
open InternedConstructorTemplates
open InternedBinderProtocol (Reference NodeRef)

/-- Removing a reference from a list uses the same source identity test as root self filtering. -/
def remove (name : Reference) (values : List (Value Symbol Guard)) : List (Value Symbol Guard) :=
  values.filter (fun value => value.referenceOf != .ref name)

/-- Two identity-based source filters commute without changing operand order. -/
theorem filters_commute (values : List (Value Symbol Guard)) (first second : NodeRef) :
    (values.filter (fun value => value.referenceOf != first)).filter (fun value => value.referenceOf != second) =
      (values.filter (fun value => value.referenceOf != second)).filter (fun value => value.referenceOf != first) := by
  simp only [List.filter_filter]
  congr 1
  funext value
  exact Bool.and_comm _ _

/-- Removing a selected reference commutes with first-identity source deduplication. -/
theorem remove_distinct (name : Reference) (values : List (Value Symbol Guard)) :
    remove name (distinctNodes values) = distinctNodes (remove name values) := by
  cases values with
  | nil => simp [remove, distinctNodes]
  | cons first rest =>
      by_cases same : first.referenceOf = .ref name
      · simp only [distinctNodes, remove, List.filter_cons, same, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        change remove name (distinctNodes (remove name rest)) = distinctNodes (remove name rest)
        rw [remove_distinct name (remove name rest)]
        simp [remove, List.filter_filter]
      · have kept : (first.referenceOf != .ref name) = true := by simpa only [bne_iff_ne] using same
        simp only [distinctNodes, remove, List.filter_cons, kept, ↓reduceIte]
        change first :: remove name (distinctNodes (rest.filter (fun value => value.referenceOf != first.referenceOf))) =
          first :: distinctNodes ((remove name rest).filter (fun value => value.referenceOf != first.referenceOf))
        rw [remove_distinct name (rest.filter (fun value => value.referenceOf != first.referenceOf))]
        congr 2
        exact filters_commute rest first.referenceOf (.ref name)
termination_by values.length
decreasing_by
  all_goals simp_wf
  all_goals have := List.length_filter_le (fun value : Value Symbol Guard => value.referenceOf != first.referenceOf) rest; simp_all [remove]; omega

/-- Filtering flattened source alternatives preserves their original child order. -/
theorem remove_flatMap (name : Reference) (values : List (Value Symbol Guard)) :
    remove name (values.flatMap unionMembers) = values.flatMap (fun value => remove name (unionMembers value)) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simpa only [List.flatMap_cons, remove, List.filter_append] using congrArg (remove name (unionMembers first) ++ ·) ih

/-- Equal stripped original alternatives determine equal stripped canonical member lists. -/
theorem normalized_equal (firstName secondName : Reference) (first second : List (Value Symbol Guard))
    (same : remove firstName (first.flatMap unionMembers) = remove secondName (second.flatMap unionMembers)) :
    remove firstName (distinctNodes (first.flatMap unionMembers)) =
      remove secondName (distinctNodes (second.flatMap unionMembers)) := by
  rw [remove_distinct, remove_distinct, same]

end MicroCFTA.InternedRootAlternativeLists
