import MicroCFTA.SourceListSortRuns

/-!
# Ordered natural runs of the actual source sorter

The descending accumulator reverses each strict run. The ascending function
accumulator retains its exact prefix. Both actual branches produce ordered
runs under a transitive relation and the source comparison choices.
-/
namespace MicroCFTA.SourceListSortRunsOrdered
open SourceListSort

private theorem append_step (relation : Item → Item → Prop)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (initial : List Item) (last next : Item) (ordered : (initial ++ [last]).Pairwise relation)
    (before : relation last next) : ((initial ++ [last]) ++ [next]).Pairwise relation := by
  apply List.pairwise_append.mpr
  refine ⟨ordered, by simp, ?_⟩
  intro item member other otherMember
  have same : other = next := List.mem_singleton.mp otherMember
  subst other
  rcases List.mem_append.mp member with member | member
  · exact transitive ((List.pairwise_append.mp ordered).2.2 item member last List.mem_cons_self) before
  · have same : item = last := List.mem_singleton.mp member
    subst item
    exact before

mutual
/-- Every run from actual source run detection is ordered. -/
theorem sequences_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b) (input : List Item) :
    ∀ run ∈ sequences gt input, run.Pairwise relation := by
  cases input with
  | nil => simp only [sequences, List.mem_singleton]; intro run same; subst run; exact .nil
  | cons a rest =>
      cases rest with
      | nil => simp only [sequences, List.mem_singleton]; intro run same; subst run; simp
      | cons b rest =>
          rw [sequences]
          split
          · rename_i take
            apply descending_ordered relation gt transitive compared b [a] rest
            rw [List.pairwise_pair]
            simpa only [take, ite_true] using compared a b
          · rename_i take
            apply ascending_ordered relation gt transitive compared b (a :: ·) rest [a]
              (fun _ => rfl)
            rw [List.singleton_append, List.pairwise_pair]
            simpa only [take, ite_false] using compared a b
termination_by 2 * input.length

private theorem descending_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (last : Item) (reversed rest : List Item) (ordered : (last :: reversed).Pairwise relation) :
    ∀ run ∈ descending gt last reversed rest, run.Pairwise relation := by
  cases rest with
  | nil =>
      rw [descending]
      intro run member
      rcases List.mem_cons.mp member with rfl | member
      · exact ordered
      · exact sequences_ordered relation gt transitive compared [] run member
  | cons b rest =>
      rw [descending]
      split
      · rename_i take
        apply descending_ordered relation gt transitive compared b (last :: reversed) rest
        apply List.pairwise_cons.mpr
        refine ⟨?_, ordered⟩
        intro item member
        have before : relation b last := by simpa only [take, ite_true] using compared last b
        rcases List.mem_cons.mp member with rfl | member
        · exact before
        · exact transitive before ((List.pairwise_cons.mp ordered).1 item member)
      · intro run member
        rcases List.mem_cons.mp member with rfl | member
        · exact ordered
        · exact sequences_ordered relation gt transitive compared (b :: rest) run member
termination_by 2 * rest.length + 1
decreasing_by all_goals simp_all only [List.length_cons]; omega

private theorem ascending_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (last : Item) (append : List Item → List Item) (rest initial : List Item)
    (exact : ∀ suffix, append suffix = initial ++ suffix)
    (ordered : (initial ++ [last]).Pairwise relation) :
    ∀ run ∈ ascending gt last append rest, run.Pairwise relation := by
  cases rest with
  | nil =>
      rw [ascending]
      intro run member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [exact] using ordered
      · exact sequences_ordered relation gt transitive compared [] run member
  | cons b rest =>
      rw [ascending]
      split
      · rename_i take
        have nextExact : ∀ suffix, append (last :: suffix) = (initial ++ [last]) ++ suffix := by
          intro suffix
          rw [exact]
          simp only [List.append_assoc, List.singleton_append]
        apply ascending_ordered relation gt transitive compared b (fun suffix => append (last :: suffix))
          rest (initial ++ [last]) nextExact
        apply append_step relation transitive initial last b ordered
        have noTake : gt last b = false := by simpa only [Bool.not_eq_true'] using take
        simpa only [noTake, Bool.false_eq_true, ite_false] using compared last b
      · intro run member
        rcases List.mem_cons.mp member with rfl | member
        · simpa only [exact] using ordered
        · exact sequences_ordered relation gt transitive compared (b :: rest) run member
termination_by 2 * rest.length + 1
decreasing_by all_goals simp_all only [List.length_cons]; omega
end

end MicroCFTA.SourceListSortRunsOrdered
