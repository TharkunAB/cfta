import MicroCFTA.RecursiveFieldCombinators

/-!
# Local callback contracts below a requested forest height

A recursive occurrence consumes a private root. The recursive induction
therefore gives child contracts only below the current request height.
These local contracts retain the source fields and their complete ranks.
-/
namespace MicroCFTA.RecursiveFieldBounds
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct
open RecursiveFieldCombinators

/-- A finite field is exact for all requests below the specified height. -/
def ExactBelow (bound : Nat) (source : Finite Symbol) : Prop :=
  ∀ view wanted, forestHeight wanted ≤ bound → ∀ position,
    (position, true) ∈ source.positions view wanted ↔
      ∃ term, source.select position = some term ∧ project view term = wanted

/-- Every finite child satisfies the same local height contract. -/
def LeavesBelow (bound : Nat) : Recipe Symbol → Prop
  | .finite source => ExactBelow bound source
  | .occurrence => True
  | .map inner | .pay inner | .label _ inner => LeavesBelow bound inner
  | .choice left right | .ap left right => LeavesBelow bound left ∧ LeavesBelow bound right

/-- Complete certificates use only finite-leaf requests below the current bound. -/
theorem checked_sound_below [DecidableEq Symbol] (limit : Nat)
    (recipe : Recipe Symbol) (leaves : LeavesBelow limit recipe)
    (view : View) (wanted : List (EngineTerm Symbol)) (bound : forestHeight wanted ≤ limit)
    (position : Position)
    (member : (position, true) ∈ positions (fun _ => 0) emptyBody recipe view wanted) :
    ∃ term, Selects (fun _ => 0) emptyBody recipe position term ∧ project view term = wanted := by
  induction recipe generalizing view wanted position with
  | finite source =>
      rw [positions] at member
      obtain ⟨term, selected, same⟩ := (leaves view wanted bound position).mp member
      exact ⟨term, .finite source position term selected, same⟩
  | occurrence =>
      simp only [positions.eq_def, emptyBody, emptyField] at member
      split at member <;> simp at member
  | map inner ih =>
      rw [positions] at member
      obtain ⟨term, selected, same⟩ := ih leaves view wanted bound position member
      exact ⟨term, .map inner position term selected, same⟩
  | pay inner ih =>
      rw [positions] at member
      obtain ⟨original, present, rfl⟩ := pay_origin _ _ member
      obtain ⟨term, selected, same⟩ := ih leaves view wanted bound original present
      exact ⟨term, .pay inner original term selected, same⟩
  | choice left right ihl ihr =>
      rw [positions.eq_def, mem_sorted] at member
      cases view with
      | labelled =>
          dsimp only at member
          rcases List.mem_append.mp member with first | second
          · obtain ⟨term, selected, same⟩ := ihl leaves.1 .labelled wanted bound position first
            exact ⟨.node (.choice 0) [term], .left left right position term selected, same⟩
          · obtain ⟨original, present, rfl⟩ := choice_origin _ _ _ _ second
            obtain ⟨term, selected, same⟩ := ihr leaves.2 .labelled wanted bound original present
            exact ⟨.node (.choice 1) [term], .right left right original term selected, same⟩
      | whole | spine =>
          dsimp only at member
          split at member
          · rename_i child
            obtain ⟨term, selected, same⟩ := ihl leaves.1 .whole [child] (by simp_all only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]; omega) position member
            have termEq := StaticCheckedRanks.whole_eq term child same
            subst term
            exact ⟨.node (.choice 0) [child], .left left right position child selected, by
              simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]⟩
          · rename_i child
            obtain ⟨original, present, rfl⟩ := choice_origin _ _ _ _ member
            obtain ⟨term, selected, same⟩ := ihr leaves.2 .whole [child] (by simp_all only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]; omega) original present
            have termEq := StaticCheckedRanks.whole_eq term child same
            subst term
            exact ⟨.node (.choice 1) [child], .right left right original child selected, by
              simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]⟩
          · simp at member
  | ap functions arguments ihf iha =>
      rw [positions.eq_def, mem_sorted] at member
      cases view with
      | whole =>
          dsimp only at member
          split at member
          · rename_i function argument
            obtain ⟨p, q, pm, qm, rfl⟩ := product_origin _ _ _ _ _ member
            obtain ⟨f, fs, fv⟩ := ihf leaves.1 .whole [function] (by simp_all only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]; omega) p pm
            obtain ⟨x, xs, xv⟩ := iha leaves.2 .whole [argument] (by simp_all only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]; omega) q qm
            have feq := StaticCheckedRanks.whole_eq f function fv
            have xeq := StaticCheckedRanks.whole_eq x argument xv
            subst f; subst x
            exact ⟨.node .apply [function, argument], .ap functions arguments p q function argument fs xs, rfl⟩
          · simp at member
      | spine | labelled =>
          dsimp only at member
          split at member
          · simp at member
          · rename_i argument found
            obtain ⟨p, q, pm, qm, rfl⟩ := product_origin _ _ _ _ _ member
            obtain ⟨f, fs, fv⟩ := ihf leaves.1 .spine wanted.dropLast (Nat.le_trans (dropLast_height wanted) bound) p pm
            obtain ⟨x, xs, xv⟩ := iha leaves.2 .whole [argument] (by have h := last_height wanted argument found; simpa only [forestHeight, List.foldr_cons, List.foldr_nil, Nat.max_zero] using Nat.le_trans h bound) q qm
            have xeq := StaticCheckedRanks.whole_eq x argument xv
            subst x
            refine ⟨.node .apply [f, argument], .ap functions arguments p q f argument fs xs, ?_⟩
            simpa [project, labelled, spine, SupportTerms.applicationLeftChildren,
              SupportTerms.applicationTermChildren, ← fv] using StaticCheckedRanks.spine_split wanted argument found
  | label symbol inner ih =>
      rw [positions.eq_def] at member
      dsimp only at member
      split at member
      · rename_i found children
        split at member
        · rename_i labelEq
          subst found
          obtain ⟨original, present, rfl⟩ := pay_origin _ _ member
          obtain ⟨term, selected, same⟩ := ih leaves .labelled children (by simp_all only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]; omega) original present
          refine ⟨SupportTerms.labelTerm symbol term, .label symbol inner original term selected, ?_⟩
          rw [labelled_source, StaticCandidateRanks.project_user]
          exact congrArg (fun terms => [Term.node (Label.user symbol) terms]) same
        · simp at member
      · simp at member

/-- Each source derivation is complete at every request below the leaf bound. -/
theorem certified_complete_below [DecidableEq Symbol] (limit : Nat)
    (recipe : Recipe Symbol) (position : Position) (term : EngineTerm Symbol)
    (selected : Selects (fun _ => 0) emptyBody recipe position term)
    (leaves : LeavesBelow limit recipe) (view : View)
    (bound : forestHeight (project view term) ≤ limit) :
    (position, true) ∈ positions (fun _ => 0) emptyBody recipe view (project view term) := by
  induction selected generalizing view with
  | finite source position term selected =>
      rw [positions]
      exact (leaves view (project view term) bound position).mpr ⟨term, selected, rfl⟩
  | occurrence position term child ih =>
      cases child with
      | finite source position term selected => simp [emptyField] at selected
  | map inner position term child ih => rw [positions]; exact ih leaves view bound
  | pay inner position term child ih =>
      rw [positions]
      exact List.mem_map.mpr ⟨(position, true), ih leaves view bound, rfl⟩
  | left left right position term child ih =>
      cases view with
      | whole | spine =>
          simpa [positions, project, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, mem_sorted] using ih leaves.1 .whole (by simp_all only [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, Option.getD_none, forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]; omega)
      | labelled =>
          rw [positions, mem_sorted]
          exact List.mem_append_left _ (ih leaves.1 .labelled bound)
  | right left right position term child ih =>
      cases view with
      | whole | spine =>
          have small : forestHeight (project .whole term) ≤ limit := by
            simp_all only [project, spine, SupportTerms.applicationLeftChildren,
              SupportTerms.applicationTermChildren, Option.getD_none, forestHeight,
              Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]
            omega
          have offsetMember := List.mem_map.mpr ⟨(position, true), ih leaves.2 .whole small,
            rfl (a := RecursiveCheckedRanks.choiceRow [counts (fun _ => 0) left, counts (fun _ => 0) right] 1 (position, true))⟩
          simpa [positions, project, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, mem_sorted, RecursiveCheckedRanks.choiceRow] using offsetMember
      | labelled =>
          rw [positions, mem_sorted]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨(position, true), ih leaves.2 .labelled bound, rfl⟩)
  | ap functions arguments first second function argument hf hx ihf ihx =>
      have childProduct := RecursiveCheckedRanks.product_complete (counts (fun _ => 0) functions) (counts (fun _ => 0) arguments)
      cases view with
      | whole =>
          simp only [project, positions, mem_sorted]
          exact childProduct _ _ _ _ (ihf leaves.1 .whole (by
            simp_all only [project, forestHeight, Term.height,
              List.foldr_cons, List.foldr_nil, Nat.max_zero]
            omega)) (ihx leaves.2 .whole (by
            simp_all only [project, forestHeight, Term.height,
              List.foldr_cons, List.foldr_nil, Nat.max_zero]
            omega))
      | spine | labelled =>
          simp only [project, labelled, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, Option.getD_some]
          rw [positions.eq_def]
          dsimp only
          rw [mem_sorted]
          split
          · rename_i found
            simp only [List.getLast?_concat] at found
            contradiction
          · rename_i last found
            have lastEq : argument = last := by simpa only [List.getLast?_concat, Option.some.injEq] using found
            subst last
            simpa only [List.dropLast_concat, project, spine] using
              childProduct _ _ _ _ (ihf leaves.1 .spine (by
            simp_all only [project, labelled, spine, SupportTerms.applicationLeftChildren,
              SupportTerms.applicationTermChildren, Option.getD_some,
              RecursiveCallbackCompleteness.fold_height_append, forestHeight,
              List.foldr_cons, List.foldr_nil, Nat.max_zero]
            omega)) (ihx leaves.2 .whole (by
            simp_all only [project, labelled, spine, SupportTerms.applicationLeftChildren,
              SupportTerms.applicationTermChildren, Option.getD_some,
              RecursiveCallbackCompleteness.fold_height_append, forestHeight,
              List.foldr_cons, List.foldr_nil, Nat.max_zero]
            omega))
  | label symbol inner position term child ih =>
      rw [labelled_source, StaticCandidateRanks.project_user, positions]
      simp only [↓reduceIte]
      exact List.mem_map.mpr ⟨(position, true), ih leaves .labelled (by rw [labelled_source, StaticCandidateRanks.project_user] at bound; simp_all only [project, forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]; omega), rfl⟩


/-- Local class tables determine finite forward derivations without callback premises. -/
theorem lookup_selects (recipe : Recipe Symbol) (indexed : LeavesIndexed recipe)
    (position : Position) (term : EngineTerm Symbol)
    (found : (classTerms (fun _ => []) recipe position.size)[position.rank]? = some term) :
    Selects (fun _ => 0) emptyBody recipe position term := by
  induction recipe generalizing position term with
  | finite source => exact .finite source position term ((finite_lookup source indexed position term).mp found)
  | occurrence => simp [classTerms] at found
  | map inner ih => exact .map inner position term (ih indexed position term found)
  | pay inner ih =>
      cases position with
      | mk size rank =>
          cases size with
          | zero => simp [classTerms] at found
          | succ size => exact .pay inner ⟨size, rank⟩ term (ih indexed _ term found)
  | choice left right ihl ihr =>
      by_cases first : position.rank < (classTerms (fun _ => []) left position.size).length
      · rw [classTerms, List.getElem?_append_left (by simpa using first), List.getElem?_map] at found
        obtain ⟨child, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        exact .left left right position child (ihl indexed.1 position child selected)
      · rw [classTerms, List.getElem?_append_right (by simpa using Nat.le_of_not_lt first),
          List.length_map, List.getElem?_map] at found
        obtain ⟨child, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        let childPosition : Position := ⟨position.size, position.rank - counts (fun _ => 0) left position.size⟩
        have selectedLocal : (classTerms (fun _ => []) right childPosition.size)[childPosition.rank]? = some child := by
          simpa [childPosition, class_length (fun _ => []) (fun _ => 0) (fun _ => rfl)] using selected
        have offset : (RecursiveCheckedRanks.choiceRow
            [counts (fun _ => 0) left, counts (fun _ => 0) right] 1 (childPosition, true)).1 = position := by
          have lower : counts (fun _ => 0) left position.size ≤ position.rank := by
            simpa [class_length (fun _ => []) (fun _ => 0) (fun _ => rfl)] using Nat.le_of_not_lt first
          simp [RecursiveCheckedRanks.choiceRow, choicePosition, childPosition, Nat.add_sub_of_le lower]
        have step := Selects.right (self := fun _ => 0) (body := emptyBody) left right childPosition child
          (ihr indexed.2 childPosition child selectedLocal)
        simpa only [offset] using step
  | ap functions arguments ihf iha =>
      obtain ⟨first, second, function, argument, rfl, firstFound, secondFound, rfl⟩ :=
        product_lookup (fun _ => []) (fun _ => 0) (fun _ => rfl) functions arguments position term found
      exact .ap functions arguments first second function argument
        (ihf indexed.1 first function firstFound) (iha indexed.2 second argument secondFound)
  | label symbol inner ih =>
      cases position with
      | mk size rank =>
          cases size with
          | zero => simp [classTerms] at found
          | succ size =>
              rw [classTerms, List.getElem?_map] at found
              obtain ⟨child, selected, rfl⟩ := Option.map_eq_some_iff.mp found
              exact .label symbol inner ⟨size, rank⟩ child (ih indexed _ child selected)

/-- Local source fields need child inverse contracts only below the requested height. -/
theorem field_exact_below [DecidableEq Symbol] (limit : Nat) (recipe : Recipe Symbol)
    (leaves : LeavesBelow limit recipe) (indexed : LeavesIndexed recipe) : ExactBelow limit (field recipe) := by
  intro view wanted bound position
  constructor
  · intro member
    obtain ⟨term, selected, projected⟩ := checked_sound_below limit recipe leaves view wanted bound position member
    refine ⟨term, ?_, projected⟩
    exact RecursiveCallbackAlignment.selects_lookup (fun _ => []) (fun _ => 0) (fun _ => rfl)
      emptyBody empty_equation empty_indexed recipe position term selected indexed
  · rintro ⟨term, selected, projected⟩
    rw [← projected]
    apply certified_complete_below limit recipe position term (lookup_selects recipe indexed position term selected) leaves view
    simpa only [projected] using bound

end MicroCFTA.RecursiveFieldBounds
