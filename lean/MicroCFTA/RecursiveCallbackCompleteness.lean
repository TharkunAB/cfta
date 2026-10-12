import MicroCFTA.RecursiveCallbackTables

/-!
# Complete source recursive callbacks against ordered class tables

The inverse reads only the requested view. Completeness follows the finite
view and recipe syntax, even when a label removes a private choice wrapper.
The root premise is the forward class equation. No inverse premise is used
at recursive occurrences. Finite leaves use only their own proved contracts.
-/
namespace MicroCFTA.RecursiveCallbackCompleteness
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables

/-- Concatenating view forests preserves the maximum height of either side. -/
theorem forest_append (left right : List (Term Symbol)) :
    forestHeight (left ++ right) = max (forestHeight left) (forestHeight right) := by
  induction left with
  | nil => simp [forestHeight]
  | cons first rest ih =>
      change max first.height (forestHeight (rest ++ right)) = max (max first.height (forestHeight rest)) (forestHeight right)
      rw [ih, Nat.max_assoc]

/-- The unfolded height fold has the same append equation. -/
theorem fold_height_append (left right : List (Term Symbol)) :
    (left ++ right).foldr (fun term height => max term.height height) 0 =
      max (left.foldr (fun term height => max term.height height) 0)
        (right.foldr (fun term height => max term.height height) 0) := forest_append left right

/-- The source finite size index has exactly the class interval declared by its plan. -/
theorem static_terms_indexed [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol)
    (plan : SourcePlanPositions.Plan) (sameCount : SourcePlanPositions.count plan = StaticCandidateRanks.cardinality source) :
    FiniteIndex (staticTerms source plan) := by
  intro position
  constructor
  · rintro ⟨term, selected⟩
    change ((SourcePlanPositions.classRanks plan position.size)[position.rank]?).bind
      (StaticCandidateRanks.select source) = some term at selected
    obtain ⟨rank, found, _⟩ := Option.bind_eq_some_iff.mp selected
    exact (List.getElem?_eq_some_iff.mp found).1
  · intro within
    exact SourcePlanPositions.every_class_selection_total plan (StaticCandidateRanks.select source)
      (fun rank bounded => StaticCandidateRanks.select_total source rank (sameCount ▸ bounded)) position within

/-- Ordinary finite producers have the complete local class-index law. -/
theorem finite_static_indexed [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol) :
    FiniteIndex (staticTerms source (staticPlan source)) :=
  static_terms_indexed source (staticPlan source) (static_plan_count source)

/-- Atomic finite producers retain their complete original class interval at size one. -/
theorem atomic_static_indexed [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol) :
    FiniteIndex (staticTerms source (.select (StaticCandidateRanks.cardinality source))) :=
  static_terms_indexed source _ rfl

set_option maxHeartbeats 1000000 in
/-- Every ordered table lookup is returned with a true flag in every source request view. -/
theorem table_complete [DecidableEq Symbol] (environment : Nat → List (EngineTerm Symbol))
    (self : Nat → Nat) (rootCounts : ∀ size, (environment size).length = self size)
    (body : Recipe Symbol)
    (rootEquation : ∀ size, environment size = (classTerms environment body size).map (fun term => .node .recursion [term]))
    (bodyExact : LeavesExact body) (bodyIndexed : LeavesIndexed body)
    (recipe : Recipe Symbol) (leaves : LeavesExact recipe) (indexed : LeavesIndexed recipe)
    (position : Position) (term : EngineTerm Symbol)
    (found : (classTerms environment recipe position.size)[position.rank]? = some term) (view : View) :
    (position, true) ∈ positions self body recipe view (project view term) := by
  cases recipe with
  | finite source =>
      rw [positions]
      exact (leaves view (project view term) position).mpr
        ⟨term, (finite_lookup source indexed position term).mp found, rfl⟩
  | occurrence =>
      change (environment position.size)[position.rank]? = some term at found
      rw [rootEquation, List.getElem?_map] at found
      obtain ⟨child, selected, rfl⟩ := Option.map_eq_some_iff.mp found
      have ih := table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
        body bodyExact bodyIndexed position child selected .whole
      cases view <;> simpa [positions, project, labelled, spine, SupportTerms.applicationLeftChildren,
        SupportTerms.applicationTermChildren] using ih
  | map inner =>
      rw [positions]
      exact table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
        inner leaves indexed position term found view
  | pay inner =>
      cases position with
      | mk size rank =>
          cases size with
          | zero => simp [classTerms] at found
          | succ size =>
              rw [positions]
              exact List.mem_map.mpr ⟨(⟨size, rank⟩, true),
                table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
                  inner leaves indexed ⟨size, rank⟩ term found view, rfl⟩
  | choice left right =>
      by_cases first : position.rank < (classTerms environment left position.size).length
      · rw [classTerms, List.getElem?_append_left (by simpa using first), List.getElem?_map] at found
        obtain ⟨child, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        cases view with
        | whole | spine =>
            simpa [positions, project, spine, SupportTerms.applicationLeftChildren,
              SupportTerms.applicationTermChildren, mem_sorted] using
                table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
                  left leaves.1 indexed.1 position child selected .whole
        | labelled =>
            rw [positions, mem_sorted]
            exact List.mem_append_left _
              (table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
                left leaves.1 indexed.1 position child selected .labelled)
      · rw [classTerms, List.getElem?_append_right (by simpa using Nat.le_of_not_lt first), List.length_map,
          List.getElem?_map] at found
        obtain ⟨child, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        let childPosition : Position := ⟨position.size, position.rank - counts self left position.size⟩
        have selectedLocal : (classTerms environment right childPosition.size)[childPosition.rank]? = some child := by
          simpa [childPosition, class_length environment self rootCounts] using selected
        have offset : RecursiveCheckedRanks.choiceRow [counts self left, counts self right] 1 (childPosition, true) = (position, true) := by
          have lower : counts self left position.size ≤ position.rank := by
            simpa [class_length environment self rootCounts] using Nat.le_of_not_lt first
          simp [RecursiveCheckedRanks.choiceRow, choicePosition, childPosition, Nat.add_sub_of_le lower]
        cases view with
        | whole | spine =>
            simp only [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, Option.getD_none]
            rw [positions, mem_sorted]
            exact List.mem_map.mpr ⟨(childPosition, true),
              table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
                right leaves.2 indexed.2 childPosition child selectedLocal .whole, offset⟩
        | labelled =>
            rw [positions, mem_sorted]
            exact List.mem_append_right _ (List.mem_map.mpr ⟨(childPosition, true),
              table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
                right leaves.2 indexed.2 childPosition child selectedLocal .labelled, offset⟩)
  | ap functions arguments =>
      obtain ⟨first, second, function, argument, rfl, firstFound, secondFound, rfl⟩ :=
        product_lookup environment self rootCounts functions arguments position term found
      cases view with
      | whole =>
          simp only [project, positions, mem_sorted]
          exact RecursiveCheckedRanks.product_complete _ _ _ _ _ _
            (table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
              functions leaves.1 indexed.1 first function firstFound .whole)
            (table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
              arguments leaves.2 indexed.2 second argument secondFound .whole)
      | spine | labelled =>
          simp only [project, labelled, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, Option.getD_some]
          rw [positions.eq_def]
          dsimp only
          rw [mem_sorted]
          split
          · rename_i absent; simp only [List.getLast?_concat] at absent; contradiction
          · rename_i last foundLast
            have same : argument = last := by simpa only [List.getLast?_concat, Option.some.injEq] using foundLast
            subst last
            simpa only [List.dropLast_concat, project, spine] using
              RecursiveCheckedRanks.product_complete (counts self functions) (counts self arguments) _ _ _ _
                (table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
                  functions leaves.1 indexed.1 first function firstFound .spine)
                (table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
                  arguments leaves.2 indexed.2 second argument secondFound .whole)
  | label symbol inner =>
      cases position with
      | mk size rank =>
          cases size with
          | zero => simp [classTerms] at found
          | succ size =>
              rw [classTerms, List.getElem?_map] at found
              obtain ⟨child, selected, rfl⟩ := Option.map_eq_some_iff.mp found
              rw [labelled_source, StaticCandidateRanks.project_user, positions]
              simp only [↓reduceIte]
              exact List.mem_map.mpr ⟨(⟨size, rank⟩, true),
                table_complete environment self rootCounts body rootEquation bodyExact bodyIndexed
                  inner leaves indexed ⟨size, rank⟩ child selected .labelled, rfl⟩
termination_by (forestHeight (project view term), depth recipe)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_all only [labelled_source, depth, project, labelled, spine,
    SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, Option.getD_some, Option.getD_none]
  all_goals simp only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  all_goals try simp only [fold_height_append, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  all_goals first
    | omega
    | cases view <;> simp_all [forestHeight, Term.height] <;> omega

end MicroCFTA.RecursiveCallbackCompleteness
