import MicroCFTA.SymbolicFuel

/-!
# Scope of every recursive source normalization input

Raw solve inputs can retain one eliminated variable as a binding. Pending
requirements can read that binding or any live domain. Every recursive caller
must preserve this scope before alpha-normalization.
-/
namespace MicroCFTA.SymbolicDriver
open Symbolic (Fragment Obligation)

/-- The complete raw problem scope before the next normalization. -/
def InputScope (problem : Problem Symbol) : Prop :=
  BindingsScoped problem.bindings (fun name => name ∈ problem.domains.map Prod.fst) ∧
    ∀ requirement ∈ problem.obligations,
      ObligationInScope (BoundOrLive problem.bindings (fun name => name ∈ problem.domains.map Prod.fst)) requirement

/-- Every key present in a finite map has a successful first-entry lookup. -/
theorem lookup_exists (entries : List (Nat × Value)) (name : Nat) (present : name ∈ entries.map Prod.fst) :
    ∃ value, lookup entries name = some value := by
  induction entries with
  | nil => cases present
  | cons first rest ih =>
      by_cases same : first.1 = name
      · exact ⟨first.2, by simp [lookup, same]⟩
      · have tail : name ∈ rest.map Prod.fst := by simpa [List.mem_cons, Ne.symm same] using present
        obtain ⟨value, success⟩ := ih tail
        exact ⟨value, by simpa [lookup, same] using success⟩

/-- The source's compact renaming map covers every live domain name. -/
theorem live_renaming_lookup (problem : Problem Symbol) (name : Nat) (live : name ∈ problem.domains.map Prod.fst) :
    ∃ new, lookup (problem.domains.zipIdx.map fun (entry, index) => (entry.1, index)) name = some new := by
  apply lookup_exists
  have keys : ((problem.domains.zipIdx.map fun (entry, index) => (entry.1, index)).map Prod.fst) = problem.domains.map Prod.fst := by
    have same := congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 problem.domains)
    simpa only [List.map_map, Function.comp_def] using same
  simpa only [keys] using live

/-- Weakening a variable scope preserves all context occurrences. -/
theorem scope_mono (first second : Nat → Prop) (containment : ∀ name, first name → second name)
    (fragment : Fragment Symbol) (within : InScope first fragment) : InScope second fragment :=
  fun name occursName => containment name (within name occursName)

/-- Weakening a variable scope preserves path existence and equality requirements. -/
theorem obligationScope_mono (first second : Nat → Prop) (containment : ∀ name, first name → second name)
    (requirement : Obligation Symbol) (within : ObligationInScope first requirement) : ObligationInScope second requirement := by
  cases requirement with
  | «exists» target => exact scope_mono first second containment target.fragment within
  | equal left right => exact ⟨scope_mono first second containment left.fragment within.1,
      scope_mono first second containment right.fragment within.2⟩

/-- A normalized problem already satisfies the raw caller scope. -/
theorem normal_inputScope (problem : Problem Symbol) (normal : NormalProblem problem) : InputScope problem := by
  constructor
  · intro name fragment found
    simp [lookup, normal.2.1] at found
  · intro requirement member
    exact obligationScope_mono _ _ (fun name live => Or.inr live) requirement (normal.2.2.2 requirement member)

/-- Raw caller scope supplies the full normalizer's map-based scope assumptions. -/
theorem scoped_normalize_total [DecidableEq Symbol] [Ord Symbol]
    (problem : Problem Symbol) (weight : Nat → Nat) (budget : BindingBudget weight problem.bindings)
    (within : InputScope problem) (fuel : Nat) (bounded : 2 * obligationsWork weight problem.obligations + 1 ≤ fuel) :
    ∃ output, normalize fuel problem = .ok output := by
  apply normalize_total weight problem budget ?_ ?_ fuel bounded
  · intro name fragment found
    exact scope_mono _ _ (fun key safe => safe.elim Or.inl (fun live => Or.inr (live_renaming_lookup problem key live)))
      fragment (within.1 name fragment found)
  · intro requirement member
    exact obligationScope_mono _ _ (fun key safe => safe.elim Or.inl (fun live => Or.inr (live_renaming_lookup problem key live)))
      requirement (within.2 requirement member)

/-- Every edge path requirement reads only its shared constructor context. -/
theorem edgeObligations_scope (allowed : Nat → Prop) (context : Fragment Symbol) (within : InScope allowed context)
    (classes : List (List (List Nat))) : ∀ requirement ∈ Symbolic.edgeObligations context classes,
      ObligationInScope allowed requirement := by
  intro requirement member
  obtain ⟨paths, _, pathMember⟩ := List.mem_flatMap.mp member
  cases paths with
  | nil => cases pathMember
  | cons first rest =>
      rcases List.mem_cons.mp pathMember with rfl | member
      · exact within
      · obtain ⟨path, _, same⟩ := List.mem_map.mp member
        subst requirement
        exact ⟨within, within⟩

/-- The complete source edge problem satisfies every normalization caller invariant. -/
theorem edgeProblem_normal (edge : Edge Symbol) (classes : List (List (List Nat))) : NormalProblem (edgeProblem edge classes) := by
  refine ⟨(edgeProblem_admissible edge classes).1, rfl, ?_, ?_⟩
  · intro entry member
    have keyPresent : entry.1 ∈ (edgeProblem edge classes).domains.map Prod.fst := List.mem_map.mpr ⟨entry, member, rfl⟩
    rw [edgeProblem_names] at keyPresent
    exact List.mem_range.mp keyPresent
  · apply edgeObligations_scope
    intro name occurrence
    change occursMany name ((List.range edge.children.length).map Fragment.var) = true at occurrence
    rw [edgeProblem_names]
    exact (occursMany_variables name _).mp occurrence

/-- A single binding whose context uses live names satisfies raw binding scope. -/
theorem single_binding_scope (problem : Problem Symbol) (name : Nat) (fragment : Fragment Symbol)
    (single : problem.bindings = [(name, fragment)])
    (within : InScope (fun key => key ∈ problem.domains.map Prod.fst) fragment) :
    BindingsScoped problem.bindings (fun key => key ∈ problem.domains.map Prod.fst) := by
  intro key context found
  have stored := lookup_member problem.bindings key context found
  simp only [single, List.mem_singleton, Prod.mk.injEq] at stored
  obtain ⟨rfl, rfl⟩ := stored
  exact scope_mono _ _ (fun _ live => Or.inr live) context within

/-- Original names survive merging as a live domain or the one stored binding. -/
theorem merged_name_scope (problem : Problem Symbol) (empty : problem.bindings = [])
    (left right common : Nat) (name : Nat) (present : name ∈ problem.domains.map Prod.fst) :
    BoundOrLive (mergedProblem problem left right common).bindings
      (fun key => key ∈ (mergedProblem problem left right common).domains.map Prod.fst) name := by
  by_cases atLeft : name = left
  · apply Or.inl
    simp [mergedProblem, empty, insert, delete, lookup, atLeft]
  · by_cases atRight : name = right
    · apply Or.inr
      exact List.mem_map.mpr ⟨(right, common), merged_common_member problem left right common, atRight.symm⟩
    · obtain ⟨entry, member, same⟩ := List.mem_map.mp present
      apply Or.inr
      exact List.mem_map.mpr ⟨entry, merged_domain_member problem left right common entry member
        (by simpa only [same] using atLeft) (by simpa only [same] using atRight), same⟩

/-- The exact variable-merge input retains complete raw scope for the next solve call. -/
theorem mergedProblem_inputScope (problem : Problem Symbol) (normal : NormalProblem problem) (left right common : Nat) :
    InputScope (mergedProblem problem left right common) := by
  constructor
  · apply single_binding_scope _ left (.var right) (by simp [mergedProblem, normal.2.1, insert, delete])
    intro name occurrence
    have same : name = right := by simpa only [occurs, beq_iff_eq] using occurrence
    exact List.mem_map.mpr ⟨(right, common), merged_common_member problem left right common, same.symm⟩
  · intro requirement member
    exact obligationScope_mono _ _ (merged_name_scope problem normal.2.1 left right common)
      requirement (normal.2.2.2 requirement member)

/-- Original names survive expansion as a retained domain or the constructor binding. -/
theorem expanded_name_scope (problem : Problem Symbol) (empty : problem.bindings = []) (name : Nat)
    (edge : Edge Symbol) (classes : List (List (List Nat))) (key : Nat) (present : key ∈ problem.domains.map Prod.fst) :
    BoundOrLive (expandedProblem problem name edge classes).bindings
      (fun variableName => variableName ∈ (expandedProblem problem name edge classes).domains.map Prod.fst) key := by
  by_cases selected : key = name
  · apply Or.inl
    simp [expandedProblem, empty, insert, delete, lookup, selected]
  · obtain ⟨entry, member, same⟩ := List.mem_map.mp present
    apply Or.inr
    exact List.mem_map.mpr ⟨entry, (expanded_domain_member problem name edge classes entry).mpr
      (Or.inr ⟨member, by simpa only [same] using selected⟩), same⟩

/-- The exact constructor expansion input retains complete raw scope for the next solve call. -/
theorem expandedProblem_inputScope (problem : Problem Symbol) (normal : NormalProblem problem) (name : Nat)
    (edge : Edge Symbol) (classes : List (List (List Nat))) : InputScope (expandedProblem problem name edge classes) := by
  have contextScope : InScope (fun key => key ∈ (expandedProblem problem name edge classes).domains.map Prod.fst)
      (expansionContext problem edge) := by
    intro key occurrence
    change occursMany key ((List.range' problem.nextVariable edge.children.length).map Fragment.var) = true at occurrence
    obtain ⟨entry, member, same⟩ := expansion_name_live problem name edge classes key ((occursMany_variables key _).mp occurrence)
    exact List.mem_map.mpr ⟨entry, member, same⟩
  constructor
  · exact single_binding_scope _ name (expansionContext problem edge)
      (by simp [expandedProblem, normal.2.1, insert, delete]) contextScope
  · intro requirement member
    rcases List.mem_append.mp member with new | old
    · exact edgeObligations_scope _ _ (scope_mono _ _ (fun _ live => Or.inr live) _ contextScope) classes requirement new
    · exact obligationScope_mono _ _ (expanded_name_scope problem normal.2.1 name edge classes)
        requirement (normal.2.2.2 requirement old)

/-- Pairwise child equations retain the scope of both constructor contexts. -/
theorem child_equations_scope (allowed : Nat → Prop) (children others : List (Fragment Symbol))
    (first : ∀ child ∈ children, InScope allowed child) (second : ∀ other ∈ others, InScope allowed other) :
    ∀ requirement ∈ List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others,
      ObligationInScope allowed requirement := by
  induction children generalizing others with
  | nil => intro requirement member; cases member
  | cons child rest ih =>
      cases others with
      | nil => intro requirement member; cases member
      | cons other tail =>
          intro requirement member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨first child (by simp), second other (by simp)⟩
          · exact ih tail (fun item present => first item (by simp [present]))
              (fun item present => second item (by simp [present])) requirement member

/-- Constructor decomposition creates another scoped problem with the same normalized domain shape. -/
theorem normal_children (problem : Problem Symbol) (normal : NormalProblem problem)
    (symbol : Symbol) (children others : List (Fragment Symbol))
    (first : InScope (fun key => key ∈ problem.domains.map Prod.fst) (.constructor symbol children))
    (second : InScope (fun key => key ∈ problem.domains.map Prod.fst) (.constructor symbol others)) :
    NormalProblem {problem with
      obligations := List.zipWith (fun a b => Obligation.equal ⟨a, []⟩ ⟨b, []⟩) children others ++ problem.obligations} := by
  refine ⟨normal.1, normal.2.1, normal.2.2.1, ?_⟩
  intro requirement member
  rcases List.mem_append.mp member with new | old
  · exact child_equations_scope _ children others (constructor_child_scope _ symbol children first)
      (constructor_child_scope _ symbol others second) requirement new
  · exact normal.2.2.2 requirement old

/-- An empty binding map has unit variable weights and a strict finite substitution budget. -/
theorem empty_binding_budget (problem : Problem Symbol) (empty : problem.bindings = []) :
    BindingBudget (fun _ => 1) problem.bindings := by
  refine ⟨fun _ => Nat.zero_lt_one, ?_⟩
  intro name fragment found
  simp [lookup, empty] at found

end MicroCFTA.SymbolicDriver
