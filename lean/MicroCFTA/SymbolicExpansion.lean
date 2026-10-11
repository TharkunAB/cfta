import MicroCFTA.SymbolicScope

/-!
# Fresh-variable semantics of symbolic constructor expansion

Each signed guard component has its own constructor language. Expansion
replaces one live term with its ordered children. Fresh variables preserve
the other live values and all existing pending requirements.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Obligation instantiate instantiateMany Satisfies)

/-- One unsigned equality component of a source edge indicator. -/
noncomputable def componentTerms (language : Nat → List (Term Symbol)) (edge : Edge Symbol)
    (classes : List (List (List Nat))) : List (Term Symbol) := by
  classical
  exact ((products language edge.children).map (Term.node edge.symbol)).filter fun term =>
    decide (∀ paths ∈ classes, Symbolic.ClassSatisfied term paths)

/-- The component uses exactly the edge's child domains and equality classes. -/
theorem componentTerms_spec (language : Nat → List (Term Symbol)) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (term : Term Symbol) :
    term ∈ componentTerms language edge classes ↔ ∃ children,
      term = .node edge.symbol children ∧ All₂ (fun node value => value ∈ language node) edge.children children ∧
      ∀ paths ∈ classes, Symbolic.ClassSatisfied term paths := by
  classical
  simp only [componentTerms, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨children, member, same⟩, constraints⟩
    exact ⟨children, same.symm, (mem_products language edge.children children).mp member, constraints⟩
  · rintro ⟨children, same, domains, constraints⟩
    exact ⟨⟨children, (mem_products language edge.children children).mpr domains, same.symm⟩, constraints⟩

/-- An equality component cannot repeat a term when each child language is distinct. -/
theorem componentTerms_nodup (language : Nat → List (Term Symbol))
    (distinct : ∀ node, (language node).Nodup) (edge : Edge Symbol) (classes : List (List (List Nat))) :
    (componentTerms language edge classes).Nodup := by
  classical
  apply List.Pairwise.filter
  apply List.pairwise_map.mpr
  exact (products_nodup language edge.children (fun node _ => distinct node)).imp
    (fun different same => different (Term.node.inj same).2)

/-- The selected variable receives the component language; other variables keep their domains. -/
noncomputable def componentChoices (language : Nat → List (Term Symbol)) (name : Nat)
    (edge : Edge Symbol) (classes : List (List (List Nat))) (entry : Nat × Nat) : List (Term Symbol) :=
  if entry.1 = name then componentTerms language edge classes else language entry.2

/-- Candidate tuples distinguish variables even when they share one graph identity. -/
noncomputable def componentSolutions (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (name : Nat) (edge : Edge Symbol) (classes : List (List (List Nat))) : List (List (Term Symbol)) := by
  classical
  exact (products (componentChoices language name edge classes) problem.domains).filter
    fun values => decide (LiveSolution problem values)

/-- The selected coordinate uses a raw guard component before signed cancellation. -/
def ComponentHolds (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (name : Nat) (edge : Edge Symbol) (classes : List (List (List Nat))) (assignment : Nat → Term Symbol) : Prop :=
  (∀ entry ∈ problem.domains, assignment entry.1 ∈ componentChoices language name edge classes entry) ∧
    BindingsHold assignment problem.bindings ∧ ∀ requirement ∈ problem.obligations, Satisfies assignment requirement

/-- Matching tuples turn coordinate membership into a valuation predicate. -/
theorem matching_products_iff (choices : (Nat × Nat) → List (Term Symbol)) (assignment : Nat → Term Symbol)
    (domains : List (Nat × Nat)) (values : List (Term Symbol)) (matching : TupleMatches assignment domains values) :
    values ∈ products choices domains ↔ ∀ entry ∈ domains, assignment entry.1 ∈ choices entry := by
  rw [mem_products]
  induction matching with
  | nil =>
      constructor
      · intro _ _ member; cases member
      · intro _; exact .nil
  | @cons entry value entries values same tail ih =>
      constructor
      · intro related
        cases related with
        | cons first rest =>
            intro candidate member
            rcases List.mem_cons.mp member with rfl | member
            · simpa only [same] using first
            · exact ih.mp rest candidate member
      · intro valid
        exact .cons (by simpa only [same] using valid entry (by simp))
          (ih.mpr (fun candidate member => valid candidate (by simp [member])))

/-- The finite component list is exactly its live valuation predicate. -/
theorem componentSolutions_spec (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (name : Nat) (edge : Edge Symbol) (classes : List (List (List Nat))) (values : List (Term Symbol)) :
    values ∈ componentSolutions language problem name edge classes ↔ ∃ assignment,
      TupleMatches assignment problem.domains values ∧ ComponentHolds language problem name edge classes assignment := by
  classical
  simp only [componentSolutions, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨candidate, assignment, matching, bindings, constraints⟩
    exact ⟨assignment, matching, (matching_products_iff _ assignment _ _ matching).mp candidate, bindings, constraints⟩
  · rintro ⟨assignment, matching, domains, bindings, constraints⟩
    exact ⟨(matching_products_iff _ assignment _ _ matching).mpr domains, assignment, matching, bindings, constraints⟩

/-- Component tuples are distinct before signed coefficients are applied. -/
theorem componentSolutions_nodup (language : Nat → List (Term Symbol))
    (distinct : ∀ node, (language node).Nodup) (problem : Problem Symbol)
    (name : Nat) (edge : Edge Symbol) (classes : List (List (List Nat))) :
    (componentSolutions language problem name edge classes).Nodup := by
  classical
  apply List.Pairwise.filter
  apply products_nodup
  intro entry _
  dsimp only [componentChoices]
  split
  · exact componentTerms_nodup language distinct edge classes
  · exact distinct entry.2

/-- Assign the fresh consecutive names without changing older names. -/
def fillFresh (assignment : Nat → Term Symbol) (next : Nat) (values : List (Term Symbol)) (name : Nat) : Term Symbol :=
  if next ≤ name then (values[name - next]?).getD (assignment name) else assignment name

/-- Fresh child assignment preserves all names below its starting point. -/
theorem fillFresh_old (assignment : Nat → Term Symbol) (next : Nat) (values : List (Term Symbol))
    (name : Nat) (older : name < next) : fillFresh assignment next values name = assignment name := by
  simp only [fillFresh, ite_eq_right (by omega : ¬next ≤ name)]

/-- The fresh names read back the complete ordered child tuple. -/
theorem fillFresh_values (assignment : Nat → Term Symbol) (next : Nat) (values : List (Term Symbol)) :
    (List.range' next values.length).map (fillFresh assignment next values) = values := by
  apply List.ext_getElem
  · simp
  · intro index firstBound secondBound
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, fillFresh, Nat.le_add_right,
      ite_true, Nat.add_sub_cancel_left, List.getElem?_eq_getElem secondBound, Option.getD_some]

/-- A list of variable fragments instantiates to the same ordered list of values. -/
theorem instantiate_variables (assignment : Nat → Term Symbol) (names : List Nat) :
    instantiateMany assignment (names.map Fragment.var) = names.map assignment := by
  induction names with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, instantiateMany, instantiate, ih]

/-- The source's exact context for a selected constructor. -/
def expansionContext (problem : Problem Symbol) (edge : Edge Symbol) : Fragment Symbol :=
  .constructor edge.symbol ((List.range' problem.nextVariable edge.children.length).map Fragment.var)

/-- The source's exact sorted domain, binding, and requirement update. -/
def expandedProblem (problem : Problem Symbol) (name : Nat) (edge : Edge Symbol)
    (classes : List (List (List Nat))) : Problem Symbol :=
  {problem with
    domains := (((List.range' problem.nextVariable edge.children.length).zip edge.children) ++ delete problem.domains name).mergeSort
      (fun left right => left.1 ≤ right.1)
    bindings := insert problem.bindings name (expansionContext problem edge)
    nextVariable := problem.nextVariable + edge.children.length
    obligations := Symbolic.edgeObligations (expansionContext problem edge) classes ++ problem.obligations}

/-- Fresh child values reconstruct their exact constructor term. -/
theorem expansion_instantiates (problem : Problem Symbol) (edge : Edge Symbol)
    (assignment : Nat → Term Symbol) (values : List (Term Symbol)) (length : values.length = edge.children.length) :
    instantiate (fillFresh assignment problem.nextVariable values) (expansionContext problem edge) = .node edge.symbol values := by
  simp only [expansionContext, instantiate, instantiate_variables, ← length, fillFresh_values]

/-- The expanded binding fixes the removed variable to its constructor context. -/
theorem expanded_binding_iff (problem : Problem Symbol) (empty : problem.bindings = [])
    (name : Nat) (edge : Edge Symbol) (classes : List (List (List Nat))) (assignment : Nat → Term Symbol) :
    BindingsHold assignment (expandedProblem problem name edge classes).bindings ↔
      assignment name = instantiate assignment (expansionContext problem edge) := by
  simp [expandedProblem, empty, insert, delete, BindingsHold]

/-- Domain membership is exactly a fresh child coordinate or an unchanged old coordinate. -/
theorem expanded_domain_member (problem : Problem Symbol) (name : Nat) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (entry : Nat × Nat) :
    entry ∈ (expandedProblem problem name edge classes).domains ↔
      entry ∈ (List.range' problem.nextVariable edge.children.length).zip edge.children ∨
        entry ∈ problem.domains ∧ entry.1 ≠ name := by
  simp [expandedProblem, delete]

/-- Zipped child names give exactly the ordered child-domain requirements. -/
theorem zipped_domains_iff (language : Nat → List (Term Symbol)) (assignment : Nat → Term Symbol)
    (names nodes : List Nat) (length : names.length = nodes.length) :
    (∀ entry ∈ names.zip nodes, assignment entry.1 ∈ language entry.2) ↔
      All₂ (fun node value => value ∈ language node) nodes (names.map assignment) := by
  induction names generalizing nodes with
  | nil =>
      have empty : nodes = [] := List.length_eq_zero_iff.mp length.symm
      subst nodes
      constructor
      · intro _; exact .nil
      · intro _ _ member; cases member
  | cons name names ih =>
      cases nodes with
      | nil => simp at length
      | cons node nodes =>
          have tailLength : names.length = nodes.length := by simpa using length
          constructor
          · intro holds
            exact .cons (holds (name, node) (by simp))
              ((ih nodes tailLength).mp (fun entry member => holds entry (by simp [member])))
          · intro related
            cases related with
            | cons first rest =>
                intro entry member
                rcases List.mem_cons.mp member with rfl | member
                · exact first
                · exact (ih nodes tailLength).mpr rest entry member

/-- An expanded solution has one exact constructor, its child domains, and the old requirements. -/
theorem expanded_solution_iff (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (empty : problem.bindings = []) (name : Nat) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (assignment : Nat → Term Symbol) :
    ProblemHolds (fun node term => term ∈ language node) assignment (expandedProblem problem name edge classes) ↔
      (∀ entry ∈ problem.domains, entry.1 ≠ name → assignment entry.1 ∈ language entry.2) ∧
      assignment name = .node edge.symbol ((List.range' problem.nextVariable edge.children.length).map assignment) ∧
      All₂ (fun node value => value ∈ language node) edge.children
        ((List.range' problem.nextVariable edge.children.length).map assignment) ∧
      (∀ paths ∈ classes, Symbolic.ClassSatisfied (assignment name) paths) ∧
      ∀ requirement ∈ problem.obligations, Satisfies assignment requirement := by
  have instantiated : instantiate assignment (expansionContext problem edge) =
      .node edge.symbol ((List.range' problem.nextVariable edge.children.length).map assignment) := by
    simp only [expansionContext, instantiate, instantiate_variables]
  constructor
  · rintro ⟨domains, bindings, constraints⟩
    have binding := (expanded_binding_iff problem empty name edge classes assignment).mp bindings
    refine ⟨?_, binding.trans instantiated, ?_, ?_, ?_⟩
    · intro entry member other
      exact domains entry ((expanded_domain_member problem name edge classes entry).mpr (Or.inr ⟨member, other⟩))
    · apply (zipped_domains_iff language assignment _ _ (by simp)).mp
      intro entry member
      exact domains entry ((expanded_domain_member problem name edge classes entry).mpr (Or.inl member))
    · have guards := (Symbolic.edgeObligations_correct (expansionContext problem edge) assignment classes).mp
        (fun requirement member => constraints requirement (List.mem_append_left _ member))
      simpa only [← binding] using guards
    · intro requirement member
      exact constraints requirement (List.mem_append_right _ member)
  · rintro ⟨remaining, binding, children, guards, constraints⟩
    have binding' := binding.trans instantiated.symm
    refine ⟨?_, (expanded_binding_iff problem empty name edge classes assignment).mpr binding', ?_⟩
    · intro entry member
      rcases (expanded_domain_member problem name edge classes entry).mp member with fresh | old
      · exact (zipped_domains_iff language assignment _ _ (by simp)).mpr children entry fresh
      · exact remaining entry old.1 old.2
    · intro requirement member
      rcases List.mem_append.mp member with new | old
      · exact (Symbolic.edgeObligations_correct (expansionContext problem edge) assignment classes).mpr
          (by simpa only [← binding'] using guards) requirement new
      · exact constraints requirement old

/-- Projection of an expanded solution satisfies the selected raw edge component. -/
theorem expansion_projects_component (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (empty : problem.bindings = []) (name : Nat) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (assignment : Nat → Term Symbol)
    (valid : ProblemHolds (fun node term => term ∈ language node) assignment (expandedProblem problem name edge classes)) :
    ComponentHolds language problem name edge classes assignment := by
  obtain ⟨remaining, binding, children, guards, constraints⟩ :=
    (expanded_solution_iff language problem empty name edge classes assignment).mp valid
  refine ⟨?_, ?_, constraints⟩
  · intro entry member
    unfold componentChoices
    split
    · rename_i same
      rw [same]
      exact (componentTerms_spec language edge classes (assignment name)).mpr ⟨_, binding, children, guards⟩
    · exact remaining entry member ‹entry.1 ≠ name›
  · simp [BindingsHold, empty]

/-- Every old component solution extends to a valid fresh-child solution with the same live values. -/
theorem component_extends_expansion (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (empty : problem.bindings = []) (within : ProblemScoped problem)
    (fresh : ∀ entry ∈ problem.domains, entry.1 < problem.nextVariable)
    (name node : Nat) (selected : (name, node) ∈ problem.domains) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (assignment : Nat → Term Symbol)
    (valid : ComponentHolds language problem name edge classes assignment) :
    ∃ extended, (∀ entry ∈ problem.domains, extended entry.1 = assignment entry.1) ∧
      ProblemHolds (fun graph term => term ∈ language graph) extended (expandedProblem problem name edge classes) := by
  have selectedValue : assignment name ∈ componentTerms language edge classes := by
    simpa only [componentChoices, ite_true] using valid.1 (name, node) selected
  obtain ⟨values, termSame, children, guards⟩ := (componentTerms_spec language edge classes (assignment name)).mp selectedValue
  let extended := fillFresh assignment problem.nextVariable values
  have agreement : ∀ entry ∈ problem.domains, extended entry.1 = assignment entry.1 := by
    intro entry member
    exact fillFresh_old assignment problem.nextVariable values entry.1 (fresh entry member)
  have valuesRead : (List.range' problem.nextVariable edge.children.length).map extended = values := by
    rw [children.length_eq]
    exact fillFresh_values assignment problem.nextVariable values
  refine ⟨extended, agreement, (expanded_solution_iff language problem empty name edge classes extended).mpr ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro entry member other
    rw [agreement entry member]
    simpa only [componentChoices, ite_eq_right other] using valid.1 entry member
  · rw [valuesRead, agreement (name, node) selected]
    exact termSame
  · simpa only [valuesRead] using children
  · simpa only [agreement (name, node) selected] using guards
  · intro requirement member
    apply (obligation_scoped_congr (fun key => key ∈ problem.domains.map Prod.fst) extended assignment
      (by
        intro key keyMember
        obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp keyMember
        subst key
        exact agreement entry entryMember) requirement (within requirement member)).mpr
    exact valid.2.2 requirement member

/-- Every fresh name has a live domain entry after expansion. -/
theorem expansion_name_live (problem : Problem Symbol) (name : Nat) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (key : Nat)
    (member : key ∈ List.range' problem.nextVariable edge.children.length) :
    ∃ entry ∈ (expandedProblem problem name edge classes).domains, entry.1 = key := by
  have inKeys : key ∈ ((List.range' problem.nextVariable edge.children.length).zip edge.children).map Prod.fst := by
    simpa only [List.map_fst_zip (by simp : (List.range' problem.nextVariable edge.children.length).length ≤ edge.children.length)] using member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp inKeys
  exact ⟨entry, (expanded_domain_member problem name edge classes entry).mpr (Or.inl entryMember), same⟩

/-- Equal expanded coordinates reconstruct equal values at every original live name. -/
theorem expanded_determines_original (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (empty : problem.bindings = []) (name : Nat) (edge : Edge Symbol)
    (classes : List (List (List Nat))) (first second : Nat → Term Symbol)
    (firstValid : ProblemHolds (fun node term => term ∈ language node) first (expandedProblem problem name edge classes))
    (secondValid : ProblemHolds (fun node term => term ∈ language node) second (expandedProblem problem name edge classes))
    (agree : ∀ entry ∈ (expandedProblem problem name edge classes).domains, first entry.1 = second entry.1) :
    ∀ entry ∈ problem.domains, first entry.1 = second entry.1 := by
  have firstBinding := (expanded_solution_iff language problem empty name edge classes first).mp firstValid |>.2.1
  have secondBinding := (expanded_solution_iff language problem empty name edge classes second).mp secondValid |>.2.1
  have childrenSame : (List.range' problem.nextVariable edge.children.length).map first =
      (List.range' problem.nextVariable edge.children.length).map second := by
    apply List.map_inj_left.mpr
    intro key member
    obtain ⟨entry, entryMember, same⟩ := expansion_name_live problem name edge classes key member
    simpa only [same] using agree entry entryMember
  intro entry member
  by_cases selected : entry.1 = name
  · rw [selected, firstBinding, secondBinding, childrenSame]
  · exact agree entry ((expanded_domain_member problem name edge classes entry).mpr (Or.inr ⟨member, selected⟩))

/-- Equal original coordinates determine all fresh ordered children and all retained coordinates. -/
theorem original_determines_expanded (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (empty : problem.bindings = []) (name node : Nat) (selected : (name, node) ∈ problem.domains)
    (edge : Edge Symbol) (classes : List (List (List Nat))) (first second : Nat → Term Symbol)
    (firstValid : ProblemHolds (fun graph term => term ∈ language graph) first (expandedProblem problem name edge classes))
    (secondValid : ProblemHolds (fun graph term => term ∈ language graph) second (expandedProblem problem name edge classes))
    (agree : ∀ entry ∈ problem.domains, first entry.1 = second entry.1) :
    ∀ entry ∈ (expandedProblem problem name edge classes).domains, first entry.1 = second entry.1 := by
  have firstBinding := (expanded_solution_iff language problem empty name edge classes first).mp firstValid |>.2.1
  have secondBinding := (expanded_solution_iff language problem empty name edge classes second).mp secondValid |>.2.1
  have childrenSame := (Term.node.inj (firstBinding.symm.trans ((agree (name, node) selected).trans secondBinding))).2
  intro entry member
  rcases (expanded_domain_member problem name edge classes entry).mp member with new | old
  · exact List.map_inj_left.mp childrenSame entry.1 (List.of_mem_zip new).1
  · exact agree entry old.1

/-- The exact source constructor expansion preserves the finite count of its raw equality component. -/
theorem expand_component_count (language : Nat → List (Term Symbol))
    (distinct : ∀ graph, (language graph).Nodup) (problem : Problem Symbol)
    (empty : problem.bindings = []) (within : ProblemScoped problem)
    (fresh : ∀ entry ∈ problem.domains, entry.1 < problem.nextVariable)
    (name node : Nat) (selected : (name, node) ∈ problem.domains) (edge : Edge Symbol)
    (classes : List (List (List Nat))) :
    (componentSolutions language problem name edge classes).length =
      solutionCount language (expandedProblem problem name edge classes) := by
  let expanded := expandedProblem problem name edge classes
  let relation := fun old new => ∃ assignment,
    TupleMatches assignment problem.domains old ∧ TupleMatches assignment expanded.domains new ∧
      ProblemHolds (fun graph term => term ∈ language graph) assignment expanded
  have forward : ∀ old ∈ componentSolutions language problem name edge classes,
      ∃ new ∈ solutionTuples language expanded, relation old new := by
    intro old member
    obtain ⟨assignment, matching, valid⟩ := (componentSolutions_spec language problem name edge classes old).mp member
    obtain ⟨extended, agreement, extendedValid⟩ :=
      component_extends_expansion language problem empty within fresh name node selected edge classes assignment valid
    let new := expanded.domains.map fun entry => extended entry.1
    have oldMatching : TupleMatches extended problem.domains old := by
      apply (tupleMatches_iff ..).mpr
      exact ((tupleMatches_iff ..).mp matching).trans (List.map_inj_left.mpr (fun entry member => (agreement entry member).symm))
    have newMatching : TupleMatches extended expanded.domains new := (tupleMatches_iff ..).mpr rfl
    exact ⟨new, (solutionTuples_spec language expanded new).mpr ⟨extended, newMatching, extendedValid⟩,
      extended, oldMatching, newMatching, extendedValid⟩
  have backward : ∀ new ∈ solutionTuples language expanded,
      ∃ old ∈ componentSolutions language problem name edge classes, relation old new := by
    intro new member
    obtain ⟨assignment, matching, valid⟩ := (solutionTuples_spec language expanded new).mp member
    let old := problem.domains.map fun entry => assignment entry.1
    have oldMatching : TupleMatches assignment problem.domains old := (tupleMatches_iff ..).mpr rfl
    exact ⟨old, (componentSolutions_spec language problem name edge classes old).mpr
      ⟨assignment, oldMatching, expansion_projects_component language problem empty name edge classes assignment valid⟩,
      assignment, oldMatching, matching, valid⟩
  have oldUnique : ∀ first ∈ componentSolutions language problem name edge classes,
      ∀ second ∈ componentSolutions language problem name edge classes,
      ∀ new ∈ solutionTuples language expanded, relation first new → relation second new → first = second := by
    intro first _ second _ new _ ⟨a, am, an, av⟩ ⟨b, bm, bn, bv⟩
    have same := expanded_determines_original language problem empty name edge classes a b av bv
      (matching_same_values a b expanded.domains new an bn)
    exact ((tupleMatches_iff ..).mp am).trans ((List.map_inj_left.mpr same).trans ((tupleMatches_iff ..).mp bm).symm)
  have newUnique : ∀ first ∈ solutionTuples language expanded, ∀ second ∈ solutionTuples language expanded,
      ∀ old ∈ componentSolutions language problem name edge classes, relation old first → relation old second → first = second := by
    intro first _ second _ old _ ⟨a, am, an, av⟩ ⟨b, bm, bn, bv⟩
    have same := original_determines_expanded language problem empty name node selected edge classes a b av bv
      (matching_same_values a b problem.domains old am bm)
    exact ((tupleMatches_iff ..).mp an).trans ((List.map_inj_left.mpr same).trans ((tupleMatches_iff ..).mp bn).symm)
  apply Nat.le_antisymm
  · exact relation_cardinality_le _ _ [] (componentSolutions_nodup language distinct problem name edge classes) relation forward oldUnique
  · exact relation_cardinality_le _ _ [] (solutionTuples_nodup language distinct expanded) (fun new old => relation old new) backward newUnique

end MicroCFTA.SymbolicDriver
