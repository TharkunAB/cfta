import MicroCFTA.SymbolicProgress
import MicroCFTA.SymbolicMeaning

/-!
# Finite live-assignment semantics of symbolic problems

A solution is indexed by one term for each live domain. Eliminated variables
are existentially reconstructed from bindings. They add no independent
choice. The finite candidate tuples come from the graph languages.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment instantiate instantiateMany Satisfies)

/-- The ordered tuple records the valuation of every live domain. -/
def TupleMatches (assignment : Nat → Term Symbol) (domains : List (Nat × Nat))
    (values : List (Term Symbol)) : Prop :=
  All₂ (fun entry value => assignment entry.1 = value) domains values

/-- A tuple is valid when its live values admit bindings and all pending constraints. -/
def LiveSolution (problem : Problem Symbol) (values : List (Term Symbol)) : Prop :=
  ∃ assignment, TupleMatches assignment problem.domains values ∧ BindingsHold assignment problem.bindings ∧
    ∀ obligation ∈ problem.obligations, Satisfies assignment obligation

/-- Candidates use the original ordered list of domain languages. -/
def candidateTuples (language : Nat → List (Term Symbol)) (domains : List (Nat × Nat)) : List (List (Term Symbol)) :=
  products language (domains.map Prod.snd)

/-- Filter the finite candidate tuples by their independent logical solution predicate. -/
noncomputable def solutionTuples (language : Nat → List (Term Symbol)) (problem : Problem Symbol) : List (List (Term Symbol)) := by
  classical
  exact (candidateTuples language problem.domains).filter fun values => decide (LiveSolution problem values)

/-- Count finite live-domain assignments, including all free domains. -/
noncomputable def solutionCount (language : Nat → List (Term Symbol)) (problem : Problem Symbol) : Nat :=
  (solutionTuples language problem).length

/-- A tuple match contains exactly the ordered live values. -/
theorem tupleMatches_iff (assignment : Nat → Term Symbol) (domains : List (Nat × Nat)) (values : List (Term Symbol)) :
    TupleMatches assignment domains values ↔ values = domains.map (fun entry => assignment entry.1) := by
  constructor
  · intro related
    exact all₂_functional _ _ _ (related.imp fun _ _ same => same.symm)
  · intro same
    subst values
    induction domains with
    | nil => exact .nil
    | cons first rest ih => exact .cons rfl ih

/-- Reading an indexed entry returns the same original domain. -/
theorem zipIdx_lookup (entries : List Value) (entry : Value) (index : Nat)
    (member : (entry, index) ∈ entries.zipIdx) : entries[index]? = some entry := by
  obtain ⟨position, bound, same⟩ := List.mem_iff_getElem.mp member
  have originalBound : position < entries.length := by simpa using bound
  have equal : entries[position] = entry ∧ position = index := by simpa only [List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq] using same
  rcases equal with ⟨rfl, rfl⟩
  exact List.getElem?_eq_getElem originalBound

/-- Compact agreement preserves every tuple coordinate, not only its length. -/
theorem tuple_renaming_semantics (old compact : Nat → Term Symbol) (domains : List (Nat × Nat))
    (agree : CompactAgreement old compact domains) (values : List (Term Symbol)) :
    TupleMatches old domains values ↔
      TupleMatches compact (domains.zipIdx.map fun (entry, new) => (new, entry.2)) values := by
  rw [tupleMatches_iff, tupleMatches_iff]
  have oldMap : domains.map (fun entry => old entry.1) =
      domains.zipIdx.map (fun indexed => old indexed.1.1) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map fun entry => old entry.1) (List.zipIdx_map_fst 0 domains).symm
  rw [oldMap]
  have sameMaps : domains.zipIdx.map (fun indexed => old indexed.1.1) =
      (domains.zipIdx.map fun (entry, new) => (new, entry.2)).map (fun entry => compact entry.1) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro indexed member
    exact agree indexed.1 indexed.2 member
  rw [sameMaps]

/-- Construct the compact valuation from an existing original valuation. -/
def compactValuation (old : Nat → Term Symbol) (domains : List (Nat × Nat)) (index : Nat) : Term Symbol :=
  match domains[index]? with
  | none => old 0
  | some entry => old entry.1

/-- Every old valuation has a matching compact valuation. -/
theorem compactValuation_agrees (old : Nat → Term Symbol) (domains : List (Nat × Nat)) :
    CompactAgreement old (compactValuation old domains) domains := by
  intro entry index member
  simp only [compactValuation, zipIdx_lookup domains entry index member]

/-- A distinct-key map returns every one of its stored entries. -/
theorem lookup_of_member (entries : List (Nat × Value)) (distinct : (entries.map Prod.fst).Nodup)
    (name : Nat) (value : Value) (member : (name, value) ∈ entries) : lookup entries name = some value := by
  induction entries with
  | nil => cases member
  | cons entry rest ih =>
      have unique := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with same | member
      · subst entry
        simp [lookup]
      · have different : entry.1 ≠ name := fun same =>
          unique.1 (List.mem_map.mpr ⟨(name, value), member, same.symm⟩)
        simpa [lookup, different] using ih unique.2 member

/-- Original names read their corresponding compact values. Other names use an arbitrary fixed value. -/
def originalValuation (compact : Nat → Term Symbol) (domains : List (Nat × Nat)) (name : Nat) : Term Symbol :=
  compact ((lookup (domains.zipIdx.map fun (entry, index) => (entry.1, index)) name).getD 0)

/-- Distinct original domain names make compact reindexing reversible on every live variable. -/
theorem originalValuation_agrees (compact : Nat → Term Symbol) (domains : List (Nat × Nat))
    (distinct : (domains.map Prod.fst).Nodup) :
    CompactAgreement (originalValuation compact domains) compact domains := by
  intro entry index member
  let names := domains.zipIdx.map fun (entry, index) => (entry.1, index)
  have nameKeys : names.map Prod.fst = domains.map Prod.fst := by
    simpa only [names, List.map_map, Function.comp_def] using
      congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 domains)
  have unique : (names.map Prod.fst).Nodup := nameKeys ▸ distinct
  have named : (entry.1, index) ∈ names := List.mem_map.mpr ⟨(entry, index), member, rfl⟩
  have found := lookup_of_member names unique entry.1 index named
  dsimp only [names] at found
  simp only [originalValuation, found, Option.getD_some]

/-- Update one eliminated variable while retaining every other assigned term. -/
def updateValuation (assignment : Nat → Term Symbol) (name : Nat) (value : Term Symbol) : Nat → Term Symbol :=
  fun other => if other = name then value else assignment other

/-- Updating an absent variable does not change the context's instantiated term. -/
theorem instantiate_update_unused (assignment : Nat → Term Symbol) (name : Nat) (value : Term Symbol)
    (fragment : Fragment Symbol) (unused : occurs name fragment = false) :
    instantiate (updateValuation assignment name value) fragment = instantiate assignment fragment := by
  induction fragment using Fragment.rec
    (motive_2 := fun children => occursMany name children = false →
      instantiateMany (updateValuation assignment name value) children = instantiateMany assignment children) with
  | var other =>
      have different : other ≠ name := by
        intro same
        subst other
        simp only [occurs, beq_self_eq_true] at unused
        cases unused
      simp [instantiate, updateValuation, different]
  | constructor symbol children ih =>
      exact congrArg (Term.node symbol) (ih unused)
  | nil _ => rfl
  | cons first rest ihfirst ihrest absent =>
      have neither : occurs name first = false ∧ occursMany name rest = false := by simpa [occursMany] using absent
      simp only [instantiateMany, ihfirst neither.1, ihrest neither.2]

/-- Source calls normalize before the next rewrite, so they introduce at most one acyclic binding. -/
def AdmissibleBindings (problem : Problem Symbol) : Prop :=
  problem.bindings = [] ∨ ∃ name fragment,
    problem.bindings = [(name, fragment)] ∧ name ∉ problem.domains.map Prod.fst ∧ occurs name fragment = false

/-- Every compact valuation extends to all source bindings without changing any live domain. -/
theorem extend_bindings (compact : Nat → Term Symbol) (problem : Problem Symbol)
    (distinct : (problem.domains.map Prod.fst).Nodup) (admissible : AdmissibleBindings problem) :
    ∃ old, BindingsHold old problem.bindings ∧ CompactAgreement old compact problem.domains := by
  let base := originalValuation compact problem.domains
  have agrees := originalValuation_agrees compact problem.domains distinct
  rcases admissible with empty | ⟨name, fragment, singleton, removed, unused⟩
  · exact ⟨base, by simp [BindingsHold, empty], agrees⟩
  · let old := updateValuation base name (instantiate base fragment)
    refine ⟨old, ?_, ?_⟩
    · rw [singleton]
      simp only [BindingsHold, List.forall_mem_singleton]
      have assigned : old name = instantiate base fragment := by simp [old, updateValuation]
      rw [assigned]
      exact (instantiate_update_unused base name (instantiate base fragment) fragment unused).symm
    · intro entry index member
      have domainMember := List.mem_of_getElem? (zipIdx_lookup problem.domains entry index member)
      have different : entry.1 ≠ name := fun same => removed (List.mem_map.mpr ⟨entry, domainMember, same⟩)
      simp only [old, updateValuation, different, ↓reduceIte]
      exact agrees entry index member

/-- Successful normalization is a bijection on the finite live tuples, including singleton substitutions. -/
theorem normalize_live_solution_iff [DecidableEq Symbol] [Ord Symbol]
    (fuel : Nat) (problem normalized : Problem Symbol)
    (distinct : (problem.domains.map Prod.fst).Nodup) (admissible : AdmissibleBindings problem)
    (success : normalize fuel problem = .ok (some normalized)) (values : List (Term Symbol)) :
    LiveSolution problem values ↔ LiveSolution normalized values := by
  have shape := normalize_shape fuel problem normalized success
  constructor
  · rintro ⟨old, tuple, bindings, constraints⟩
    let compact := compactValuation old problem.domains
    have agreement := compactValuation_agrees old problem.domains
    have constraints' := (normalize_semantics old compact problem bindings
      (compact_names_agree old compact problem.domains agreement) fuel (some normalized) success).mp constraints
    refine ⟨compact, ?_, ?_, constraints'⟩
    · rw [shape.1]
      exact (tuple_renaming_semantics old compact problem.domains agreement values).mp tuple
    · simp [BindingsHold, shape.2.1]
  · rintro ⟨compact, tuple, _, constraints⟩
    obtain ⟨old, bindings, agreement⟩ := extend_bindings compact problem distinct admissible
    have constraints' := (normalize_semantics old compact problem bindings
      (compact_names_agree old compact problem.domains agreement) fuel (some normalized) success).mpr constraints
    refine ⟨old, ?_, bindings, constraints'⟩
    rw [shape.1] at tuple
    exact (tuple_renaming_semantics old compact problem.domains agreement values).mpr tuple

/-- The actual normalizer preserves the exact finite solution count. -/
theorem normalize_count [DecidableEq Symbol] [Ord Symbol]
    (language : Nat → List (Term Symbol)) (fuel : Nat) (problem normalized : Problem Symbol)
    (distinct : (problem.domains.map Prod.fst).Nodup) (admissible : AdmissibleBindings problem)
    (success : normalize fuel problem = .ok (some normalized)) :
    solutionCount language problem = solutionCount language normalized := by
  classical
  unfold solutionCount solutionTuples candidateTuples
  rw [normalize_preserves_graph_domains fuel problem normalized success]
  congr 1
  apply List.filter_congr
  intro values member
  simp only [normalize_live_solution_iff fuel problem normalized distinct admissible success values]

/-- A failed normalization has zero finite solutions, independently of the domain sizes. -/
theorem normalize_none_count [DecidableEq Symbol] [Ord Symbol]
    (language : Nat → List (Term Symbol)) (fuel : Nat) (problem : Problem Symbol)
    (success : normalize fuel problem = .ok none) : solutionCount language problem = 0 := by
  classical
  have noSolution : ∀ values, ¬ LiveSolution problem values := by
    intro values ⟨old, _, bindings, constraints⟩
    let compact := compactValuation old problem.domains
    have agreement := compactValuation_agrees old problem.domains
    exact (normalize_semantics old compact problem bindings
      (compact_names_agree old compact problem.domains agreement) fuel none success).mp constraints
  simp [solutionCount, solutionTuples, noSolution]

/-- Updating a name outside the live domains preserves every recorded tuple coordinate. -/
theorem tuple_update_unused (assignment : Nat → Term Symbol) (name : Nat) (value : Term Symbol)
    (domains : List (Nat × Nat)) (values : List (Term Symbol)) (absent : name ∉ domains.map Prod.fst) :
    TupleMatches (updateValuation assignment name value) domains values ↔ TupleMatches assignment domains values := by
  rw [tupleMatches_iff, tupleMatches_iff]
  have unchanged : domains.map (fun entry => updateValuation assignment name value entry.1) =
      domains.map (fun entry => assignment entry.1) := by
    apply List.map_congr_left
    intro entry member
    have different : entry.1 ≠ name := fun same => absent (List.mem_map.mpr ⟨entry, member, same⟩)
    simp only [updateValuation, different, ↓reduceIte]
  rw [unchanged]

/-- Any complete tuple over distinct live names defines a valuation of those names. -/
theorem tuple_assignment_exists (fallback : Term Symbol) (domains : List (Nat × Nat))
    (values : List (Term Symbol)) (distinct : (domains.map Prod.fst).Nodup)
    (length : values.length = domains.length) : ∃ assignment, TupleMatches assignment domains values := by
  induction domains generalizing values with
  | nil =>
      have empty : values = [] := by simpa using length
      subst values
      exact ⟨fun _ => fallback, .nil⟩
  | cons entry rest ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          have tailLength : values.length = rest.length := by simpa using length
          have distinct := List.nodup_cons.mp distinct
          obtain ⟨assignment, matching⟩ := ih values distinct.2 tailLength
          refine ⟨updateValuation assignment entry.1 value, .cons ?_ ?_⟩
          · simp [updateValuation]
          · exact (tuple_update_unused assignment entry.1 value rest values distinct.1).mpr matching

/-- A product candidate has one value for every original live domain. -/
theorem candidate_tuple_length (language : Nat → List (Term Symbol)) (domains : List (Nat × Nat))
    (values : List (Term Symbol)) (member : values ∈ candidateTuples language domains) :
    values.length = domains.length := by
  have related := (mem_products language (domains.map Prod.snd) values).mp member
  simpa only [List.length_map] using related.length_eq.symm

/-- Cartesian products have the product of the independent domain sizes. -/
theorem products_length (choices : Input → List Output) (inputs : List Input) :
    (products choices inputs).length = (inputs.map fun input => (choices input).length).prod := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      simp only [products, List.length_flatMap, List.length_map, List.map_cons, List.prod_cons]
      simp only [List.map_const', List.sum_replicate_nat, ih]

/-- Independent domains count every tuple once; an unused domain remains an independent choice. -/
theorem independent_solution_count (language : Nat → List (Term Symbol)) (fallback : Term Symbol)
    (problem : Problem Symbol) (distinct : (problem.domains.map Prod.fst).Nodup)
    (bindings : problem.bindings = []) (obligations : problem.obligations = []) :
    solutionCount language problem = (problem.domains.map fun entry => (language entry.2).length).prod := by
  classical
  have everyCandidate : ∀ values ∈ candidateTuples language problem.domains, LiveSolution problem values := by
    intro values member
    obtain ⟨assignment, matching⟩ := tuple_assignment_exists fallback problem.domains values distinct
      (candidate_tuple_length language problem.domains values member)
    exact ⟨assignment, matching, by simp [BindingsHold, bindings], by simp [obligations]⟩
  unfold solutionCount solutionTuples
  rw [List.filter_eq_self.mpr (fun values member => by simpa using everyCandidate values member)]
  simpa only [candidateTuples, List.map_map, Function.comp_def] using products_length language (problem.domains.map Prod.snd)

/-- If any independent domain is empty, its entire Cartesian product is empty. -/
theorem products_empty_domain (choices : Input → List Output) (inputs : List Input) (input : Input)
    (member : input ∈ inputs) (empty : choices input = []) : products choices inputs = [] := by
  induction inputs with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [products, empty]
      · simp [products, ih member]

/-- The source's early empty-domain branch has zero semantic solutions. -/
theorem empty_domain_solution_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (entry : Nat × Nat) (member : entry ∈ problem.domains) (empty : language entry.2 = []) :
    solutionCount language problem = 0 := by
  have noCandidates := products_empty_domain language (problem.domains.map Prod.snd) entry.2
    (List.mem_map.mpr ⟨entry, member, rfl⟩) empty
  simp [solutionCount, solutionTuples, candidateTuples, noCandidates]

/-- Replacing a pending conjunction by an equivalent conjunction preserves its finite solution count. -/
theorem solutionCount_obligations (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (obligations : List (Symbolic.Obligation Symbol))
    (equivalent : ∀ assignment,
      (∀ obligation ∈ problem.obligations, Satisfies assignment obligation) ↔
        ∀ obligation ∈ obligations, Satisfies assignment obligation) :
    solutionCount language problem = solutionCount language {problem with obligations := obligations} := by
  classical
  unfold solutionCount solutionTuples
  congr 1
  apply List.filter_congr
  intro values _
  simp only [LiveSolution, equivalent]
  rfl

/-- A universally false pending requirement gives semantic count zero. -/
theorem solutionCount_impossible (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (impossible : ∀ assignment, ¬(∀ obligation ∈ problem.obligations, Satisfies assignment obligation)) :
    solutionCount language problem = 0 := by
  classical
  have noSolution : ∀ values, ¬LiveSolution problem values := by
    intro values ⟨assignment, _, _, constraints⟩
    exact impossible assignment constraints
  simp [solutionCount, solutionTuples, noSolution]

/-- Dropping a resolved existence target preserves the actual problem's finite count. -/
theorem resolved_exists_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (target : Symbolic.Target Symbol) (rest : List (Symbolic.Obligation Symbol)) (resolved : Fragment Symbol)
    (pending : problem.obligations = .exists target :: rest)
    (found : Symbolic.resolveContext target.fragment target.path = .resolved resolved) :
    solutionCount language problem = solutionCount language {problem with obligations := rest} := by
  apply solutionCount_obligations language problem rest
  intro assignment
  have value := Symbolic.resolveContext_sound assignment target.fragment resolved target.path found
  have satisfied : Satisfies assignment (.exists target) := ⟨instantiate assignment resolved, value⟩
  simp only [pending, List.forall_mem_cons, satisfied, true_and]

/-- The source's absent-path branch has no solution. -/
theorem absent_exists_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (target : Symbolic.Target Symbol) (rest : List (Symbolic.Obligation Symbol))
    (pending : problem.obligations = .exists target :: rest)
    (missing : Symbolic.resolveContext target.fragment target.path = .absent) :
    solutionCount language problem = 0 := by
  apply solutionCount_impossible language problem
  intro assignment constraints
  obtain ⟨term, found⟩ := constraints (.exists target) (by simp [pending])
  have absent := Symbolic.resolveContext_absent assignment target.fragment target.path missing
  rw [Symbolic.targetValue, absent] at found
  cases found

/-- Following both resolved equality targets preserves the source unifier's whole-context equation. -/
theorem resolved_equality_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (left right : Symbolic.Target Symbol) (first second : Fragment Symbol)
    (rest : List (Symbolic.Obligation Symbol)) (pending : problem.obligations = .equal left right :: rest)
    (leftFound : Symbolic.resolveContext left.fragment left.path = .resolved first)
    (rightFound : Symbolic.resolveContext right.fragment right.path = .resolved second) :
    solutionCount language problem = solutionCount language
      {problem with obligations := .equal ⟨first, []⟩ ⟨second, []⟩ :: rest} := by
  apply solutionCount_obligations
  intro assignment
  simp only [pending, List.forall_mem_cons, Satisfies, Symbolic.targetValue,
    Symbolic.resolveContext_sound assignment left.fragment first left.path leftFound,
    Symbolic.resolveContext_sound assignment right.fragment second right.path rightFound, Term.atPath]

/-- The source's whole-context occurs-check zero is the exact finite solution count. -/
theorem occurs_solution_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (name : Nat) (symbol : Symbol) (children : List (Fragment Symbol)) (rest : List (Symbolic.Obligation Symbol))
    (pending : problem.obligations = .equal ⟨.var name, []⟩ ⟨.constructor symbol children, []⟩ :: rest)
    (occurrence : occurs name (.constructor symbol children) = true) : solutionCount language problem = 0 := by
  apply solutionCount_impossible language problem
  intro assignment constraints
  have equal := constraints (.equal ⟨.var name, []⟩ ⟨.constructor symbol children, []⟩) (by simp [pending])
  obtain ⟨term, left, right⟩ := equal
  have impossible := occurs_constructor_reject assignment name symbol children occurrence
  exact impossible (Option.some.inj (left.trans right.symm))

end MicroCFTA.SymbolicDriver
