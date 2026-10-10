import Std

/-!
# Repeated target paths in Holds

The repaired `Holds` evaluator creates one formal per target occurrence. It
adds an equality from each repeated occurrence to the first formal for that
path. This module computes those first occurrences and proves that the alias
assumptions give exactly one semantic value per mentioned path.

Formulas are arbitrary predicates on occurrence assignments. The equivalence
therefore applies to both formula entailment and formula refutation. It does
not certify the SMT solver or the Liquid Fixpoint substitution implementation.
-/

namespace MicroCFTA.Holds

/-- Find the first occurrence of a path. Return the list length when it is absent. -/
def firstIndex {Path : Type} [DecidableEq Path] : List Path → Path → Nat
  | [], _ => 0
  | p :: ps, wanted => if p = wanted then 0 else firstIndex ps wanted + 1

/-- A successful lookup has a first occurrence, and that occurrence is no later. -/
theorem firstIndex_lookup {Path : Type} [DecidableEq Path]
    (targets : List Path) (wanted : Path) (index : Nat)
    (found : targets[index]? = some wanted) :
    targets[firstIndex targets wanted]? = some wanted ∧ firstIndex targets wanted ≤ index := by
  induction targets generalizing index with
  | nil => simp at found
  | cons p ps ih =>
      by_cases same : p = wanted
      · subst p
        simp [firstIndex]
      · cases index with
        | zero =>
            have impossible : p = wanted := Option.some.inj found
            exact False.elim (same impossible)
        | succ index =>
            have previous : ps[index]? = some wanted := by simpa using found
            obtain ⟨existsFirst, before⟩ := ih index previous
            simp only [firstIndex, same, ↓reduceIte, List.getElem?_cons_succ]
            exact ⟨existsFirst, Nat.succ_le_succ before⟩

/-- Every mentioned path has an in-range first occurrence. -/
theorem firstIndex_lt_of_mem {Path : Type} [DecidableEq Path]
    (targets : List Path) (wanted : Path) (member : wanted ∈ targets) :
    firstIndex targets wanted < targets.length := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp (firstIndex_lookup targets wanted index found).1
  exact bound

/-- Lookup at the computed first occurrence returns its path. -/
theorem get_firstIndex {Path : Type} [DecidableEq Path]
    (targets : List Path) (wanted : Path) (member : wanted ∈ targets) :
    targets[firstIndex targets wanted]'(firstIndex_lt_of_mem targets wanted member) = wanted := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  have first := (firstIndex_lookup targets wanted index found).1
  rw [List.getElem?_eq_getElem (firstIndex_lt_of_mem targets wanted member)] at first
  exact Option.some.inj first

/-- No earlier index contains the path selected by `firstIndex`. -/
theorem firstIndex_earliest {Path : Type} [DecidableEq Path]
    (targets : List Path) (wanted : Path) (index : Nat)
    (earlier : index < firstIndex targets wanted) : targets[index]? ≠ some wanted := by
  intro found
  have before := (firstIndex_lookup targets wanted index found).2
  omega

/-- Insert one occurrence name while retaining an earlier name for the same path. -/
def rememberFirst {Path : Type} [DecidableEq Path]
    (names : Path → Option Nat) (path : Path) (index : Nat) : Path → Option Nat :=
  fun wanted => if path = wanted then
    match names wanted with
    | some earlier => some earlier
    | none => some index
  else names wanted

/-- Insert occurrence names from left to right, as in `Map.fromListWith`. -/
def collectFirst {Path : Type} [DecidableEq Path] :
    List Path → Nat → (Path → Option Nat) → Path → Option Nat
  | [], _, names => names
  | path :: rest, index, names =>
      collectFirst rest (index + 1) (rememberFirst names path index)

/-- Once a path has a name, later insertions retain that name. -/
theorem collectFirst_existing {Path : Type} [DecidableEq Path]
    (targets : List Path) (index : Nat) (names : Path → Option Nat)
    (wanted : Path) (earlier : Nat) (present : names wanted = some earlier) :
    collectFirst targets index names wanted = some earlier := by
  induction targets generalizing index names with
  | nil => exact present
  | cons path rest ih =>
      apply ih
      simp [rememberFirst, present]

/-- A path absent from the initial map receives its first occurrence's name. -/
theorem collectFirst_absent {Path : Type} [DecidableEq Path]
    (targets : List Path) (index : Nat) (names : Path → Option Nat)
    (wanted : Path) (absent : names wanted = none) :
    collectFirst targets index names wanted =
      if wanted ∈ targets then some (index + firstIndex targets wanted) else none := by
  induction targets generalizing index names with
  | nil => simpa [collectFirst] using absent
  | cons path rest ih =>
      by_cases same : path = wanted
      · subst path
        have nowPresent : rememberFirst names wanted index wanted = some index := by
          simp [rememberFirst, absent]
        have retained := collectFirst_existing rest (index + 1)
          (rememberFirst names wanted index) wanted index nowPresent
        simpa [collectFirst, firstIndex] using retained
      · have stillAbsent : rememberFirst names path index wanted = none := by
          simp [rememberFirst, same, absent]
        rw [collectFirst, ih _ _ stillAbsent]
        simp only [List.mem_cons, Ne.symm same, false_or, firstIndex, same, ↓reduceIte]
        by_cases occurs : wanted ∈ rest
        · simp [occurs, Nat.add_assoc, Nat.add_comm]
        · simp [occurs]

/-- Build the first-occurrence map from an empty map and numbered formals. -/
def firstNames {Path : Type} [DecidableEq Path] (targets : List Path) : Path → Option Nat :=
  collectFirst targets 0 (fun _ => none)

/-- The insertion-based first-name map agrees with direct first-index search. -/
theorem firstNames_lookup {Path : Type} [DecidableEq Path]
    (targets : List Path) (wanted : Path) :
    firstNames targets wanted =
      if wanted ∈ targets then some (firstIndex targets wanted) else none := by
  simpa [firstNames] using collectFirst_absent targets 0 (fun _ => none) wanted rfl

/-- The finite index of an argument formal in the target list. -/
abbrev FormalIndex {Path : Type} (targets : List Path) := Fin targets.length

/-- The finite set of paths named by at least one formal occurrence. -/
abbrev Mentioned {Path : Type} (targets : List Path) := { path : Path // path ∈ targets }

/-- The mentioned path at one formal occurrence. -/
def formalPath {Path : Type} (targets : List Path) (index : FormalIndex targets) :
    Mentioned targets := ⟨targets[index.val], List.getElem_mem index.isLt⟩

/-- The first formal occurrence for a mentioned path. -/
def firstFormalIndex {Path : Type} [DecidableEq Path]
    (targets : List Path) (path : Mentioned targets) : FormalIndex targets :=
  ⟨firstIndex targets path.val, firstIndex_lt_of_mem targets path.val path.property⟩

/-- The representative formal used for one occurrence's alias. -/
def representative {Path : Type} [DecidableEq Path]
    (targets : List Path) (index : FormalIndex targets) : FormalIndex targets :=
  firstFormalIndex targets (formalPath targets index)

/-- Every map lookup used by alias emission exists and returns the computed representative. -/
theorem firstNames_at_formal {Path : Type} [DecidableEq Path]
    (targets : List Path) (index : FormalIndex targets) :
    firstNames targets (formalPath targets index).val =
      some (representative targets index).val := by
  rw [firstNames_lookup]
  simp only [(formalPath targets index).property, ↓reduceIte]
  rfl

/-- Every mentioned path is covered by its computed representative. -/
theorem firstFormalIndex_covers {Path : Type} [DecidableEq Path]
    (targets : List Path) (path : Mentioned targets) :
    formalPath targets (firstFormalIndex targets path) = path := by
  apply Subtype.ext
  exact get_firstIndex targets path.val path.property

/-- The representative points to the same target path as its occurrence. -/
theorem representative_path {Path : Type} [DecidableEq Path]
    (targets : List Path) (index : FormalIndex targets) :
    formalPath targets (representative targets index) = formalPath targets index :=
  firstFormalIndex_covers targets (formalPath targets index)

/-- The computed representative is never later than its occurrence. -/
theorem representative_le {Path : Type} [DecidableEq Path]
    (targets : List Path) (index : FormalIndex targets) :
    (representative targets index).val ≤ index.val :=
  (firstIndex_lookup targets targets[index.val] index.val
    (List.getElem?_eq_getElem index.isLt)).2

/-- FormalIndexs of the same path compute the same representative. -/
theorem representative_same_path {Path : Type} [DecidableEq Path]
    (targets : List Path) (left right : FormalIndex targets)
    (same : formalPath targets left = formalPath targets right) :
    representative targets left = representative targets right :=
  congrArg (firstFormalIndex targets) same

/-- Computing the representative twice has the same result as computing it once. -/
theorem representative_idempotent {Path : Type} [DecidableEq Path]
    (targets : List Path) (index : FormalIndex targets) :
    representative targets (representative targets index) = representative targets index :=
  representative_same_path targets _ _ (representative_path targets index)

/-- Alias equalities tie each occurrence to its computed representative. -/
def Aliases {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (values : FormalIndex targets → Value) : Prop :=
  ∀ index, values index = values (representative targets index)

/-- The evaluator emits only alias equalities between distinct formals. -/
def EmittedAliases {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (values : FormalIndex targets → Value) : Prop :=
  ∀ index, representative targets index ≠ index →
    values index = values (representative targets index)

/-- Omitting a formal's reflexive alias has no semantic effect. -/
theorem emittedAliases_iff {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (values : FormalIndex targets → Value) :
    EmittedAliases targets values ↔ Aliases targets values := by
  constructor
  · intro aliases index
    by_cases same : representative targets index = index
    · rw [same]
    · exact aliases index same
  · intro aliases index _
    exact aliases index

/-- The finite alias list emitted for occurrence names that differ from their representative. -/
def aliasPairs {Path : Type} [DecidableEq Path] (targets : List Path) :
    List (FormalIndex targets × FormalIndex targets) :=
  ((List.finRange targets.length).filter fun index =>
    decide (representative targets index ≠ index)).map fun index =>
      (index, representative targets index)

/-- Each emitted equality is exactly an occurrence and its distinct first representative. -/
theorem mem_aliasPairs {Path : Type} [DecidableEq Path] (targets : List Path)
    (left right : FormalIndex targets) :
    (left, right) ∈ aliasPairs targets ↔
      right = representative targets left ∧ right ≠ left := by
  constructor
  · intro member
    obtain ⟨index, inside, equal⟩ := List.mem_map.mp member
    obtain ⟨_, different⟩ := List.mem_filter.mp inside
    rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
    exact ⟨rfl, of_decide_eq_true different⟩
  · rintro ⟨rfl, different⟩
    exact List.mem_map.mpr ⟨left,
      List.mem_filter.mpr ⟨List.mem_finRange left, by simp [different]⟩, rfl⟩

/-- Conjoining the emitted finite equalities gives exactly the alias predicate. -/
theorem aliasPairs_correct {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (values : FormalIndex targets → Value) :
    (∀ pair ∈ aliasPairs targets, values pair.1 = values pair.2) ↔
      Aliases targets values := by
  rw [← emittedAliases_iff]
  constructor
  · intro allPairs index different
    exact allPairs (index, representative targets index)
      ((mem_aliasPairs targets _ _).mpr ⟨rfl, different⟩)
  · intro allAliases pair inside
    have member := (mem_aliasPairs targets pair.1 pair.2).mp inside
    rw [member.1]
    exact allAliases pair.1 (by simpa only [member.1] using member.2)

/-- All occurrences of the same target path have the same value. -/
def Coherent {Path Value : Type} (targets : List Path)
    (values : FormalIndex targets → Value) : Prop :=
  ∀ left right, formalPath targets left = formalPath targets right →
    values left = values right

/-- The concrete representative aliases establish exactly path coherence. -/
theorem aliases_iff_coherent {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (values : FormalIndex targets → Value) :
    Aliases targets values ↔ Coherent targets values := by
  constructor
  · intro aliases left right same
    rw [aliases left, aliases right, representative_same_path targets left right same]
  · intro coherent index
    exact coherent index (representative targets index) (representative_path targets index).symm

/-- Read a path valuation at every formal occurrence. -/
def expand {Path Value : Type} (targets : List Path)
    (values : Mentioned targets → Value) : FormalIndex targets → Value :=
  fun index => values (formalPath targets index)

/-- Read each path's value from its computed first formal. -/
def collapse {Path Value : Type} [DecidableEq Path] (targets : List Path)
    (values : FormalIndex targets → Value) : Mentioned targets → Value :=
  fun path => values (firstFormalIndex targets path)

/-- Expanding a path valuation satisfies every alias. -/
theorem expand_aliases {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (values : Mentioned targets → Value) :
    Aliases targets (expand targets values) := by
  intro index
  simp only [expand, representative_path]

/-- Collapsing then expanding an aliased assignment recovers every formal value. -/
theorem expand_collapse {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (values : FormalIndex targets → Value)
    (aliases : Aliases targets values) :
    expand targets (collapse targets values) = values := by
  funext index
  exact (aliases index).symm

/-- Expanding then collapsing recovers the complete mentioned-path valuation. -/
theorem collapse_expand {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (values : Mentioned targets → Value) :
    collapse targets (expand targets values) = values := by
  funext path
  exact congrArg values (firstFormalIndex_covers targets path)

/-- Refinement assumptions for all occurrence formals. -/
def Refinements {Path Value : Type} (targets : List Path)
    (refinement : Path → Value → Prop) (values : FormalIndex targets → Value) : Prop :=
  ∀ index, refinement (formalPath targets index).val (values index)

/-- Refinement assumptions with one value per mentioned path. -/
def PathRefinements {Path Value : Type} (targets : List Path)
    (refinement : Path → Value → Prop) (values : Mentioned targets → Value) : Prop :=
  ∀ path, refinement path.val (values path)

/-- Repeated occurrence refinements are equivalent to one assumption per path. -/
theorem refinements_expand_iff {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (refinement : Path → Value → Prop)
    (values : Mentioned targets → Value) :
    Refinements targets refinement (expand targets values) ↔
      PathRefinements targets refinement values := by
  constructor
  · intro inside path
    have atFirst := inside (firstFormalIndex targets path)
    simpa only [expand, firstFormalIndex_covers] using atFirst
  · intro inside index
    exact inside (formalPath targets index)

/-- Contract entailment with the repaired occurrence-formal assumptions. -/
def HoldsWithAliases {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (refinement : Path → Value → Prop)
    (formula : (FormalIndex targets → Value) → Prop) : Prop :=
  ∀ values, Refinements targets refinement values → EmittedAliases targets values → formula values

/-- Contract entailment with one value for each mentioned path. -/
def HoldsByPath {Path Value : Type} (targets : List Path)
    (refinement : Path → Value → Prop)
    (formula : (FormalIndex targets → Value) → Prop) : Prop :=
  ∀ values, PathRefinements targets refinement values →
    formula (expand targets values)

/-- The repaired alias query is sound and complete for one value per target path. -/
theorem holdsWithAliases_iff {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (refinement : Path → Value → Prop)
    (formula : (FormalIndex targets → Value) → Prop) :
    HoldsWithAliases targets refinement formula ↔ HoldsByPath targets refinement formula := by
  constructor
  · intro proved values inside
    exact proved (expand targets values)
      ((refinements_expand_iff targets refinement values).mpr inside)
      ((emittedAliases_iff targets _).mpr (expand_aliases targets values))
  · intro proved values inside aliases
    have same := expand_collapse targets values ((emittedAliases_iff targets values).mp aliases)
    have pathInside := (refinements_expand_iff targets refinement (collapse targets values)).mp
      (by simpa only [same] using inside)
    have accepted := proved (collapse targets values) pathInside
    simpa only [same] using accepted

/-- Positive contracts prove the formula. Negative contracts prove its negation. -/
def signed {Index Value : Type} (positive : Bool)
    (formula : (Index → Value) → Prop) (values : Index → Value) : Prop :=
  if positive then formula values else ¬formula values

/-- Alias repair preserves both positive entailment and formula refutation. -/
theorem signed_holdsWithAliases_iff {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (refinement : Path → Value → Prop)
    (formula : (FormalIndex targets → Value) → Prop) (positive : Bool) :
    HoldsWithAliases targets refinement (signed positive formula) ↔
      HoldsByPath targets refinement (signed positive formula) :=
  holdsWithAliases_iff targets refinement (signed positive formula)

/-- The finite compiled query conjoins refinements and its emitted alias equations. -/
def CompiledQuery {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (refinement : Path → Value → Prop)
    (formula : (FormalIndex targets → Value) → Prop) : Prop :=
  ∀ values, (Refinements targets refinement values ∧
    ∀ pair ∈ aliasPairs targets, values pair.1 = values pair.2) → formula values

/-- The concrete emitted-query construction is sound and complete for every polarity. -/
theorem compiledQuery_iff {Path Value : Type} [DecidableEq Path]
    (targets : List Path) (refinement : Path → Value → Prop)
    (formula : (FormalIndex targets → Value) → Prop) (positive : Bool) :
    CompiledQuery targets refinement (signed positive formula) ↔
      HoldsByPath targets refinement (signed positive formula) := by
  rw [← signed_holdsWithAliases_iff targets refinement formula positive]
  constructor
  · intro compiled values inside aliases
    exact compiled values ⟨inside,
      (aliasPairs_correct targets values).mpr ((emittedAliases_iff targets values).mp aliases)⟩
  · intro proved values assumptions
    exact proved values assumptions.1
      ((emittedAliases_iff targets values).mpr
        ((aliasPairs_correct targets values).mp assumptions.2))

end MicroCFTA.Holds
