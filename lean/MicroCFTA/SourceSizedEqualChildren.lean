import MicroCFTA.SourceCompactGuards
import MicroCFTA.SourceSizedDecided

/-!
# Source equal-child row classification

Table.equalChildren rejects residual guards. It reads the current normalized
equalities, parses direct child paths, joins the child groups, and retains the
sorted groups with at least two positions. Relabeling retains the symbol and
every child domain. The semantic law uses the source cached-class invariant.
Actual Constraint construction must derive that invariant. Classification
does not test or assume its proof.
-/
namespace MicroCFTA.SourceSizedEqualChildren
open Language SourceGuards SourceObservations SourceSymbolicIndex SourceSizedDecided

variable {State Symbol Formula Value : Type}

/-- Sort each retained group without changing the order of the groups. -/
def classesOf (groups : List (List Nat)) : List (List Nat) :=
  (groups.filter fun group => decide (2 ≤ group.length)).map
    fun group => group.mergeSort (fun left right => decide (left ≤ right))

/-- Each output class comes from one nontrivial group in the source list. -/
theorem mem_classesOf (groups : List (List Nat)) (positions : List Nat) :
    positions ∈ classesOf groups ↔ ∃ group ∈ groups, 2 ≤ group.length ∧
      group.mergeSort (fun left right => decide (left ≤ right)) = positions := by
  constructor
  · intro member
    obtain ⟨group, retained, same⟩ := List.mem_map.mp member
    obtain ⟨groupIn, long⟩ := List.mem_filter.mp retained
    exact ⟨group, groupIn, of_decide_eq_true long, same⟩
  · rintro ⟨group, groupIn, long, same⟩
    exact List.mem_map.mpr ⟨group, List.mem_filter.mpr ⟨groupIn, by simpa using long⟩, same⟩

private theorem equalAt_sorted (value : Nat → Value) (group : List Nat) :
    CompactGroups.EqualAt value (group.mergeSort (fun left right => decide (left ≤ right))) ↔
      CompactGroups.EqualAt value group := by
  have perm := List.mergeSort_perm group (fun left right => decide (left ≤ right))
  constructor
  · intro equal left leftIn right rightIn
    exact equal left (perm.mem_iff.mpr leftIn) right (perm.mem_iff.mpr rightIn)
  · intro equal left leftIn right rightIn
    exact equal left (perm.mem_iff.mp leftIn) right (perm.mem_iff.mp rightIn)

private theorem equalAt_short (value : Nat → Value) (group : List Nat)
    (short : group.length < 2) : CompactGroups.EqualAt value group := by
  cases group with
  | nil => simp [CompactGroups.EqualAt]
  | cons first rest =>
      cases rest with
      | nil => simp [CompactGroups.EqualAt]
      | cons second rest => simp only [List.length_cons] at short; omega

/-- Sorting and removing singleton groups preserve all equality conditions. -/
theorem classesOf_exact (value : Nat → Value) (groups : List (List Nat)) :
    CompactGroups.GroupsEqual value (classesOf groups) ↔ CompactGroups.GroupsEqual value groups := by
  constructor
  · intro equal group groupIn
    by_cases long : 2 ≤ group.length
    · exact (equalAt_sorted value group).mp
        (equal _ ((mem_classesOf groups _).mpr ⟨group, groupIn, long, rfl⟩))
    · exact equalAt_short value group (by omega)
  · intro equal positions positionsIn
    obtain ⟨group, groupIn, _, rfl⟩ := (mem_classesOf groups positions).mp positionsIn
    exact (equalAt_sorted value group).mpr (equal group groupIn)

/-- Retained equality classes have at least two entries. -/
theorem classesOf_nontrivial (groups : List (List Nat)) :
    ∀ positions ∈ classesOf groups, 2 ≤ positions.length := by
  intro positions positionsIn
  obtain ⟨group, _, long, rfl⟩ := (mem_classesOf groups positions).mp positionsIn
  rw [(List.mergeSort_perm group (fun left right => decide (left ≤ right))).length_eq]
  exact long

/-- Sorting retained groups preserves every checked position bound. -/
theorem classesOf_bounded (arity : Nat) (groups : List (List Nat))
    (valid : CompactGroups.ValidClasses arity groups) :
    CompactGroups.ValidClasses arity (classesOf groups) := by
  intro positions positionsIn index indexIn
  obtain ⟨group, groupIn, _, rfl⟩ := (mem_classesOf groups positions).mp positionsIn
  exact valid group groupIn index
    ((List.mergeSort_perm group (fun left right => decide (left ≤ right))).mem_iff.mp indexIn)

/-- Execute the source residual check, current equalities, grouping, and classesOf. -/
noncomputable def equalChildren (row : Row State Symbol (Constraint Formula)) :
    Option (List (List Nat)) :=
  if (SourceCompactGuards.positive row.constraint.guard).isSome = true then do
    let paths ← SourceCompactGuards.sourceEqualities row.constraint
    let parsed ← SourceCompactGuards.parse row.children.length paths
    pure (classesOf (CompactGroups.childGroups row.children.length parsed))
  else none

/-- Success records the current equalities and the literal joined-group result. -/
theorem equalChildren_exact (row : Row State Symbol (Constraint Formula))
    (classes : List (List Nat)) :
    equalChildren row = some classes ↔
      (SourceCompactGuards.positive row.constraint.guard).isSome = true ∧
      ∃ paths parsed, SourceCompactGuards.sourceEqualities row.constraint = some paths ∧
        SourceCompactGuards.parse row.children.length paths = some parsed ∧
        classes = classesOf (CompactGroups.childGroups row.children.length parsed) := by
  unfold equalChildren
  split
  next positive =>
    simp only [Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq]
    constructor
    · rintro ⟨paths, read, parsed, checked, same⟩
      exact ⟨positive, paths, parsed, read, checked, same.symm⟩
    · rintro ⟨_, paths, parsed, read, checked, same⟩
      exact ⟨paths, read, parsed, checked, same.symm⟩
  next residual =>
    constructor
    · intro impossible; cases impossible
    · intro accepted
      exact False.elim (residual accepted.1)

/-- A residual guard cannot return an equal-child classification. -/
theorem equalChildren_residual (row : Row State Symbol (Constraint Formula))
    (residual : (SourceCompactGuards.positive row.constraint.guard).isSome = false) :
    equalChildren row = none := by
  simp [equalChildren, residual]

/-- Every emitted class position is inside the actual source row arity. -/
theorem equalChildren_bounded (row : Row State Symbol (Constraint Formula))
    (classes : List (List Nat)) (success : equalChildren row = some classes) :
    CompactGroups.ValidClasses row.children.length classes := by
  obtain ⟨_, _, parsed, _, _, rfl⟩ := (equalChildren_exact row classes).mp success
  apply classesOf_bounded
  intro group groupIn index indexIn
  have inGroups := List.mem_flatten.mpr ⟨group, groupIn, indexIn⟩
  exact List.mem_range.mp
    ((CompactGroups.childGroups_positions row.children.length parsed).mem_iff.mp inGroups)

/-- Successful classification emits only nontrivial equality classes. -/
theorem equalChildren_nontrivial (row : Row State Symbol (Constraint Formula))
    (classes : List (List Nat)) (success : equalChildren row = some classes) :
    ∀ positions ∈ classes, 2 ≤ positions.length := by
  obtain ⟨_, _, _, _, _, rfl⟩ := (equalChildren_exact row classes).mp success
  exact classesOf_nontrivial _

/-- The successful current classifier preserves the complete source guard meaning. -/
theorem equalChildren_guard [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (row : Row State (Label Formula) (Constraint Formula)) (classes : List (List Nat))
    (success : equalChildren row = some classes)
    (active : SourceCompactGuards.ActiveOption row.constraint.equalities)
    (values : List (Term (Label Formula))) (arity : values.length = row.children.length) :
    acceptsConstraint formulas solver row.constraint (.node row.label values) = true ↔
      CompactGroups.GroupsEqual
        (CompactEdgeRanks.childValue (.node row.label []) values) classes := by
  obtain ⟨positive, paths, parsed, read, checked, rfl⟩ :=
    (equalChildren_exact row classes).mp success
  have valid := ((SourceCompactGuards.parse_exact row.children.length paths parsed).mp checked).2
  rw [SourceCompactGuards.sourceEqualities_exact formulas solver row.constraint active positive
    (.node row.label values), read]
  change paths.all (SymbolicDriver.classTest (.node row.label values)) = true ↔
    CompactGroups.GroupsEqual (CompactEdgeRanks.childValue (.node row.label []) values)
      (classesOf (CompactGroups.childGroups row.children.length parsed))
  rw [classesOf_exact, CompactGroups.childGroups_exact _ _ _ valid]
  exact SourceCompactGuards.parsed_guard row.label values paths parsed (by rw [arity]; exact checked)

/-- Relabel a successful row without changing its symbol or child list. -/
noncomputable def classify (row : Row State Symbol (Constraint Formula)) :
    Option (Row State Symbol (List (List Nat))) :=
  (equalChildren row).map fun classes => ⟨row.label, row.children, classes⟩

/-- The relabeled row records its exact source row and classified constraint. -/
theorem classify_shape (row : Row State Symbol (Constraint Formula))
    (output : Row State Symbol (List (List Nat))) (success : classify row = some output) :
    output.label = row.label ∧ output.children = row.children ∧
      equalChildren row = some output.constraint := by
  obtain ⟨classes, checked, same⟩ := Option.map_eq_some_iff.mp success
  cases same
  exact ⟨rfl, rfl, checked⟩

/-- Child domains and the complete equality language survive actual row relabeling. -/
theorem classify_semantics [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (row : Row State (Label Formula) (Constraint Formula))
    (output : Row State (Label Formula) (List (List Nat)))
    (success : classify row = some output)
    (active : SourceCompactGuards.ActiveOption row.constraint.equalities)
    (domain : State → Term (Label Formula) → Prop) (values : List (Term (Label Formula))) :
    (All₂ domain row.children values ∧
      acceptsConstraint formulas solver row.constraint (.node row.label values) = true) ↔
    (All₂ domain output.children values ∧
      CompactGroups.GroupsEqual
        (CompactEdgeRanks.childValue (.node output.label []) values) output.constraint) := by
  have frame := classify_shape row output success
  constructor
  · rintro ⟨children, accepted⟩
    refine ⟨by simpa only [frame.2.1] using children, ?_⟩
    simpa only [frame.1] using
      (equalChildren_guard formulas solver row output.constraint frame.2.2 active values
        children.length_eq.symm).mp accepted
  · rintro ⟨children, accepted⟩
    have original : All₂ domain row.children values := by simpa only [frame.2.1] using children
    refine ⟨original, (equalChildren_guard formulas solver row output.constraint frame.2.2 active values
      original.length_eq.symm).mpr ?_⟩
    simpa only [frame.1] using accepted

/-- Successful source traversal gives each relabeled row an actual original-row witness. -/
theorem classifyRows_origin (rows : List (Row State Symbol (Constraint Formula)))
    (outputs : List (Row State Symbol (List (List Nat))))
    (success : rows.mapM classify = some outputs) :
    ∀ output ∈ outputs, ∃ row ∈ rows, classify row = some output ∧
      output.label = row.label ∧ output.children = row.children := by
  induction rows generalizing outputs with
  | nil =>
      have empty : outputs = [] := by simpa using success.symm
      subst outputs
      simp
  | cons first rest ih =>
      rw [List.mapM_cons] at success
      simp only [Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at success
      obtain ⟨head, checked, tail, traversed, rfl⟩ := success
      intro output member
      rcases List.mem_cons.mp member with rfl | present
      · have frame := classify_shape first output checked
        exact ⟨first, by simp, checked, frame.1, frame.2.1⟩
      · obtain ⟨row, rowIn, actual, label, children⟩ := ih tail traversed output present
        exact ⟨row, by simp [rowIn], actual, label, children⟩

end MicroCFTA.SourceSizedEqualChildren
