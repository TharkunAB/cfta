import MicroCFTA.SourceDenotationLevelDistinct
import MicroCFTA.CanonicalClasses

/-!
# Bounded ordinary denotation and the empty-level stop

The finite key list is the exposed trimmed map domain. All other rows are
empty. The stopping test checks every key, including keys other than the
root. A finite requested prefix is unchanged by stopping at the first empty
level. Set readback controls only the unspecified order within each level.
-/

namespace MicroCFTA.SourceDenotationPlain

open Language LevelEnumeration SourceDenotationLevels SourceDenotationLevelDistinct

/-- The source global stopping test examines every stored row key. -/
def stopped (keys : List State) (table : Tables State Symbol) : Bool :=
  keys.all fun state => (table.current state).isEmpty

/-- Finite ordinary collection follows takeWhile over the source exact-level stream. -/
def collect (automaton : Automaton State Symbol) (setList : List (Term Symbol) → List (Term Symbol))
    (unambiguous : Bool) (keys : List State) (root : State) : Nat → Nat → List (Term Symbol)
  | _, 0 => []
  | depth, count + 1 =>
      if stopped keys (tables automaton setList unambiguous depth) then [] else
        (tables automaton setList unambiguous depth).current root ++
          collect automaton setList unambiguous keys root (depth + 1) count

/-- The finite map's empty test implies an empty current table at every state. -/
theorem stopped_empty (automaton : Automaton State Symbol) (keys : List State)
    (supported : ∀ state, state ∉ keys → automaton state = [])
    (height : Nat) (table : Tables State Symbol) (semantic : Exact automaton height table)
    (empty : stopped keys table = true) : ∀ state, table.current state = [] := by
  intro state
  by_cases present : state ∈ keys
  · have emptyAt := List.all_eq_true.mp empty state present
    simpa using emptyAt
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro term member
    have accepted := ((semantic.1 state term).mp member).1
    cases accepted with
    | node edge children listed accepted guarded =>
        rw [supported state present] at listed
        exact List.not_mem_nil listed

/-- An empty source level leaves every later finite level empty. -/
theorem later_empty (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms) (unambiguous : Bool)
    (depth : Nat) (empty : ∀ state, (tables automaton setList unambiguous depth).current state = [])
    (later : Nat) (after : depth ≤ later) : ∀ state, (tables automaton setList unambiguous later).current state = [] := by
  have referenceEmpty : ∀ state, LevelEnumeration.current automaton (depth + 1) state = [] := by
    intro state
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro term member
    have valid : Accepts automaton state term ∧ term.height = depth + 1 := by
      obtain ⟨listed, height⟩ := List.mem_filter.mp member
      exact ⟨((Language.mem_enumerate_iff automaton (depth + 1) state term).mp listed).1,
        of_decide_eq_true height⟩
    have source := ((tables_exact automaton plain setList setExact unambiguous depth).1 state term).mpr valid
    rw [empty] at source
    exact List.not_mem_nil source
  intro state
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro term member
  obtain ⟨accepted, height⟩ := ((tables_exact automaton plain setList setExact unambiguous later).1 state term).mp member
  have before := LevelEnumeration.stop_complete automaton (depth + 1) (by omega) referenceEmpty state term accepted
  omega

/-- Stopping removes only empty levels, so it preserves the complete finite sequence exactly. -/
theorem collect_exact (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms) (unambiguous : Bool)
    (keys : List State) (supported : ∀ state, state ∉ keys → automaton state = [])
    (root : State) (depth count : Nat) :
    collect automaton setList unambiguous keys root depth count =
      (List.range' depth count).flatMap fun index => (tables automaton setList unambiguous index).current root := by
  induction count generalizing depth with
  | zero => rfl
  | succ count ih =>
      by_cases empty : stopped keys (tables automaton setList unambiguous depth) = true
      · have allEmpty := stopped_empty automaton keys supported (depth + 1) _
          (tables_exact automaton plain setList setExact unambiguous depth) empty
        have restEmpty : ((List.range' depth (count + 1)).flatMap fun index =>
            (tables automaton setList unambiguous index).current root) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro index member
          have lower : depth ≤ index := by
            obtain ⟨offset, _, same⟩ := List.mem_range'.mp member
            omega
          exact later_empty automaton plain setList setExact unambiguous depth allEmpty index lower root
        simp [collect, empty, restEmpty]
      · simp [collect, empty, List.range'_succ, List.flatMap_cons, ih]


/-- The source distinctSymbols predicate compares nubOrd length with the input length. -/
def distinctSymbols [DecidableEq Symbol] (symbols : List Symbol) : Bool :=
  decide ((SourceSizedReference.nub symbols).length = symbols.length)

/-- The actual distinct-symbol length test is equivalent to duplicate freedom. -/
theorem distinctSymbols_exact [DecidableEq Symbol] (symbols : List Symbol) :
    distinctSymbols symbols = true ↔ symbols.Nodup := by
  constructor
  · intro checked
    have same : (SourceSizedReference.nub symbols).length = symbols.length := of_decide_eq_true checked
    have permutation := CanonicalClasses.perm_of_nodup_subset_length (SourceSizedReference.nub symbols) symbols
      (SourceSizedReference.nub_nodup symbols)
      (fun symbol member => (SourceSizedReference.mem_nub symbols symbol).mp member) same
    exact permutation.nodup_iff.mp (SourceSizedReference.nub_nodup symbols)
  · intro distinct
    simp [distinctSymbols, SourceSizedReference.nub_eq_self symbols distinct]

/-- The source enables the shortcut only when every stored row has distinct symbols. -/
def unambiguous [DecidableEq Symbol] (automaton : Automaton State Symbol) (keys : List State) : Bool :=
  keys.all fun state => distinctSymbols ((automaton state).map Edge.label)

/-- The concrete source ambiguity gate supplies the required distinctness premise at every state. -/
theorem gate_unique [DecidableEq Symbol] (automaton : Automaton State Symbol) (keys : List State)
    (supported : ∀ state, state ∉ keys → automaton state = [])
    (enabled : unambiguous automaton keys = true) : ∀ state, ((automaton state).map Edge.label).Nodup := by
  intro state
  by_cases present : state ∈ keys
  · exact (distinctSymbols_exact _).mp (List.all_eq_true.mp enabled state present)
  · simp [supported state present]

/-- A complete ordinary prefix has no duplicates, including across levels. -/
theorem through_nodup (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms)
    (setDistinct : ∀ terms, (setList terms).Nodup) (shortcut : Bool)
    (unique : shortcut = true → ∀ state, ((automaton state).map Edge.label).Nodup)
    (depth : Nat) (root : State) : (through automaton setList shortcut depth root).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro index present
    exact (tables_distinct automaton plain setList setExact setDistinct shortcut unique index).1 root
  · apply List.pairwise_lt_range.imp
    intro first second less left leftIn right rightIn same
    have a := ((tables_exact automaton plain setList setExact shortcut first).1 root left |>.mp leftIn).2
    have b := ((tables_exact automaton plain setList setExact shortcut second).1 root right |>.mp rightIn).2
    subst right
    omega

/-- Ordinary prefix order increases source depth, independently of each level's set iteration order. -/
theorem through_ordered (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms) (shortcut : Bool)
    (depth : Nat) (root : State) :
    (through automaton setList shortcut depth root).Pairwise (fun first second => first.height ≤ second.height) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro index present
    apply List.pairwise_of_forall_mem_list
    intro first firstIn second secondIn
    have a := ((tables_exact automaton plain setList setExact shortcut index).1 root first |>.mp firstIn).2
    have b := ((tables_exact automaton plain setList setExact shortcut index).1 root second |>.mp secondIn).2
    omega
  · apply List.pairwise_lt_range.imp
    intro first second less left leftIn right rightIn
    have a := ((tables_exact automaton plain setList setExact shortcut first).1 root left |>.mp leftIn).2
    have b := ((tables_exact automaton plain setList setExact shortcut second).1 root right |>.mp rightIn).2
    omega

/-- The source plainTermsAtMost branch, including negative bounds and missing roots. -/
def terms [DecidableEq State] [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (setList : List (Term Symbol) → List (Term Symbol)) (keys : List State) (bound : Int) (root : State) : List (Term Symbol) :=
  if bound < 0 ∨ root ∉ keys then [] else
    collect automaton setList (unambiguous automaton keys) keys root 0 (bound.toNat + 1)

/-- The actual ordinary shortcut returns exactly all bounded accepted terms. -/
theorem terms_exact [DecidableEq State] [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms)
    (keys : List State) (supported : ∀ state, state ∉ keys → automaton state = [])
    (bound : Int) (root : State) (term : Term Symbol) :
    term ∈ terms automaton setList keys bound root ↔ Accepts automaton root term ∧ ((term.height - 1 : Nat) : Int) ≤ bound := by
  by_cases below : bound < 0
  · simp only [terms, below, true_or, ↓reduceIte, List.not_mem_nil, false_iff]
    omega
  · by_cases missing : root ∉ keys
    · have rejected : ¬Accepts automaton root term := by
        intro accepted
        cases accepted with
        | node edge children listed accepted guarded =>
            rw [supported root missing] at listed
            exact List.not_mem_nil listed
      simp [terms, missing, rejected]
    · have source : terms automaton setList keys bound root = through automaton setList (unambiguous automaton keys) bound.toNat root := by
        simp only [terms, below, missing, false_or, ↓reduceIte]
        rw [collect_exact automaton plain setList setExact _ keys supported]
        simp only [through, List.range_eq_range']
      rw [source, prefix_exact automaton plain setList setExact]
      have positive := term.height_pos
      exact and_congr Iff.rfl (by omega)

/-- The concrete ambiguity gate proves the ordinary result distinct and depth ordered. -/
theorem terms_distinct_ordered [DecidableEq State] [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms)
    (setDistinct : ∀ terms, (setList terms).Nodup)
    (keys : List State) (supported : ∀ state, state ∉ keys → automaton state = [])
    (bound : Int) (root : State) :
    (terms automaton setList keys bound root).Nodup ∧
      (terms automaton setList keys bound root).Pairwise (fun first second => first.height ≤ second.height) := by
  unfold terms
  split
  · exact ⟨.nil, .nil⟩
  · rw [collect_exact automaton plain setList setExact _ keys supported, ← List.range_eq_range']
    change (through automaton setList (unambiguous automaton keys) bound.toNat root).Nodup ∧
      (through automaton setList (unambiguous automaton keys) bound.toNat root).Pairwise _
    exact ⟨through_nodup automaton plain setList setExact setDistinct _ (gate_unique automaton keys supported) _ root,
      through_ordered automaton plain setList setExact _ _ root⟩

end MicroCFTA.SourceDenotationPlain
