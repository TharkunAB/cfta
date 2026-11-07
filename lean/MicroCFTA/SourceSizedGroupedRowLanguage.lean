import MicroCFTA.SourceSizedGroupedChainOrder
import MicroCFTA.SourceSizedConjunctionSemantics

/-!
# Language and size of the literal grouped row worker

Each child class supplies its accepted terms and their exact sizes.
Actual equality groups share the same child-state read at each position.
The computed group fold then has the ordinary row language, with the actual
direct-child equality guard and the exact reconstructed node count.

The shared-child condition is local to the actual computed groups. There is
no supplied output generator, layout, or fuel witness. Native indexes, the
minimum table, and public dispatcher attachment remain separate.
-/

namespace MicroCFTA.SourceSizedGroupedRowLanguage

open Language RecursiveSize SourceSizedGroupedChainOrder CompactGroups CompactEdgeRanks

/-- Count every selected term once for each child slot that its group fills. -/
def selectionSize (selected : List (List Nat × Term Symbol)) : Nat :=
  (selected.map (fun group => group.1.length * nodeSize group.2)).sum

private theorem selectionSize_snoc (selected : List (List Nat × Term Symbol))
    (positions : List Nat) (term : Term Symbol) :
    selectionSize (selected ++ [(positions, term)]) =
      selectionSize selected + positions.length * nodeSize term := by
  simp [selectionSize]

private theorem slots_size (selected : List (List Nat × Term Symbol)) :
    ((CompactChildSlots.slots selected).map (fun entry => nodeSize entry.2)).sum =
      selectionSize selected := by
  induction selected using RecursiveSize.snoc_induction with
  | empty => rfl
  | step before last ih =>
      rw [slots_snoc, CompactChildSlots.addGroup_append, List.map_append, List.sum_append,
        List.map_map, Function.comp_def]
      change (last.1.map (fun _ => nodeSize last.2)).sum +
        ((CompactChildSlots.slots before).map (fun entry => nodeSize entry.2)).sum =
          selectionSize (before ++ [last])
      rw [sum_constant, ih]
      simp [selectionSize, Nat.add_comm]

private theorem forestSize_sum (values : List (Term Symbol)) :
    forestSize values = (values.map nodeSize).sum := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      change nodeSize first + forestSize rest = nodeSize first + (rest.map nodeSize).sum
      rw [ih]

/-- Actual group reconstruction preserves the sum of all duplicated child sizes. -/
theorem assemble_size (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (selected : List (Term Symbol))
    (length : (childGroups arity classes).length = selected.length) :
    nodeSize (assemble symbol arity (childGroups arity classes) selected) =
      selectionSize ((childGroups arity classes).zip selected) + 1 := by
  let pairs := (childGroups arity classes).zip selected
  have layout : pairs.map Prod.fst = childGroups arity classes :=
    List.map_fst_zip (Nat.le_of_eq length)
  have agrees := assignment_agrees (.node symbol []) pairs (by
    rw [layout]
    exact childGroups_nodup arity classes)
  have permutation := CompactChildSlots.slots_permutation
    (assignment (.node symbol []) pairs) pairs arity classes layout agrees
  have sizes := (permutation.map (fun entry => nodeSize entry.2)).sum_nat
  rw [slots_size] at sizes
  simp only [List.map_map, Function.comp_def] at sizes
  simp only [assemble, nodeSize, childrenOf]
  change forestSize ((List.range arity).map (assignment (.node symbol []) pairs)) + 1 =
    selectionSize pairs + 1
  rw [forestSize_sum, List.map_map, Function.comp_def, ← sizes]

private theorem mem_scaled_iff (inner : Nat → List (Term Symbol))
    (domain : Term Symbol → Prop)
    (exact : ∀ size term, term ∈ inner size ↔ domain term ∧ nodeSize term = size)
    (factor : Nat) (positive : 0 < factor) (size : Nat) (term : Term Symbol) :
    term ∈ scaled factor inner size ↔ domain term ∧ factor * nodeSize term = size := by
  by_cases one : factor = 1
  · subst factor
    simpa [scaled] using exact size term
  · constructor
    · intro member
      by_cases divisible : size % factor = 0
      · have accepted := (exact (size / factor) term).mp
          (by simpa [scaled, one, divisible] using member)
        refine ⟨accepted.1, ?_⟩
        rw [accepted.2]
        simpa [divisible] using Nat.div_add_mod size factor
      · simp [scaled, one, divisible] at member
    · rintro ⟨accepted, sizeEq⟩
      rw [← sizeEq]
      simpa [scaled, one, Nat.mul_div_cancel_left (nodeSize term) positive] using
        (exact (nodeSize term) term).mpr ⟨accepted, rfl⟩

private theorem groupClass_exact (classAt : State → Nat → List (Term Symbol))
    (domain : State → Term Symbol → Prop)
    (childExact : ∀ state size term,
      term ∈ classAt state size ↔ domain state term ∧ nodeSize term = size)
    (children : List State) (classes : List (List Nat))
    (valid : ValidClasses children.length classes)
    (shared : GroupsEqual (fun index => children[index]?) (childGroups children.length classes))
    (group : List Nat) (groupIn : group ∈ childGroups children.length classes)
    (size : Nat) (term : Term Symbol) :
    term ∈ groupClass classAt children group size ↔
      (∀ index ∈ group, positionDomain domain children index term) ∧
        group.length * nodeSize term = size := by
  have nonempty := childGroups_nonempty children.length classes valid group groupIn
  cases group with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      have within : first < children.length := List.mem_range.mp
        ((childGroups_positions children.length classes).mem_iff.mp
          (List.mem_flatten.mpr ⟨first :: rest, groupIn, by simp⟩))
      have read : children[first]? = some children[first] := List.getElem?_eq_getElem within
      have everyRead : ∀ index ∈ first :: rest, children[index]? = some children[first] := by
        intro index member
        exact (shared (first :: rest) groupIn index member first (by simp)).trans read
      simp only [groupClass, read]
      rw [mem_scaled_iff _ (domain children[first]) (childExact children[first])
        (first :: rest).length (by simp) size term]
      constructor
      · rintro ⟨accepted, count⟩
        exact ⟨fun index member => ⟨children[first], everyRead index member, accepted⟩, count⟩
      · rintro ⟨accepted, count⟩
        obtain ⟨state, found, accepted⟩ := accepted first (by simp)
        have same := Option.some.inj (found.symm.trans read)
        exact ⟨same ▸ accepted, count⟩

private theorem prefixes_exact
    (generate : List Nat → Nat → List (Term Symbol))
    (domain : List Nat → Term Symbol → Prop) (groups : List (List Nat))
    (groupExact : ∀ group ∈ groups, ∀ size term,
      term ∈ generate group size ↔ domain group term ∧ group.length * nodeSize term = size)
    (size : Nat) (selected : List (Term Symbol)) :
    selected ∈
      (groups.foldl (fun built group => extendForests built (generate group)) seed) size ↔
      All₂ domain groups selected ∧ selectionSize (groups.zip selected) + 1 = size := by
  induction groups using RecursiveSize.snoc_induction generalizing size selected with
  | empty =>
      constructor
      · intro member
        have one : size = 1 := by
          by_cases same : size = 1
          · exact same
          · simp [seed, same] at member
        subst size
        have empty : selected = [] := by simpa [seed] using member
        subst selected
        exact ⟨.nil, rfl⟩
      · rintro ⟨related, count⟩
        cases related
        have one : size = 1 := by simpa [selectionSize] using count.symm
        simp [seed, one]
  | step groups last ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have earlierExact := fun group present => groupExact group (List.mem_append_left [last] present)
      constructor
      · intro member
        obtain ⟨prefixSize, within, before, beforeIn, term, termIn, same⟩ :=
          (by simpa [extendForests, List.mem_flatMap, List.mem_map] using member :
            ∃ prefixSize, prefixSize < size + 1 ∧ ∃ before,
              before ∈ (groups.foldl
                (fun built group => extendForests built (generate group)) seed) prefixSize ∧
              ∃ term, term ∈ generate last (size - prefixSize) ∧ before ++ [term] = selected)
        have beforeFacts := (ih earlierExact prefixSize before).mp beforeIn
        have lastFacts := (groupExact last (by simp) (size - prefixSize) term).mp termIn
        subst selected
        refine ⟨(all₂_snoc_iff domain groups last _).mpr
          ⟨before, term, rfl, beforeFacts.1, lastFacts.1⟩, ?_⟩
        rw [List.zip_append beforeFacts.1.length_eq]
        simp only [List.zip_cons_cons, List.zip_nil_left]
        rw [selectionSize_snoc]
        omega
      · rintro ⟨related, count⟩
        obtain ⟨before, term, rfl, beforeAccepted, lastAccepted⟩ :=
          (all₂_snoc_iff domain groups last selected).mp related
        rw [List.zip_append beforeAccepted.length_eq] at count
        simp only [List.zip_cons_cons, List.zip_nil_left] at count
        rw [selectionSize_snoc] at count
        let prefixSize := selectionSize (groups.zip before) + 1
        have within : prefixSize < size + 1 := by dsimp [prefixSize]; omega
        have lastSize : last.length * nodeSize term = size - prefixSize := by
          dsimp [prefixSize]
          omega
        apply List.mem_flatMap.mpr
        refine ⟨prefixSize, List.mem_range.mpr within, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨before, (ih earlierExact prefixSize before).mpr ⟨beforeAccepted, rfl⟩, ?_⟩
        exact List.mem_map.mpr ⟨term,
          (groupExact last (by simp) _ term).mpr ⟨lastAccepted, lastSize⟩, rfl⟩

private theorem paired_zip {A B : Type} {relation : A → B → Prop}
    {left : List A} {right : List B} (related : All₂ relation left right) :
    ∀ pair ∈ left.zip right, relation pair.1 pair.2 := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      intro pair present
      rcases List.mem_cons.mp present with same | later
      · cases same; exact head
      · exact ih pair later

private theorem choose_paired {A B : Type} (items : List A) (relation : A → B → Prop)
    (each : ∀ item ∈ items, ∃ value, relation item value) :
    ∃ values, All₂ relation items values := by
  induction items with
  | nil => exact ⟨[], .nil⟩
  | cons item rest ih =>
      obtain ⟨first, accepted⟩ := each item (by simp)
      obtain ⟨tail, related⟩ := ih
        (fun value present => each value (List.mem_cons_of_mem item present))
      exact ⟨first :: tail, .cons accepted related⟩

private theorem assemble_of_agrees (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (selected : List (Term Symbol)) (length : (childGroups arity classes).length = selected.length)
    (value : Nat → Term Symbol)
    (agrees : CompactChildSlots.Agrees value ((childGroups arity classes).zip selected)) :
    assemble symbol arity (childGroups arity classes) selected =
      .node symbol ((List.range arity).map value) := by
  have layout : ((childGroups arity classes).zip selected).map Prod.fst =
      childGroups arity classes := List.map_fst_zip (Nat.le_of_eq length)
  exact Option.some.inj ((construct_generated symbol arity classes _ layout).symm.trans
    (construct_exact symbol value _ arity classes layout agrees))

/-- The computed grouped class has the original ordered row language, its
actual equality guard, and the exact reconstructed node size. -/
theorem mem_rowClass_iff {State Symbol : Type} [DecidableEq Symbol]
    (classAt : State → Nat → List (Term Symbol))
    (domain : State → Term Symbol → Prop)
    (childExact : ∀ state size term,
      term ∈ classAt state size ↔ domain state term ∧ nodeSize term = size)
    (symbol : Symbol) (children : List State) (classes : List (List Nat))
    (valid : ValidClasses children.length classes)
    (shared : GroupsEqual (fun index => children[index]?) (childGroups children.length classes))
    (size : Nat) (term : Term Symbol) :
    term ∈ rowClass classAt symbol children classes size ↔
      ∃ values, term = .node symbol values ∧ All₂ domain children values ∧
        SourceSizedConjunctionSemantics.holds classes term = true ∧ nodeSize term = size := by
  let groups := childGroups children.length classes
  let groupDomain := fun (group : List Nat) (selected : Term Symbol) => ∀ index ∈ group,
    positionDomain domain children index selected
  have exactGroups := groupClass_exact classAt domain childExact children classes valid shared
  have exactPrefixes := prefixes_exact (groupClass classAt children) groupDomain groups exactGroups
  constructor
  · intro member
    obtain ⟨selected, selectedIn, rfl⟩ := List.mem_map.mp member
    have accepted := (exactPrefixes size selected).mp selectedIn
    let pairs := groups.zip selected
    let values := childrenOf symbol children.length pairs
    have layout : pairs.map Prod.fst = groups := List.map_fst_zip (Nat.le_of_eq accepted.1.length_eq)
    have agree := generated_agreement symbol children.length classes pairs layout
    have arity : values.length = children.length := by simp [values, childrenOf]
    have selections : ∀ group ∈ groups,
        GroupSelection (positionDomain domain children)
          (childValue (.node symbol []) values) group := by
      intro group groupIn
      obtain ⟨pair, pairIn, same⟩ := List.mem_map.mp (layout.symm ▸ groupIn)
      have selectedAccepted := paired_zip accepted.1 pair pairIn
      refine ⟨pair.2, ?_⟩
      intro index indexIn
      have inPair : index ∈ pair.1 := same.symm ▸ indexIn
      refine ⟨selectedAccepted index inPair, ?_⟩
      change (childrenOf symbol children.length pairs)[index]?.getD (.node symbol []) = pair.2
      exact congrArg (fun found : Option (Term Symbol) => found.getD (.node symbol []))
        (agree pair pairIn index inPair)
    have ordinary := (groupSelections_exact (positionDomain domain children)
      (childValue (.node symbol []) values) children.length classes valid).mp selections
    refine ⟨values, rfl,
      (all₂_positions domain children values (.node symbol [])).mpr
        ⟨arity.symm, fun index within => ordinary.1 index (by omega)⟩, ?_, ?_⟩
    · exact (SourceSizedConjunctionSemantics.holds_node symbol values classes
        (by rw [arity]; exact valid)).mpr ordinary.2
    · exact (assemble_size symbol children.length classes selected accepted.1.length_eq).trans accepted.2
  · rintro ⟨values, rfl, related, guard, count⟩
    have arity := related.length_eq
    have indexed := (all₂_positions domain children values (.node symbol [])).mp related
    have equalities := (SourceSizedConjunctionSemantics.holds_node symbol values classes
      (by rw [← arity]; exact valid)).mp guard
    let value := childValue (.node symbol []) values
    have selections := (groupSelections_exact (positionDomain domain children) value
      children.length classes valid).mpr ⟨fun index within => indexed.2 index (by omega), equalities⟩
    obtain ⟨selected, paired⟩ := choose_paired groups
      (fun group selected => groupDomain group selected ∧ ∀ index ∈ group, value index = selected) (by
        intro group groupIn
        obtain ⟨selected, facts⟩ := selections group groupIn
        exact ⟨selected, ⟨fun index present => (facts index present).1,
          fun index present => (facts index present).2⟩⟩)
    have acceptedGroups := paired.imp (fun _ _ facts => facts.1)
    have agree : CompactChildSlots.Agrees value (groups.zip selected) := by
      intro pair present index within
      exact (paired_zip paired pair present).2 index within
    have rebuilt := assemble_of_agrees symbol children.length classes selected paired.length_eq value agree
    have original : assemble symbol children.length groups selected = .node symbol values := by
      rw [rebuilt, arity]
      apply congrArg (Term.node symbol)
      change (List.range values.length).map
        (fun index => values[index]?.getD (.node symbol [])) = values
      exact rebuild_values (.node symbol []) values
    apply List.mem_map.mpr
    refine ⟨selected, (exactPrefixes size selected).mpr ⟨acceptedGroups, ?_⟩, original⟩
    have reconstructed := assemble_size symbol children.length classes selected paired.length_eq
    rw [original] at reconstructed
    exact reconstructed.symm.trans count

end MicroCFTA.SourceSizedGroupedRowLanguage
