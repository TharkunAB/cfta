import MicroCFTA.SourceSizedConjunctionRows
import MicroCFTA.SourceSizedEqualities

/-!
# One-step language of literal conjunction rows

The guard checks the actual direct-child paths. The one-step law relates
the computed intersection rows to one accepted original row per owner.
It does not assume a finite state type or prove the worklist language law.
-/

namespace MicroCFTA.SourceSizedConjunctionSemantics

open Language SourceSizedDecided

/-- Represent every child position by its direct-child path. -/
def paths (classes : List (List Nat)) : List (List (List Nat)) :=
  classes.map (fun positions => positions.map (fun index => [index]))

/-- Run the source equality worker on the represented direct-child paths. -/
def holds [DecidableEq Symbol] (classes : List (List Nat)) (term : Term Symbol) : Bool :=
  SourceSizedEqualities.equalitiesHold (some (paths classes)) term

/-- Bounded direct-child paths hold exactly when their selected children agree. -/
theorem holds_node [DecidableEq Symbol] (symbol : Symbol) (terms : List (Term Symbol))
    (classes : List (List Nat)) (valid : CompactGroups.ValidClasses terms.length classes) :
    holds classes (.node symbol terms) = true ↔
      CompactGroups.GroupsEqual (CompactEdgeRanks.childValue (.node symbol []) terms) classes := by
  have worker : holds classes (.node symbol terms) =
      (paths classes).all (SymbolicDriver.classTest (.node symbol terms)) := by
    simp only [holds, SourceSizedEqualities.equalitiesHold]
    congr 1
    funext positions
    exact SourceSizedEqualities.classHolds_eq_classTest _ positions
  rw [worker]
  apply SourceCompactGuards.parsed_guard
  exact (SourceCompactGuards.parse_exact terms.length (paths classes) classes).mpr ⟨rfl, valid⟩

private theorem all₂_lookup_iff {State Value : Type} (domain : State → Value → Prop)
    (states : List State) (values : List Value) (fallback : Value) :
    All₂ domain states values ↔ states.length = values.length ∧
      ∀ index state, states[index]? = some state →
        domain state (CompactEdgeRanks.childValue fallback values index) := by
  rw [CompactEdgeRanks.all₂_positions domain states values fallback]
  constructor
  · rintro ⟨arity, indexed⟩
    refine ⟨arity, ?_⟩
    intro index state read
    obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp read
    obtain ⟨chosen, chosenRead, accepted⟩ := indexed index (by omega)
    have same := Option.some.inj (chosenRead.symm.trans read)
    exact same ▸ accepted
  · rintro ⟨arity, indexed⟩
    refine ⟨arity, ?_⟩
    intro index within
    have inStates : index < states.length := by omega
    exact ⟨states[index], List.getElem?_eq_getElem inStates,
      indexed index states[index] (List.getElem?_eq_getElem inStates)⟩

/-- Ordered children and the actual guard give the indexed assignment meaning. -/
theorem node_assignment_iff {State Symbol : Type} [DecidableEq Symbol]
    (row : Row State Symbol (List (List Nat)))
    (valid : CompactGroups.ValidClasses row.children.length row.constraint)
    (domain : State → Term Symbol → Prop) (symbol : Symbol) (terms : List (Term Symbol))
    (arity : row.children.length = terms.length) :
    (All₂ domain row.children terms ∧ holds row.constraint (.node symbol terms) = true) ↔
      SourceSizedConjunctionRows.assignmentHolds row domain
        (CompactEdgeRanks.childValue (.node symbol []) terms) := by
  unfold SourceSizedConjunctionRows.assignmentHolds
  rw [all₂_lookup_iff domain row.children terms (.node symbol []),
    holds_node symbol terms row.constraint (by rw [← arity]; exact valid)]
  simp [arity]

private theorem related_member_left {A B : Type} {relation : A → B → Prop}
    {left : List A} {right : List B} (related : All₂ relation left right)
    (owner : A) (present : owner ∈ left) : ∃ value ∈ right, relation owner value := by
  induction related with
  | nil => cases present
  | @cons first value rest tail head paired ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨value, by simp, head⟩
      · obtain ⟨chosen, chosenIn, related⟩ := ih later
        exact ⟨chosen, List.mem_cons_of_mem value chosenIn, related⟩

private theorem related_member_right {A B : Type} {relation : A → B → Prop}
    {left : List A} {right : List B} (related : All₂ relation left right)
    (value : B) (present : value ∈ right) : ∃ owner ∈ left, relation owner value := by
  induction related with
  | nil => cases present
  | @cons owner first rest tail head paired ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨owner, by simp, head⟩
      · obtain ⟨chosen, chosenIn, related⟩ := ih later
        exact ⟨chosen, List.mem_cons_of_mem owner chosenIn, related⟩

private theorem choose_related {A B : Type} (lookup : A → List B) (property : B → Prop)
    (owners : List A) (available : ∀ owner ∈ owners, ∃ row ∈ lookup owner, property row) :
    ∃ selected, All₂ (fun owner row => row ∈ lookup owner ∧ property row) owners selected := by
  induction owners with
  | nil => exact ⟨[], .nil⟩
  | cons owner rest ih =>
      obtain ⟨first, stored, accepted⟩ := available owner (by simp)
      obtain ⟨tail, paired⟩ := ih
        (fun state present => available state (List.mem_cons_of_mem owner present))
      exact ⟨first :: tail, .cons ⟨stored, accepted⟩ paired⟩

variable {State Symbol : Type} [DecidableEq State] [Ord State] [DecidableEq Symbol]

/-- Literal row intersection preserves one-step acceptance of a common forest. -/
theorem intersection_node_iff (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat))))
    (domain : State → Term Symbol → Prop) (symbol : Symbol) (terms : List (Term Symbol))
    (arities : ∀ member ∈ first :: others, member.children.length = terms.length)
    (valid : ∀ member ∈ first :: others,
      CompactGroups.ValidClasses member.children.length member.constraint) :
    (All₂ (fun child term => ∀ state ∈ child, domain state term)
        (SourceSizedConjunctionRows.intersection first others).children terms ∧
      holds (SourceSizedConjunctionRows.intersection first others).constraint (.node symbol terms) = true) ↔
      ∀ member ∈ first :: others,
        All₂ domain member.children terms ∧ holds member.constraint (.node symbol terms) = true := by
  have firstArity := arities first (by simp)
  have sameArity : ∀ member ∈ first :: others,
      member.children.length = first.children.length := by
    intro member present
    exact (arities member present).trans firstArity.symm
  have allValid : CompactGroups.ValidClasses first.children.length
      ((first :: others).flatMap fun member => member.constraint) := by
    intro positions present index indexIn
    obtain ⟨member, memberIn, classIn⟩ := List.mem_flatMap.mp present
    rw [← sameArity member memberIn]
    exact valid member memberIn positions classIn index indexIn
  rw [node_assignment_iff _ (SourceSizedConjunctionRows.intersection_bounded first others)
    (fun child term => ∀ state ∈ child, domain state term) symbol terms
    ((SourceSizedConjunctionRows.intersection_arity first others).trans firstArity)]
  apply (SourceSizedConjunctionRows.intersection_exact first others sameArity allValid domain
    (CompactEdgeRanks.childValue (.node symbol []) terms)).trans
  constructor
  · intro accepted member present
    exact (node_assignment_iff member (valid member present) domain symbol terms
      (arities member present)).mpr (accepted member present)
  · intro accepted member present
    exact (node_assignment_iff member (valid member present) domain symbol terms
      (arities member present)).mp (accepted member present)

/-- Computed conjunction rows accept a node exactly when every key owner has
an original row that accepts the same node. -/
theorem rows_node_iff (lookup : State → List (Row State Symbol (List (List Nat))))
    (valid : ∀ owner row, row ∈ lookup owner →
      CompactGroups.ValidClasses row.children.length row.constraint)
    (key : List State) (nonempty : key ≠ [])
    (domain : State → Term Symbol → Prop) (symbol : Symbol) (terms : List (Term Symbol)) :
    (∃ output ∈ SourceSizedConjunctionRows.rows lookup key,
      output.label = symbol ∧
      All₂ (fun child term => ∀ state ∈ child, domain state term) output.children terms ∧
      holds output.constraint (.node symbol terms) = true) ↔
      ∀ owner ∈ key, ∃ row ∈ lookup owner, row.label = symbol ∧
        All₂ domain row.children terms ∧ holds row.constraint (.node symbol terms) = true := by
  constructor
  · rintro ⟨output, present, label, children, guard⟩
    obtain ⟨first, others, tupleIn, rfl⟩ :=
      (SourceSizedConjunctionRows.mem_rows lookup key output).mp present
    have firstArity : first.children.length = terms.length :=
      (SourceSizedConjunctionRows.intersection_arity first others).symm.trans children.length_eq
    have arities : ∀ member ∈ first :: others, member.children.length = terms.length := by
      intro member memberIn
      exact ((SourceSizedConjunctionTuples.common_shape lookup key _ tupleIn
        member first memberIn (by simp)).2).trans firstArity
    have tupleValid : ∀ member ∈ first :: others,
        CompactGroups.ValidClasses member.children.length member.constraint := by
      intro member memberIn
      obtain ⟨owner, _, stored⟩ :=
        SourceSizedConjunctionTuples.row_origin lookup key _ tupleIn member memberIn
      exact valid owner member stored
    have accepted := (intersection_node_iff first others domain symbol terms arities tupleValid).mp
      ⟨children, guard⟩
    intro owner ownerIn
    obtain ⟨member, memberIn, stored⟩ := related_member_left
      (SourceSizedConjunctionTuples.tuple_origin lookup key _ tupleIn) owner ownerIn
    refine ⟨member, stored, ?_, accepted member memberIn⟩
    exact ((SourceSizedConjunctionTuples.common_shape lookup key _ tupleIn
      member first memberIn (by simp)).1).trans label
  · intro accepted
    cases key with
    | nil => exact False.elim (nonempty rfl)
    | cons owner owners =>
        let property := fun row : Row State Symbol (List (List Nat)) =>
          row.label = symbol ∧ All₂ domain row.children terms ∧
            holds row.constraint (.node symbol terms) = true
        obtain ⟨first, stored, firstLabel, firstChildren, firstGuard⟩ := accepted owner (by simp)
        obtain ⟨others, paired⟩ := choose_related lookup property owners
          (fun state present => accepted state (List.mem_cons_of_mem owner present))
        have filtered : All₂ (fun state row => row ∈ lookup state ∧
            SourceSizedConjunctionTuples.sameToken first row = true) owners others := by
          apply paired.imp
          intro state row facts
          exact ⟨facts.1, (SourceSizedConjunctionTuples.sameToken_iff first row).mpr
            ⟨firstLabel.trans facts.2.1.symm,
              firstChildren.length_eq.trans facts.2.2.1.length_eq.symm⟩⟩
        have tupleIn : first :: others ∈
            SourceSizedConjunctionTuples.tuples lookup (owner :: owners) :=
          (SourceSizedConjunctionTuples.mem_tuples_cons lookup owner owners _).mpr
            ⟨first, stored, others, rfl, filtered⟩
        have every : ∀ member ∈ first :: others, property member := by
          intro member present
          rcases List.mem_cons.mp present with rfl | later
          · exact ⟨firstLabel, firstChildren, firstGuard⟩
          · obtain ⟨_, _, facts⟩ := related_member_right paired member later
            exact facts.2
        have arities : ∀ member ∈ first :: others, member.children.length = terms.length :=
          fun member present => (every member present).2.1.length_eq
        have tupleValid : ∀ member ∈ first :: others,
            CompactGroups.ValidClasses member.children.length member.constraint := by
          intro member memberIn
          obtain ⟨state, _, original⟩ := SourceSizedConjunctionTuples.row_origin lookup
            (owner :: owners) _ tupleIn member memberIn
          exact valid state member original
        refine ⟨SourceSizedConjunctionRows.intersection first others,
          (SourceSizedConjunctionRows.mem_rows lookup (owner :: owners) _).mpr
            ⟨first, others, tupleIn, rfl⟩, firstLabel, ?_⟩
        exact (intersection_node_iff first others domain symbol terms arities tupleValid).mpr
          (fun member present => (every member present).2)

end MicroCFTA.SourceSizedConjunctionSemantics
