import MicroCFTA.SourceSizedConjunctionSemantics
import MicroCFTA.SourceSizedConjunctionClosure
import MicroCFTA.SourceSizedConjunctionClassified

/-!
# Language of the computed conjunction table

Successful source preparation returns the literal rows for each reached key.
Its child keys are also stored. Induction on term height then identifies a
key's language with the intersection of its original states' languages.
The classification adapter derives all equality-position bounds.

This file proves language preservation. It does not prove enumeration order,
native container correspondence, or a bound on total native execution cost.
-/
namespace MicroCFTA.SourceSizedConjunctionLanguage
open Language SourceSizedDecided SourceSizedFiniteKeys SourceSizedConjunctionWorklist

variable {State Symbol Formula : Type}

/-- Interpret the actual classified rows with the direct-child equality worker. -/
def graph [DecidableEq Symbol] (rows : State → List (Row State Symbol (List (List Nat)))) :
    Automaton State Symbol := automaton rows SourceSizedConjunctionSemantics.holds

private theorem graph_node [DecidableEq Symbol]
    (rows : State → List (Row State Symbol (List (List Nat))))
    (state : State) (symbol : Symbol) (terms : List (Term Symbol)) :
    Accepts (graph rows) state (.node symbol terms) ↔
      ∃ row ∈ rows state, row.label = symbol ∧
        All₂ (Accepts (graph rows)) row.children terms ∧
        SourceSizedConjunctionSemantics.holds row.constraint (.node symbol terms) = true := by
  rw [accepts_node_iff]
  constructor
  · rintro ⟨edge, member, label, children, guard⟩
    obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp member
    exact ⟨row, rowIn, label, children, guard⟩
  · rintro ⟨row, member, label, children, guard⟩
    exact ⟨row.edge SourceSizedConjunctionSemantics.holds,
      List.mem_map.mpr ⟨row, member, rfl⟩, label, children, guard⟩

private theorem all₂_congr_on {Key Value : Type} {R S : Key → Value → Prop}
    (keys : List Key) (values : List Value)
    (same : ∀ key ∈ keys, ∀ value ∈ values, R key value ↔ S key value) :
    All₂ R keys values ↔ All₂ S keys values := by
  induction keys generalizing values with
  | nil =>
      cases values with
      | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
      | cons value values => constructor <;> intro impossible <;> cases impossible
  | cons key keys ih =>
      cases values with
      | nil => constructor <;> intro impossible <;> cases impossible
      | cons value values =>
          have head := same key (by simp) value (by simp)
          have tail := ih values (fun key keyIn value valueIn =>
            same key (List.mem_cons_of_mem _ keyIn) value (List.mem_cons_of_mem _ valueIn))
          constructor
          · intro related
            cases related with
            | cons first rest => exact .cons (head.mp first) (tail.mp rest)
          · intro related
            cases related with
            | cons first rest => exact .cons (head.mpr first) (tail.mpr rest)

private theorem lookup_absent {Key Payload : Type} [DecidableEq Key]
    (table : Table Key Symbol Payload) (key : Key) (absent : key ∉ table.map Prod.fst) :
    lookup table key = [] := by
  induction table with
  | nil => rfl
  | cons entry table ih =>
      have notHead : entry.1 ≠ key := by
        intro same
        exact absent (List.mem_cons.mpr (.inl same.symm))
      have notTail : key ∉ table.map Prod.fst := by
        intro member
        exact absent (List.mem_cons_of_mem _ member)
      change (if entry.1 = key then entry.2 else []) ++ lookup table key = []
      simp only [notHead, ↓reduceIte, List.nil_append, ih notTail]

private theorem lookup_function {Key Payload : Type} [DecidableEq Key]
    (table : Table Key Symbol Payload) (rows : Key → List (Row Key Symbol Payload))
    (distinct : (table.map Prod.fst).Nodup)
    (readback : ∀ entry ∈ table, entry.2 = rows entry.1)
    (key : Key) (present : key ∈ table.map Prod.fst) : lookup table key = rows key := by
  induction table with
  | nil => cases present
  | cons entry table ih =>
      have unique := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp present with same | previous
      · subst key
        change (if entry.1 = entry.1 then entry.2 else []) ++ lookup table entry.1 = rows entry.1
        simp only [↓reduceIte, lookup_absent table entry.1 unique.1, List.append_nil]
        exact readback entry (by simp)
      · have notHead : entry.1 ≠ key := by
          intro same
          exact unique.1 (same.symm ▸ previous)
        change (if entry.1 = key then entry.2 else []) ++ lookup table key = rows key
        simp only [notHead, ↓reduceIte, List.nil_append]
        exact ih unique.2 (fun member memberIn => readback member (List.mem_cons_of_mem _ memberIn)) previous

/-- Every stored key reads back the complete uncapped source conjunction rows. -/
theorem prepare_lookup [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned)
    (key : List State) (present : key ∈ returned.map Prod.fst) :
    lookup returned key = SourceSizedConjunctionRows.rows (lookup classified) key := by
  have valid := prepare_ready classified root returned success
  exact lookup_function returned (SourceSizedConjunctionRows.rows (lookup classified))
    valid.distinct valid.rowReadback key present

/-- Each child in an actual returned lookup row has a stored conjunction key. -/
theorem prepare_children [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned)
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ lookup returned key) (child : List State) (childIn : child ∈ row.children) :
    child ∈ returned.map Prod.fst := by
  obtain ⟨entry, entryIn, selected⟩ := List.mem_flatMap.mp member
  have rowIn : row ∈ entry.2 := by
    split at selected
    · exact selected
    · cases selected
  exact (SourceSizedConjunctionClosure.prepare_complete classified root returned success).childClosed
    entry entryIn row rowIn child childIn

/-- The computed returned graph denotes the intersection at every stored nonempty key. -/
theorem prepare_language [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol)
    (valid : ∀ owner row, row ∈ lookup classified owner →
      CompactGroups.ValidClasses row.children.length row.constraint)
    (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned)
    (key : List State) (present : key ∈ returned.map Prod.fst) (term : Term Symbol) :
    Accepts (graph (lookup returned)) key term ↔
      ∀ original ∈ key, Accepts (graph (lookup classified)) original term := by
  suffices bounded : ∀ (height : Nat) (term : Term Symbol), term.height ≤ height → ∀ key ∈ returned.map Prod.fst,
      Accepts (graph (lookup returned)) key term ↔
        ∀ original ∈ key, Accepts (graph (lookup classified)) original term from
    bounded term.height term (Nat.le_refl _) key present
  intro height
  induction height with
  | zero =>
      intro term bound key present
      have positive := Term.height_pos term
      omega
  | succ height ih =>
      intro term bound key present
      cases term with
      | node symbol terms =>
          have childBound : ∀ child ∈ terms, child.height ≤ height := by
            intro child member
            have below := height_le_forestHeight terms child member
            simp only [Term.height] at bound
            change forestHeight terms + 1 ≤ height + 1 at bound
            omega
          have recursive : ∀ row ∈ lookup returned key,
              All₂ (Accepts (graph (lookup returned))) row.children terms ↔
                All₂ (fun child value => ∀ state ∈ child,
                  Accepts (graph (lookup classified)) state value) row.children terms := by
            intro row member
            apply all₂_congr_on
            intro child childIn value valueIn
            exact ih value (childBound value valueIn) child
              (prepare_children classified root returned success key row member child childIn)
          have readback := prepare_lookup classified root returned success key present
          have nonempty := SourceSizedConjunctionClosure.prepare_nonempty
            classified root returned success key present
          have oneStep := SourceSizedConjunctionSemantics.rows_node_iff (lookup classified)
            valid key nonempty (Accepts (graph (lookup classified))) symbol terms
          constructor
          · intro accepted
            obtain ⟨row, member, label, children, guard⟩ :=
              (graph_node (lookup returned) key symbol terms).mp accepted
            have every := oneStep.mp ⟨row, readback ▸ member, label,
              (recursive row member).mp children, guard⟩
            intro original originalIn
            exact (graph_node (lookup classified) original symbol terms).mpr (every original originalIn)
          · intro every
            have one : ∀ original ∈ key, ∃ row ∈ lookup classified original,
                row.label = symbol ∧
                All₂ (Accepts (graph (lookup classified))) row.children terms ∧
                SourceSizedConjunctionSemantics.holds row.constraint (.node symbol terms) = true :=
              fun original originalIn =>
                (graph_node (lookup classified) original symbol terms).mp (every original originalIn)
            obtain ⟨row, rowIn, label, children, guard⟩ := oneStep.mpr one
            have member : row ∈ lookup returned key := readback.symm ▸ rowIn
            exact (graph_node (lookup returned) key symbol terms).mpr
              ⟨row, member, label, (recursive row member).mpr children, guard⟩

/-- The actual initial singleton key preserves its classified root language. -/
theorem prepare_root_language [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol)
    (valid : ∀ owner row, row ∈ lookup classified owner →
      CompactGroups.ValidClasses row.children.length row.constraint)
    (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) (term : Term Symbol) :
    Accepts (graph (lookup returned)) [root] term ↔
      Accepts (graph (lookup classified)) root term := by
  simpa only [List.mem_singleton, forall_eq] using prepare_language classified valid root returned success
    [root] (SourceSizedConjunctionClosure.prepare_root classified root returned success) term

/-- Actual complete classification supplies all position bounds to the language theorem. -/
theorem classify_prepare_language [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned)
    (key : List State) (present : key ∈ returned.map Prod.fst) (term : Term Symbol) :
    Accepts (graph (lookup returned)) key term ↔
      ∀ state ∈ key, Accepts (graph (lookup classified)) state term :=
  prepare_language classified
    (SourceSizedConjunctionClassified.lookup_bounded original classified classification)
    root returned success key present term

/-- The classification and exploration successes preserve the classified root language. -/
theorem classify_prepare_root_language [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) (term : Term Symbol) :
    Accepts (graph (lookup returned)) [root] term ↔
      Accepts (graph (lookup classified)) root term :=
  prepare_root_language classified
    (SourceSizedConjunctionClassified.lookup_bounded original classified classification)
    root returned success term

end MicroCFTA.SourceSizedConjunctionLanguage
