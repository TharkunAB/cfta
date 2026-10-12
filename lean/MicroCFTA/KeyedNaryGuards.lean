import MicroCFTA.KeyedNaryAlignment
import MicroCFTA.KeyedGuards

/-!
# Original typed occurrence guards for flat keyed bodies

A label uses constructor metadata. A plain pay changes only the size guard.
The original metadata preserves the minimum, size flags, and used flags of
the value lowering. The termless flags remain separate.
-/
namespace MicroCFTA.KeyedNaryGuards
open KeyedNaryAlignment
open OccurrenceGuard (Shape Summary summary)

/-- Flat choice metadata keeps all source alternatives, including empty ones. -/
def alternatives : List Shape → Shape
  | [] => .source []
  | [only] => only
  | first :: second :: rest => .choice first (alternatives (second :: rest))

/-- Read occurrence metadata from the original typed body before value lowering. -/
def shape (token : Nat) (known : GroupedProbe.Table Key) : Recipe Key Root Symbol α → Shape
  | .finite source | .retained _ _ source => .source (SourceMinimum.minimum source).toList
  | .occurrence key => .occurrence token (known key).join
  | .map _ inner => .map (shape token known inner)
  | .pay inner => .pay (shape token known inner)
  | .choice _ branches => alternatives (List.ofFn fun index => shape token known (branches index))
  | .ap functions arguments => .product (shape token known functions) (shape token known arguments)
  | .label _ inner => .constructor (shape token known inner)

/-- These fields survive value lowering; termless flags need not survive it. -/
def SameSize (left right : Shape) : Prop :=
  (summary left).minimum = (summary right).minimum ∧
  (summary left).unguarded = (summary right).unguarded ∧
  (summary left).used = (summary right).used

/-- Binary metadata composition preserves all fields relevant to size and use. -/
theorem choice_same (left right otherLeft otherRight : Shape)
    (leftSame : SameSize left otherLeft) (rightSame : SameSize right otherRight) :
    SameSize (.choice left right) (.choice otherLeft otherRight) := by
  rcases leftSame with ⟨lm, lg, lu⟩
  rcases rightSame with ⟨rm, rg, ru⟩
  simp only [SameSize, summary, lm, lg, lu, rm, rg, ru, and_self]

/-- The flat metadata fold preserves pointwise equality of the three relevant fields. -/
theorem alternatives_same (names : List Name) (left right : Name → Shape)
    (same : ∀ name ∈ names, SameSize (left name) (right name)) :
    SameSize (alternatives (names.map left)) (alternatives (names.map right)) := by
  induction names with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons first rest ih =>
      cases rest with
      | nil => exact same first (by simp)
      | cons second rest =>
          apply choice_same
          · exact same first (by simp)
          · exact ih (fun name present => same name (by simp [present]))

/-- Metadata erasure commutes with the ordered source choice lowering. -/
theorem lowered_alternatives (token : Nat) (known : GroupedProbe.Table Key)
    (branches : List (KeyedSource.Recipe Key Root α)) :
    KeyedGuards.shape token known (KeyedNaryAlignment.alternatives branches) =
      alternatives (branches.map (KeyedGuards.shape token known)) := by
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          simp only [KeyedNaryAlignment.alternatives, KeyedGuards.shape, List.map_cons, alternatives]
          rw [ih]
          rfl

/-- Labels and pays agree on size and use while keeping distinct term-growth metadata. -/
theorem lowered_summary (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) :
    SameSize (shape token known recipe) (KeyedGuards.shape token known (valueRecipe recipe)) := by
  induction recipe with
  | finite source | retained mass positive source | occurrence key => exact ⟨rfl, rfl, rfl⟩
  | map transform inner ih => exact ih
  | pay inner ih | label symbol inner ih =>
      exact ⟨congrArg (Option.map (· + 1)) ih.1, rfl, ih.2.2⟩
  | choice count branches ih =>
      simp only [shape, valueRecipe, lowered_alternatives, List.map_ofFn]
      simpa only [List.map_ofFn, Function.comp_def, id_eq] using
        alternatives_same (List.ofFn id)
          (fun index => shape token known (branches index))
          (fun index => KeyedGuards.shape token known (valueRecipe (branches index)))
          (fun index _ => ih index)
  | ap functions arguments ihf iha =>
      rcases ihf with ⟨fm, fg, fu⟩
      rcases iha with ⟨am, ag, au⟩
      simp only [SameSize, shape, valueRecipe, KeyedGuards.shape, summary, OccurrenceGuard.beside,
        fm, fg, fu, am, ag, au, and_self]

/-- The original body uses exactly the settled minimum of its value-size expression. -/
theorem shape_minimum (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) :
    (summary (shape token known recipe)).minimum =
      (GroupedMinimum.evaluate (KeyedSource.minimumExpr (valueRecipe recipe)) known).join :=
  (lowered_summary token known recipe).1.trans (KeyedGuards.shape_minimum token known (valueRecipe recipe))

/-- The original size-unguarded token test is the exact semantic class guard. -/
theorem size_guard_exact (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) :
    KeyedSource.guarded (valueRecipe recipe) known = true ↔ token ∉ (summary (shape token known recipe)).unguarded := by
  rw [(lowered_summary token known recipe).2.1]
  exact KeyedGuards.size_guard_exact token known (valueRecipe recipe)

/-- The flat minimum uses the source fold and ignores alternatives with no finite member. -/
theorem alternatives_minimum (branches : List Shape) :
    (summary (alternatives branches)).minimum =
      (branches.map fun branch => (summary branch).minimum).foldr MinimumSize.best none := by
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp only [alternatives, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          cases (summary first).minimum <;> rfl
      | cons second rest =>
          change MinimumSize.best (summary first).minimum (summary (alternatives (second :: rest))).minimum = _
          rw [ih]
          rfl

/-- A flat choice retains a size-unguarded token exactly when one child retains it. -/
theorem alternatives_unguarded (branches : List Shape) (token : Nat) :
    token ∈ (summary (alternatives branches)).unguarded ↔ ∃ branch ∈ branches, token ∈ (summary branch).unguarded := by
  induction branches with
  | nil => simp [alternatives, summary]
  | cons first rest ih =>
      cases rest with
      | nil => simp [alternatives]
      | cons second rest =>
          simp only [alternatives, summary, OccurrenceGuard.union, List.mem_eraseDups, List.mem_append]
          rw [ih]
          simp

/-- Every termless token of a flat choice comes from an original alternative. -/
theorem alternatives_termless (branches : List Shape) (token : Nat) :
    token ∈ (summary (alternatives branches)).termless ↔ ∃ branch ∈ branches, token ∈ (summary branch).termless := by
  induction branches with
  | nil => simp [alternatives, summary]
  | cons first rest ih =>
      cases rest with
      | nil => simp [alternatives]
      | cons second rest =>
          simp only [alternatives, summary, OccurrenceGuard.union, List.mem_eraseDups, List.mem_append]
          rw [ih]
          simp

/-- Choice term growth requires every branch; labels and applications add a node. -/
def termGuard : Recipe Key Root Symbol α → Bool
  | .finite _ | .retained .. => true
  | .occurrence _ => false
  | .map _ inner | .pay inner => termGuard inner
  | .choice _ branches => (List.ofFn fun index => termGuard (branches index)).all id
  | .ap .. | .label .. => true

/-- The source termless test reads the original syntax, including constructor labels. -/
theorem term_guard_exact (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) :
    termGuard recipe = true ↔ token ∉ (summary (shape token known recipe)).termless := by
  induction recipe with
  | finite source | retained mass positive source => simp [termGuard, shape, summary]
  | occurrence key => simp [termGuard, shape, summary]
  | map transform inner ih | pay inner ih => exact ih
  | label symbol inner ih | ap functions arguments ihf iha => simp [termGuard, shape, summary]
  | choice count branches ih =>
      simp only [termGuard, shape, alternatives_termless, List.mem_ofFn, List.all_eq_true, id_eq]
      constructor
      · intro all ⟨branch, ⟨index, same⟩, member⟩
        subst branch
        exact (ih index).mp (all _ ⟨index, rfl⟩) member
      · intro absent result ⟨index, same⟩
        rw [← same]
        apply (ih index).mpr
        intro member
        exact absent ⟨_, ⟨index, rfl⟩, member⟩

/-- The family-use flag checks every original branch and product operand. -/
def used : Recipe Key Root Symbol α → Bool
  | .finite _ | .retained .. => false
  | .occurrence _ => true
  | .map _ inner | .pay inner | .label _ inner => used inner
  | .choice _ branches => (List.ofFn fun index => used (branches index)).any id
  | .ap functions arguments => used functions || used arguments

/-- Every used token of a flat choice comes from an original alternative. -/
theorem alternatives_used (branches : List Shape) (token : Nat) :
    token ∈ (summary (alternatives branches)).used ↔ ∃ branch ∈ branches, token ∈ (summary branch).used := by
  induction branches with
  | nil => simp [alternatives, summary]
  | cons first rest ih =>
      cases rest with
      | nil => simp [alternatives]
      | cons second rest =>
          simp only [alternatives, summary, OccurrenceGuard.union, List.mem_eraseDups, List.mem_append]
          rw [ih]
          simp

/-- The finite shortcut reads exactly the original body's used-token flag. -/
theorem used_exact (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) :
    used recipe = true ↔ token ∈ (summary (shape token known recipe)).used := by
  induction recipe with
  | finite source | retained mass positive source => simp [used, shape, summary]
  | occurrence key => simp [used, shape, summary]
  | map transform inner ih | pay inner ih | label symbol inner ih => exact ih
  | ap functions arguments ihf iha => simp [used, shape, summary, OccurrenceGuard.union, Bool.or_eq_true, ihf, iha]
  | choice count branches ih =>
      simp only [used, shape, alternatives_used, List.mem_ofFn, List.any_eq_true, id_eq]
      constructor
      · rintro ⟨result, ⟨index, same⟩, yes⟩
        exact ⟨_, ⟨index, rfl⟩, (ih index).mp (same ▸ yes)⟩
      · rintro ⟨branch, ⟨index, same⟩, member⟩
        exact ⟨_, ⟨index, rfl⟩, (ih index).mpr (same ▸ member)⟩

/-- The source rejects either a size-unguarded occurrence or a termless occurrence. -/
def unguarded (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) : Prop :=
  token ∈ (summary (shape token known recipe)).unguarded ∨ token ∈ (summary (shape token known recipe)).termless

/-- The combined original-syntax rejection check has two independent obligations. -/
theorem accepted_guards (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) :
    ¬unguarded token known recipe ↔ KeyedSource.guarded (valueRecipe recipe) known = true ∧ termGuard recipe = true := by
  rw [size_guard_exact token known recipe, term_guard_exact token known recipe]
  exact not_or

/-- Public acceptance discharges each guard needed by the complete family semantics. -/
theorem family_guards (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Symbol Root)
    (accepted : ∀ key, ¬unguarded token (KeyedSource.minima keys complete (valueProgram program)) (program key)) :
    ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true :=
  fun key => ((accepted_guards token _ _).mp (accepted key)).1

/-- The original used flag agrees with the value compiler despite label erasure. -/
theorem lowered_used (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) :
    used recipe = KeyedGuards.used (valueRecipe recipe) := by
  apply Bool.eq_iff_iff.mpr
  rw [used_exact token known recipe, KeyedGuards.used_exact token known (valueRecipe recipe),
    (lowered_summary token known recipe).2.2]

/-- The executable source rejection test is exactly the conjunction of both guards. -/
theorem public_guard_exact (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α) :
    OccurrenceGuard.isUnguarded token (shape token known recipe) = false ↔
      KeyedSource.guarded (valueRecipe recipe) known = true ∧ termGuard recipe = true := by
  rw [size_guard_exact token known recipe, term_guard_exact token known recipe]
  simp [OccurrenceGuard.isUnguarded]

/-- The executable per-key source check discharges the semantic class guards. -/
theorem public_family_guards (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Symbol Root)
    (accepted : ∀ key, OccurrenceGuard.isUnguarded token
      (shape token (KeyedSource.minima keys complete (valueProgram program)) (program key)) = false) :
    ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true :=
  fun key => ((public_guard_exact token _ _).mp (accepted key)).1

/-- Public acceptance ensures strict size and term growth in every original context. -/
theorem context_growth (token : Nat) (known : GroupedProbe.Table Key) (recipe : Recipe Key Root Symbol α)
    (accepted : OccurrenceGuard.isUnguarded token (shape token known recipe) = false)
    (context : OccurrenceGuard.Context) (present : context ∈ OccurrenceGuard.contexts (shape token known recipe))
    (same : context.token = token) (holeSize holeNodes : Nat) :
    holeSize < holeSize + context.size ∧ holeNodes < holeNodes + context.nodes :=
  OccurrenceGuard.guarded_context_growth _ token accepted context present same holeSize holeNodes

/-- A label accepts an occurrence even though its value lowering uses pay. -/
theorem labelled_occurrence (token : Nat) (known : GroupedProbe.Table Key) (key : Key) (symbol : Symbol) :
    OccurrenceGuard.isUnguarded token
      (shape token known (Recipe.label (Root := Root) symbol (.occurrence key))) = false ∧
      KeyedGuards.termGuard (valueRecipe (Recipe.label (Root := Root) symbol (.occurrence key))) = false := by
  simp [shape, OccurrenceGuard.isUnguarded, summary, valueRecipe, KeyedGuards.termGuard]

/-- A plain pay passes the size guard but fails the original term-growth check. -/
theorem paid_occurrence (token : Nat) (known : GroupedProbe.Table Key) (key : Key) :
    KeyedSource.guarded (valueRecipe (Recipe.pay (Root := Root) (Symbol := Symbol) (.occurrence key))) known = true ∧
      OccurrenceGuard.isUnguarded token
        (shape token known (Recipe.pay (Root := Root) (Symbol := Symbol) (.occurrence key))) = true := by
  simp [shape, OccurrenceGuard.isUnguarded, summary, valueRecipe, KeyedSource.guarded]

/-- Raw choice wrappers do not clear the source's termless occurrence flag. -/
theorem singleton_occurrence (token : Nat) (known : GroupedProbe.Table Key) (key : Key) :
    termGuard (Recipe.choice (Root := Root) (Symbol := Symbol) 1 (fun _ => .occurrence key)) = false ∧
      OccurrenceGuard.isUnguarded token
        (shape token known (Recipe.choice (Root := Root) (Symbol := Symbol) 1 (fun _ => .occurrence key))) = true := by
  simp [termGuard, shape, alternatives, OccurrenceGuard.isUnguarded, summary]

end MicroCFTA.KeyedNaryGuards
