import MicroCFTA.SourceEqualityNeededMap

/-!
# The signed source simultaneous-edit compiler

Leaf payloads identify source callbacks. Empty paths replace the current
subtree. A deeper insertion under an existing leaf keeps that leaf. The
source right fold determines which callback survives duplicate paths.
-/
namespace MicroCFTA.SourceEqualityEdits
open SourceEqualityNeededMap

abbrev Path := List Int

/-- Edits retain a callback at a path or signed edits below its children. -/
inductive Edits (Action : Type) where
  | editAt (action : Action)
  | editBelow (children : List (Int × Edits Action))
  deriving Repr

/-- The empty source edit map visits no child position. -/
def empty : Edits Action := .editBelow []

/-- Insert one edit with the source empty-path and ancestor-leaf branch priority. -/
def insert : Path → Action → Edits Action → Edits Action
  | [], action, _ => .editAt action
  | index :: rest, action, .editBelow children =>
      .editBelow (alter index (fun previous => insert rest action (previous.getD empty)) children)
  | _ :: _, _, leaf@(.editAt _) => leaf

/-- Compile source edit pairs in their original right-fold order. -/
def build (edits : List (Path × Action)) : Edits Action :=
  edits.foldr (fun edit prior => insert edit.1 edit.2 prior) empty

/-- Every child map has ascending unique keys and valid descendants. -/
def Valid : Edits Action → Prop
  | .editAt _ => True
  | .editBelow children => Ascending children ∧ ∀ index child, (index, child) ∈ children → Valid child
termination_by edits => sizeOf edits
decreasing_by
  have smaller := List.sizeOf_lt_of_mem ‹(index, child) ∈ children›
  simp only [Prod.mk.sizeOf_spec, Edits.editBelow.sizeOf_spec] at *
  omega

/-- Retain a property of every callback that can survive in the compiled trie. -/
def All (property : Action → Prop) : Edits Action → Prop
  | .editAt action => property action
  | .editBelow children => ∀ index child, (index, child) ∈ children → All property child
termination_by edits => sizeOf edits
decreasing_by
  have smaller := List.sizeOf_lt_of_mem ‹(index, child) ∈ children›
  simp only [Prod.mk.sizeOf_spec, Edits.editBelow.sizeOf_spec] at *
  omega

/-- No edit callback is present in the empty map. -/
theorem empty_valid : Valid (empty : Edits Action) := by simp [Valid, empty, Ascending]

/-- Actual insertion preserves signed-map validity. -/
theorem insert_valid (path : Path) (action : Action) (edits : Edits Action) (valid : Valid edits) :
    Valid (insert path action edits) := by
  induction path generalizing edits with
  | nil => simp [insert, Valid]
  | cons index rest ih =>
      cases edits with
      | editAt prior => simpa only [insert] using valid
      | editBelow children =>
          rw [Valid] at valid
          have previous : Valid ((lookup index children).getD empty) := by
            cases found : lookup index children with
            | none => exact empty_valid
            | some child => exact valid.2 index child (lookup_mem _ _ _ found)
          rw [SourceEqualityEdits.insert, Valid]
          exact ⟨alter_ascending _ _ _ valid.1,
            alter_all _ _ _ Valid valid.2 (ih _ previous) valid.1⟩

/-- The complete source compiler always produces valid finite child maps. -/
theorem build_valid (edits : List (Path × Action)) : Valid (build edits) := by
  induction edits with
  | nil => exact empty_valid
  | cons edit rest ih => exact insert_valid edit.1 edit.2 (build rest) ih

/-- Insertion needs the callback property only for the old leaves and the inserted callback. -/
theorem insert_all (property : Action → Prop) (path : Path) (action : Action) (edits : Edits Action)
    (valid : Valid edits) (prior : All property edits) (new : property action) :
    All property (insert path action edits) := by
  induction path generalizing edits with
  | nil => simpa only [insert, All] using new
  | cons index rest ih =>
      cases edits with
      | editAt old => exact prior
      | editBelow children =>
          rw [Valid] at valid
          rw [All] at prior
          have previousValid : Valid ((lookup index children).getD empty) := by
            cases found : lookup index children with
            | none => exact empty_valid
            | some child => exact valid.2 index child (lookup_mem _ _ _ found)
          have previousAll : All property ((lookup index children).getD empty) := by
            cases found : lookup index children with
            | none => simp [All, empty]
            | some child => exact prior index child (lookup_mem _ _ _ found)
          rw [SourceEqualityEdits.insert, All]
          exact alter_all _ _ _ (All property) prior (ih _ previousValid previousAll) valid.1

/-- Every retained callback derives its contract from an original edit pair. -/
theorem build_all (property : Action → Prop) (edits : List (Path × Action))
    (callbacks : ∀ path action, (path, action) ∈ edits → property action) : All property (build edits) := by
  induction edits with
  | nil => simp [build, empty, All]
  | cons edit rest ih =>
      exact insert_all property edit.1 edit.2 (build rest) (build_valid rest)
        (ih (fun path action member => callbacks path action (List.mem_cons_of_mem _ member)))
        (callbacks edit.1 edit.2 List.mem_cons_self)

/-- Every retained callback property can be weakened pointwise. -/
theorem all_mono (first second : Action → Prop) (implies : ∀ action, first action → second action)
    (edits : Edits Action) (prior : All first edits) : All second edits := by
  cases shape : edits with
  | editAt action =>
      rw [shape, All] at prior
      rw [All]
      exact implies action prior
  | editBelow entries =>
      rw [shape, All] at prior
      rw [All]
      intro index child member
      exact all_mono first second implies child (prior index child member)
termination_by sizeOf edits
decreasing_by
  rw [shape]
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Edits.editBelow.sizeOf_spec] at *
  omega

/-- A callback at the current path replaces every earlier subtree shape. -/
theorem insert_root (action : Action) (edits : Edits Action) : insert [] action edits = .editAt action := rfl

/-- A nonempty deeper insertion cannot replace an existing ancestor callback. -/
theorem insert_under_leaf (index : Int) (rest : Path) (action prior : Action) :
    insert (index :: rest) action (.editAt prior) = .editAt prior := rfl

/-- Duplicate paths retain the first callback in the original input list. -/
theorem duplicate_example : build [([0], 7), ([0], 9)] = .editBelow [(0, .editAt 7)] := rfl

/-- A prefix callback shadows its descendant in either source input order. -/
theorem prefix_examples :
    build [([0], 7), ([0, 1], 9)] = .editBelow [(0, .editAt 7)] ∧
    build [([0, 1], 9), ([0], 7)] = .editBelow [(0, .editAt 7)] := by constructor <;> rfl

/-- The root callback shadows all child edits even when it appears later in the input. -/
theorem root_example : build [([0, 1], 9), ([], 7)] = .editAt 7 := rfl

end MicroCFTA.SourceEqualityEdits
