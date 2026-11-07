import MicroCFTA.SourceSizedEqualChildren
import MicroCFTA.SourceSizedFiniteKeys

/-!
# Complete source-table equal-child classification

The two traversals classify every stored row, including unreachable rows.
They preserve the complete key sequence and alternative order. A failed row
rejects the table. No semantic invariant is an argument to the computation.
-/
namespace MicroCFTA.SourceSizedConjunctionClassified
open Language SourceSizedDecided SourceSymbolicIndex SourceSizedFiniteKeys
open SourceSizedEqualChildren (classify)

variable {State Symbol Formula : Type}

/-- Traverse the source table entries and every row in each entry. -/
noncomputable def classifyTable (table : Table State Symbol (Constraint Formula)) :
    Option (Table State Symbol (List (List Nat))) :=
  table.mapM fun entry =>
    (entry.2.mapM classify).map fun rows => (entry.1, rows)

private theorem mapM_related {α β : Type} (f : α → Option β)
    (before : List α) (after : List β) (success : before.mapM f = some after) :
    All₂ (fun original output => f original = some output) before after := by
  induction before generalizing after with
  | nil =>
      have empty : after = [] := by simpa using success.symm
      subst after
      exact .nil
  | cons first rest ih =>
      rw [List.mapM_cons] at success
      simp only [Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at success
      obtain ⟨head, actual, tail, traversed, rfl⟩ := success
      exact .cons actual (ih tail traversed)

private theorem mapM_member {α β : Type} (f : α → Option β)
    (before : List α) (after : List β) (success : before.mapM f = some after) :
    ∀ original ∈ before, ∃ output ∈ after, f original = some output := by
  have related := mapM_related f before after success
  clear success
  induction related with
  | nil => simp
  | @cons first result rest produced actual _ ih =>
      intro original originalIn
      rcases List.mem_cons.mp originalIn with rfl | present
      · exact ⟨result, by simp, actual⟩
      · obtain ⟨output, outputIn, done⟩ := ih original present
        exact ⟨output, by simp [outputIn], done⟩

/-- Each output entry keeps its key and the complete successful row traversal. -/
theorem classifyTable_shape (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output) :
    All₂ (fun original classified => classified.1 = original.1 ∧
      original.2.mapM classify = some classified.2) table output := by
  have related := mapM_related
    (fun entry : State × List (Row State Symbol (Constraint Formula)) =>
      (entry.2.mapM classify).map fun rows => (entry.1, rows)) table output success
  apply All₂.imp ?_ related
  intro original classified actual
  obtain ⟨rows, checked, same⟩ := Option.map_eq_some_iff.mp actual
  cases same
  exact ⟨rfl, checked⟩

/-- Source key order and repeated key occurrences are unchanged. -/
theorem key_sequence (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output) :
    output.map Prod.fst = table.map Prod.fst := by
  have related := classifyTable_shape table output success
  clear success
  induction related with
  | nil => rfl
  | cons frame _ ih => simp only [List.map_cons, frame.1, ih]

section Lookup
variable [DecidableEq State]

/-- Classification commutes with merged lookup in exact alternative order. -/
theorem lookup_classifies (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output)
    (owner : State) :
    (lookup table owner).mapM classify = some (lookup output owner) := by
  have related := classifyTable_shape table output success
  clear success
  induction related with
  | nil => rfl
  | @cons original classified originals produced frame _ ih =>
      simp only [lookup] at ih
      simp only [lookup, List.flatMap_cons]
      rw [frame.1]
      by_cases present : original.1 = owner
      · simp only [present, ↓reduceIte]
        rw [List.mapM_append, frame.2, ih]
        rfl
      · simpa only [present, ↓reduceIte, List.nil_append] using ih

/-- Every classified lookup row has an exact original row and classification receipt. -/
theorem lookup_origin (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output)
    (owner : State) (classified : Row State Symbol (List (List Nat)))
    (present : classified ∈ lookup output owner) :
    ∃ original ∈ lookup table owner, classify original = some classified ∧
      classified.label = original.label ∧ classified.children = original.children :=
  SourceSizedEqualChildren.classifyRows_origin (lookup table owner) (lookup output owner)
    (lookup_classifies table output success owner) classified present

/-- Every original lookup row receives a classified row; no row is skipped. -/
theorem lookup_source (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output)
    (owner : State) (original : Row State Symbol (Constraint Formula))
    (present : original ∈ lookup table owner) :
    ∃ classified ∈ lookup output owner, classify original = some classified :=
  mapM_member classify (lookup table owner) (lookup output owner)
    (lookup_classifies table output success owner) original present

/-- Lookup retains the complete symbol and child-list sequence. -/
theorem lookup_shapes (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output)
    (owner : State) :
    (lookup output owner).map (fun row => (row.label, row.children)) =
      (lookup table owner).map (fun row => (row.label, row.children)) := by
  have related := mapM_related classify (lookup table owner) (lookup output owner)
    (lookup_classifies table output success owner)
  have preserve {before : List (Row State Symbol (Constraint Formula))}
      {after : List (Row State Symbol (List (List Nat)))}
      (relation : All₂ (fun original classified => classify original = some classified) before after) :
      after.map (fun row => (row.label, row.children)) =
        before.map (fun row => (row.label, row.children)) := by
    induction relation with
    | nil => rfl
    | cons actual _ ih =>
        have frame := SourceSizedEqualChildren.classify_shape _ _ actual
        simp only [List.map_cons, frame.1, frame.2.1, ih]
  exact preserve related

/-- Each emitted equality position is bounded by its own row's unchanged arity. -/
theorem lookup_bounded (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output)
    (owner : State) (classified : Row State Symbol (List (List Nat)))
    (present : classified ∈ lookup output owner) :
    CompactGroups.ValidClasses classified.children.length classified.constraint := by
  obtain ⟨original, _, actual, _, children⟩ := lookup_origin table output success owner classified present
  have frame := SourceSizedEqualChildren.classify_shape original classified actual
  have valid := SourceSizedEqualChildren.equalChildren_bounded
    original classified.constraint frame.2.2
  simpa only [children] using valid

/-- The finite map-key inventory remains exactly the original inventory. -/
theorem keys_eq [Ord State] (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output) :
    SourceDenseRows.keys output = SourceDenseRows.keys table := by
  unfold SourceDenseRows.keys
  rw [key_sequence table output success]

/-- Original structural closure transfers to the actual classified table. -/
theorem classifyTable_closed [Ord State] (table : Table State Symbol (Constraint Formula))
    (output : Table State Symbol (List (List Nat))) (success : classifyTable table = some output)
    (closed : SourceSizedFiniteKeys.Closed table) : SourceSizedFiniteKeys.Closed output := by
  intro owner classified present child childIn
  obtain ⟨original, originalIn, _, _, children⟩ :=
    lookup_origin table output success owner classified present
  rw [keys_eq table output success]
  apply closed owner original originalIn child
  rwa [children] at childIn

/-- An unsupported original row rejects the entire source traversal. -/
theorem reject_unsupported (table : Table State Symbol (Constraint Formula))
    (owner : State) (original : Row State Symbol (Constraint Formula))
    (present : original ∈ lookup table owner) (unsupported : classify original = none) :
    classifyTable table = none := by
  cases actual : classifyTable table with
  | none => rfl
  | some output =>
      obtain ⟨classified, _, checked⟩ := lookup_source table output actual owner original present
      rw [unsupported] at checked
      cases checked

/-- Residual syntax rejects a stored row even when its owner is unreachable. -/
theorem reject_residual (table : Table State Symbol (Constraint Formula))
    (owner : State) (original : Row State Symbol (Constraint Formula))
    (present : original ∈ lookup table owner)
    (residual : (SourceCompactGuards.positive original.constraint.guard).isSome = false) :
    classifyTable table = none := by
  apply reject_unsupported table owner original present
  simp [SourceSizedEqualChildren.classify,
    SourceSizedEqualChildren.equalChildren_residual original residual]

end Lookup
end MicroCFTA.SourceSizedConjunctionClassified
