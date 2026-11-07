import MicroCFTA.SourceSizedGroupedClasses
import MicroCFTA.SourceSizedGroupedRowUnique
import MicroCFTA.SourceSizedConjunctionUnambiguity

/-!
# Distinct whole grouped size classes

Strictly smaller child requests supply distinct exact-size child classes.
The literal grouped row worker preserves distinctness. Actual alternative
disjointness then separates the row lists in the outer concatenation.

The scoped source Boolean gate and successful conjunction preparation
derive all row, sharing, and disjointness facts for the public endpoint.
No caller supplies output uniqueness or a completed class evaluator.
Native minimum tables, lazy indexes, count/select/rank execution, and total
native execution cost remain separate.
-/
namespace MicroCFTA.SourceSizedGroupedUnique
open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys
open SourceSizedGroupedClasses SourceSizedGroupedChainOrder
open SourceSizedConjunctionLanguage (graph)

variable {State Symbol Formula : Type}

/-- Valid shared rows with disjoint alternatives give distinct whole grouped classes. -/
theorem classes_nodup [DecidableEq Symbol]
    (rows : State → List (Row State Symbol (List (List Nat))))
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧
        SourceSizedConjunctionSharing.Shared row)
    (separate : ∀ state, RecursiveUnambiguous.DisjointRows (graph rows) state)
    (size : Nat) (state : State) : (classes rows size state).Nodup := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [classes_zero]; exact .nil
      | succ remaining =>
          rw [classes_succ]
          let childAt := fun child childSize =>
            if childSize ≤ remaining then classes rows childSize child else []
          let domain := fun child term => Accepts (graph rows) child term ∧ nodeSize term ≤ remaining
          have childExact : ∀ child childSize term, term ∈ childAt child childSize ↔
              domain child term ∧ nodeSize term = childSize := by
            intro child childSize term
            by_cases smaller : childSize ≤ remaining
            · simp only [childAt, smaller, ↓reduceIte]
              rw [mem_classes_iff rows facts childSize child term]
              dsimp only [domain]
              constructor
              · rintro ⟨accepted, sized⟩
                exact ⟨⟨accepted, by omega⟩, sized⟩
              · rintro ⟨⟨accepted, _⟩, sized⟩
                exact ⟨accepted, sized⟩
            · simp only [childAt, smaller, ↓reduceIte, List.not_mem_nil, false_iff]
              rintro ⟨⟨_, bounded⟩, sized⟩
              omega
          have childSized : ∀ child childSize term, term ∈ childAt child childSize → nodeSize term = childSize :=
            fun child childSize term member => ((childExact child childSize term).mp member).2
          have childUnique : ∀ child childSize, (childAt child childSize).Nodup := by
            intro child childSize
            by_cases smaller : childSize ≤ remaining
            · simp only [childAt, smaller, ↓reduceIte]
              exact ih childSize (by omega) child
            · simp [childAt, smaller]
          have sound : ∀ row ∈ rows state, ∀ term ∈ rowClass childAt row.label row.children row.constraint (remaining + 1),
              AutomatonAmbiguity.EdgeLanguage (Accepts (graph rows))
                (row.edge SourceSizedConjunctionSemantics.holds) term := by
            intro row rowIn term produced
            obtain ⟨values, same, children, guard, _⟩ :=
              (SourceSizedGroupedRowLanguage.mem_rowClass_iff childAt domain childExact
                row.label row.children row.constraint (facts state row rowIn).1
                (facts state row rowIn).2 (remaining + 1) term).mp produced
            exact ⟨values, same, children.imp (fun _ _ accepted => accepted.1), guard⟩
          change ((rows state).flatMap fun row =>
            rowClass childAt row.label row.children row.constraint (remaining + 1)).Nodup
          apply List.pairwise_flatMap.mpr
          constructor
          · intro row rowIn
            exact SourceSizedGroupedRowUnique.rowClass_nodup childAt childSized childUnique
              row.label row.children row.constraint (facts state row rowIn).1 (remaining + 1)
          · apply (List.pairwise_map.mp (separate state)).imp_of_mem
            intro first second firstIn secondIn apart left leftIn right rightIn same
            subst right
            exact apart left (sound first firstIn left leftIn) (sound second secondIn left rightIn)

/-- The evaluator with its computed request-size bound retains whole-class distinctness. -/
theorem run_nodup [DecidableEq Symbol]
    (rows : State → List (Row State Symbol (List (List Nat))))
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧
        SourceSizedConjunctionSharing.Shared row)
    (separate : ∀ state, RecursiveUnambiguous.DisjointRows (graph rows) state)
    (size : Nat) (state : State) : (run rows size state).Nodup := by
  rw [run_eq_classes]
  exact classes_nodup rows facts separate size state

/-- The actual scoped gate and preparation derive distinct classes at every output key. -/
theorem prepared_classes_nodup [DecidableEq State] [Ord State] [Ord (List State)]
    [DecidableEq Symbol] [Ord Symbol]
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (size : Nat) (key : List State) : (classes (lookup output) size key).Nodup :=
  classes_nodup (lookup output)
    (SourceSizedConjunctionSharing.preparation_facts
      (SourceSizedScopedTrimInventory.trimmedTable table root) root output success)
    (SourceSizedConjunctionUnambiguity.preparation_disjoint table root validated passed output success) size key

/-- Actual source preparation gives distinct complete evaluator results without supplied uniqueness. -/
theorem prepared_run_nodup [DecidableEq State] [Ord State] [Ord (List State)]
    [DecidableEq Symbol] [Ord Symbol]
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (size : Nat) (key : List State) : (run (lookup output) size key).Nodup := by
  rw [run_eq_classes]
  exact prepared_classes_nodup table root validated passed output success size key

/-- The complete grouped result lists each accepted term of the requested size exactly once. -/
theorem prepared_run_exact [DecidableEq State] [Ord State] [Ord (List State)]
    [DecidableEq Symbol] [Ord Symbol]
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (size : Nat) (key : List State) :
    (run (lookup output) size key).Nodup ∧
      ∀ term, term ∈ run (lookup output) size key ↔
        Accepts (graph (lookup output)) key term ∧ nodeSize term = size :=
  ⟨prepared_run_nodup table root validated passed output success size key,
    SourceSizedGroupedClasses.prepared_run_iff
      (SourceSizedScopedTrimInventory.trimmedTable table root) root output success size key⟩

end MicroCFTA.SourceSizedGroupedUnique
