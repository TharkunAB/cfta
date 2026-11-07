import MicroCFTA.SourceSizedGroupedRowLanguage
import MicroCFTA.SourceSizedConjunctionSharing
import MicroCFTA.GraphRewrite

/-!
# Finite exact-size classes of grouped source rows

The class recurrence retains source row and group-product order. It makes
recursive calls only at smaller sizes. A structural evaluator reaches the
same result with a bound computed from the requested size.

Actual conjunction preparation supplies all position and sharing facts.
No caller supplies a layout, completed class worker, or evaluation fuel.
Native minimum tables, lazy indexes, count/select/rank execution, and class
uniqueness remain separate.
-/
namespace MicroCFTA.SourceSizedGroupedClasses
open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys
open SourceSizedConjunctionLanguage (graph)

variable {State Symbol Formula : Type}

/-- Retain every source row occurrence and its grouped product order. -/
def classOf (classAt : State → Nat → List (Term Symbol))
    (rows : List (Row State Symbol (List (List Nat)))) (size : Nat) : List (Term Symbol) :=
  rows.flatMap fun row => SourceSizedGroupedChainOrder.rowClass
    classAt row.label row.children row.constraint size

/-- Compute a size class by strictly decreasing requested node count. -/
def classes (rows : State → List (Row State Symbol (List (List Nat))))
    (size : Nat) (state : State) : List (Term Symbol) :=
  match size with
  | 0 => []
  | remaining + 1 => classOf
      (fun child childSize => if _smaller : childSize ≤ remaining then classes rows childSize child else [])
      (rows state) (remaining + 1)
termination_by size

/-- The structural evaluator retains the same bounded child calls and row order. -/
def evaluate : Nat → (State → List (Row State Symbol (List (List Nat)))) →
    Nat → State → List (Term Symbol)
  | 0, _, _, _ => []
  | _ + 1, _, 0, _ => []
  | fuel + 1, rows, remaining + 1, state => classOf
      (fun child childSize => if childSize ≤ remaining then evaluate fuel rows childSize child else [])
      (rows state) (remaining + 1)

/-- Supply the structural evaluator's bound from the request alone. -/
def run (rows : State → List (Row State Symbol (List (List Nat))))
    (size : Nat) (state : State) : List (Term Symbol) := evaluate (size + 1) rows size state

/-- A zero-size request has no terms. -/
theorem classes_zero (rows : State → List (Row State Symbol (List (List Nat)))) (state : State) :
    classes rows 0 state = [] := by rw [classes]

/-- A positive request unfolds the concrete grouped class recurrence. -/
theorem classes_succ (rows : State → List (Row State Symbol (List (List Nat))))
    (remaining : Nat) (state : State) :
    classes rows (remaining + 1) state = classOf
      (fun child childSize => if childSize ≤ remaining then classes rows childSize child else [])
      (rows state) (remaining + 1) := by
  rw [classes]
  apply congrArg (fun childAt => classOf childAt (rows state) (remaining + 1))
  funext child childSize
  by_cases smaller : childSize ≤ remaining <;> simp [smaller]

private theorem child_size_le (terms : List (Term Symbol)) (child : Term Symbol)
    (member : child ∈ terms) : nodeSize child ≤ forestSize terms := by
  induction terms with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst child
        exact Nat.le_add_right _ _
      · have before := ih later
        change nodeSize child ≤ nodeSize first + forestSize rest
        omega

/-- Valid shared rows generate exactly their accepted terms of the requested node count. -/
theorem mem_classes_iff [DecidableEq Symbol]
    (rows : State → List (Row State Symbol (List (List Nat))))
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧
        SourceSizedConjunctionSharing.Shared row)
    (size : Nat) (state : State) (term : Term Symbol) :
    term ∈ classes rows size state ↔ Accepts (graph rows) state term ∧ nodeSize term = size := by
  induction size using Nat.strongRecOn generalizing state term with
  | ind size ih =>
      cases size with
      | zero =>
          rw [classes_zero]
          constructor
          · intro impossible; cases impossible
          · rintro ⟨_, sized⟩
            have positive := nodeSize_pos term
            omega
      | succ remaining =>
          rw [classes_succ]
          let domain := fun child value => Accepts (graph rows) child value ∧ nodeSize value ≤ remaining
          let childAt := fun child childSize =>
            if childSize ≤ remaining then classes rows childSize child else []
          have childExact : ∀ child childSize value, value ∈ childAt child childSize ↔
              domain child value ∧ nodeSize value = childSize := by
            intro child childSize value
            by_cases smaller : childSize ≤ remaining
            · simp only [childAt, smaller, ↓reduceIte]
              rw [ih childSize (by omega) child value]
              dsimp [domain]
              constructor
              · rintro ⟨accepted, sized⟩
                exact ⟨⟨accepted, by omega⟩, sized⟩
              · rintro ⟨⟨accepted, _⟩, sized⟩
                exact ⟨accepted, sized⟩
            · simp only [childAt, smaller, ↓reduceIte, List.not_mem_nil, false_iff]
              rintro ⟨⟨_, bound⟩, same⟩
              omega
          constructor
          · intro member
            obtain ⟨row, rowIn, produced⟩ := List.mem_flatMap.mp member
            obtain ⟨values, same, children, guard, sized⟩ :=
              (SourceSizedGroupedRowLanguage.mem_rowClass_iff childAt domain childExact
                row.label row.children row.constraint (facts state row rowIn).1
                (facts state row rowIn).2 (remaining + 1) term).mp produced
            subst term
            have acceptedChildren : All₂ (Accepts (graph rows)) row.children values :=
              children.imp (fun _ _ accepted => accepted.1)
            exact ⟨.node (row.edge SourceSizedConjunctionSemantics.holds) values
              (List.mem_map.mpr ⟨row, rowIn, rfl⟩) acceptedChildren guard, sized⟩
          · rintro ⟨accepted, sized⟩
            cases accepted with
            | node edge values member children guard =>
                obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp member
                have boundedChildren : All₂ domain row.children values := by
                  apply GraphRewrite.all₂_local_imp _ _ children
                  intro child value valueIn accepts
                  refine ⟨accepts, ?_⟩
                  have below := child_size_le values value valueIn
                  simp only [nodeSize] at sized
                  change forestSize values + 1 = remaining + 1 at sized
                  omega
                apply List.mem_flatMap.mpr
                refine ⟨row, rowIn, ?_⟩
                exact (SourceSizedGroupedRowLanguage.mem_rowClass_iff childAt domain childExact
                  row.label row.children row.constraint (facts state row rowIn).1
                  (facts state row rowIn).2 (remaining + 1) _).mpr
                    ⟨values, rfl, boundedChildren, guard, sized⟩

/-- A sufficient structural bound gives the complete class without truncation. -/
theorem evaluate_eq_classes (rows : State → List (Row State Symbol (List (List Nat))))
    (size : Nat) (state : State) (fuel : Nat) (enough : size + 1 ≤ fuel) :
    evaluate fuel rows size state = classes rows size state := by
  induction size using Nat.strongRecOn generalizing state fuel with
  | ind size ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases size with
          | zero => rw [evaluate, classes_zero]
          | succ remaining =>
              rw [evaluate, classes_succ]
              apply congrArg (fun childAt => classOf childAt (rows state) (remaining + 1))
              funext child childSize
              split
              · rename_i smaller
                exact ih childSize (by omega) child fuel (by omega)
              · rfl

/-- The computed request-size bound evaluates every class completely. -/
theorem run_eq_classes (rows : State → List (Row State Symbol (List (List Nat))))
    (size : Nat) (state : State) : run rows size state = classes rows size state :=
  evaluate_eq_classes rows size state (size + 1) (Nat.le_refl _)

/-- The computed evaluator has the exact grouped graph language and node count. -/
theorem mem_run_iff [DecidableEq Symbol]
    (rows : State → List (Row State Symbol (List (List Nat))))
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧
        SourceSizedConjunctionSharing.Shared row)
    (size : Nat) (state : State) (term : Term Symbol) :
    term ∈ run rows size state ↔ Accepts (graph rows) state term ∧ nodeSize term = size := by
  rw [run_eq_classes]
  exact mem_classes_iff rows facts size state term

/-- Actual final conjunction preparation derives every prerequisite for exact-size classes. -/
theorem prepared_run_iff [DecidableEq State] [Ord State] [Ord (List State)]
    [DecidableEq Symbol] [Ord Symbol]
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size : Nat) (key : List State) (term : Term Symbol) :
    term ∈ run (lookup output) size key ↔
      Accepts (graph (lookup output)) key term ∧ nodeSize term = size :=
  mem_run_iff (lookup output)
    (SourceSizedConjunctionSharing.preparation_facts original root output success) size key term

open SourceGuards SourceObservations SourceSymbolicIndex

/-- The complete prepared root generates exactly the original guarded terms at each size.
The remaining input-construction task must derive the internal activity condition. -/
theorem prepared_root_language [DecidableEq State] [Ord State] [Ord (List State)]
    [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (active : ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State (Label Formula))
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size : Nat) (term : Term (Label Formula)) :
    term ∈ run (lookup output) size [root] ↔
      Accepts (SourceSizedConjunctionGuarded.originalGraph formulas solver original) root term ∧
        nodeSize term = size :=
  (prepared_run_iff original root output success size [root] term).trans
    (and_congr (SourceSizedConjunctionPreparation.root_language
      formulas solver original active root output success term) Iff.rfl)

end MicroCFTA.SourceSizedGroupedClasses
