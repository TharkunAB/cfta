import MicroCFTA.SourceSizedConjunctionClosure
import MicroCFTA.SourceSizedConjunctionClassified

/-!
# Original-state support of reached conjunction keys

Each reached key is a list without duplicates, drawn from the original
finite map keys. Generated children derive both properties from the actual
intersection tuples and set readback. The literal worklist preserves the
properties for stored and pending keys.

The original-table adapters derive classified closure and root membership
from successful current structural validation and complete classification.
Each key's length is then bounded by the original map's key count. This is
a value bound. It does not bound native tuple generation or execution cost.
-/
namespace MicroCFTA.SourceSizedConjunctionSupport
open SourceSizedDecided SourceSizedConjunctionWorklist

variable {State Symbol Formula : Type}

/-- A conjunction key has no duplicates and uses only the supplied finite inventory. -/
structure KeyWithin (inventory key : List State) : Prop where
  distinct : key.Nodup
  supported : ∀ state ∈ key, state ∈ inventory

/-- A key without duplicates cannot exceed the length of its supporting inventory. -/
theorem KeyWithin.length_le (inventory key : List State) (within : KeyWithin inventory key) :
    key.length ≤ inventory.length :=
  within.distinct.length_le_of_subset (by intro state member; exact within.supported state member)

/-- The initial singleton key derives its distinctness and finite support. -/
theorem singleton_within (inventory : List State) (root : State) (present : root ∈ inventory) :
    KeyWithin inventory [root] := by
  constructor
  · simp
  · intro state member
    have same : state = root := List.mem_singleton.mp member
    subst state
    exact present

/-- Actual same-token intersection rows emit keys without duplicates and with original support. -/
theorem generated_key [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key)
    (child : List State) (childIn : child ∈ row.children) :
    KeyWithin (SourceDenseRows.keys classified) child := by
  obtain ⟨first, others, tupleIn, rfl⟩ :=
    (SourceSizedConjunctionRows.mem_rows (SourceSizedFiniteKeys.lookup classified) key row).mp member
  obtain ⟨group, _, _, _, same⟩ := SourceSizedConjunctionPositions.child_origin
    (first :: others) first.children.length child childIn
  constructor
  · rw [same]
    exact SourceSizedConjunctionGroupKeys.groupKey_nodup _ _
  · apply SourceSizedConjunctionRows.intersection_supported classified closed first others ?_ child childIn
    intro selected selectedIn
    obtain ⟨owner, _, stored⟩ := SourceSizedConjunctionTuples.row_origin
      (SourceSizedFiniteKeys.lookup classified) key _ tupleIn selected selectedIn
    exact ⟨owner, selected, stored, rfl⟩

/-- The source cap prefix retains the same finite-key facts as the full row enumeration. -/
theorem capped_key [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ cappedRows limit classified key) (child : List State) (childIn : child ∈ row.children) :
    KeyWithin (SourceDenseRows.keys classified) child :=
  generated_key classified closed key row (List.mem_of_mem_take member) child childIn

/-- Stored and pending conjunction keys retain distinctness and finite support. -/
structure Invariant (inventory : List State) (table : Stored State Symbol)
    (pending : List (List State)) : Prop where
  stored : ∀ key ∈ table.map Prod.fst, KeyWithin inventory key
  queued : ∀ key ∈ pending, KeyWithin inventory key

/-- The actual empty-map and singleton-root initialization derives the key invariant. -/
theorem empty_invariant (inventory : List State) (root : State) (present : root ∈ inventory) :
    Invariant inventory ([] : Stored State Symbol) [[root]] := by
  constructor
  · intro key member; cases member
  · intro key member
    have same : key = [root] := List.mem_singleton.mp member
    subst key
    exact singleton_within inventory root present

private theorem insert_invariant (inventory key : List State) (table : Stored State Symbol)
    (pending : List (List State)) (rows : List (Row (List State) Symbol (List (List Nat))))
    (invariant : Invariant inventory table (key :: pending))
    (generated : ∀ row ∈ rows, ∀ child ∈ row.children, KeyWithin inventory child) :
    Invariant inventory ((key, rows) :: table) ((rows.flatMap fun row => row.children) ++ pending) := by
  constructor
  · intro owner ownerIn
    change owner ∈ key :: table.map Prod.fst at ownerIn
    rcases List.mem_cons.mp ownerIn with rfl | previous
    · exact invariant.queued owner (by simp)
    · exact invariant.stored owner previous
  · intro owner ownerIn
    rcases List.mem_append.mp ownerIn with scheduled | previous
    · obtain ⟨row, rowIn, childIn⟩ := List.mem_flatMap.mp scheduled
      exact generated row rowIn owner childIn
    · exact invariant.queued owner (List.mem_cons_of_mem _ previous)

/-- Every actual visited or inserted step preserves original-state support and distinctness. -/
theorem step_invariant [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (table nextTable : Stored State Symbol) (pending nextPending : List (List State))
    (invariant : Invariant (SourceDenseRows.keys classified) table pending)
    (checked : step limit classified table pending = .next nextTable nextPending) :
    Invariant (SourceDenseRows.keys classified) nextTable nextPending := by
  cases pending with
  | nil => cases checked
  | cons key pending =>
      simp only [step] at checked
      split at checked
      · rcases Action.next.inj checked with ⟨rfl, rfl⟩
        constructor
        · exact invariant.stored
        · intro owner present
          exact invariant.queued owner (List.mem_cons_of_mem _ present)
      · split at checked
        · cases checked
        · split at checked
          · cases checked
          · rcases Action.next.inj checked with ⟨rfl, rfl⟩
            apply insert_invariant _ key table pending (cappedRows limit classified key) invariant
            exact capped_key limit classified closed key

private def ReadyInvariant (inventory : List State) : Outcome State Symbol → Prop
  | .ready table => Invariant inventory table []
  | _ => True

private theorem evaluation_invariant [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (table : Stored State Symbol) (pending : List (List State)) (calls : Nat) (result : Outcome State Symbol)
    (execution : Evaluation limit classified table pending calls result) :
    Invariant (SourceDenseRows.keys classified) table pending →
      ReadyInvariant (SourceDenseRows.keys classified) result := by
  induction execution with
  | ready checked =>
      intro invariant
      obtain ⟨_, same⟩ := SourceSizedConjunctionClosure.step_ready limit classified _ _ _ checked
      rw [same]
      change Invariant (SourceDenseRows.keys classified) _ []
      constructor
      · exact invariant.stored
      · intro key member; cases member
  | limitExceeded _ => intro _; trivial
  | next checked _ ih =>
      intro invariant
      exact ih (step_invariant limit classified closed _ _ _ _ invariant checked)

/-- Successful concrete source traces retain the invariant for every returned map key. -/
theorem evaluation_ready [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    {table : Stored State Symbol} {pending : List (List State)} {calls : Nat}
    {result : Outcome State Symbol} {returned : Stored State Symbol}
    (execution : Evaluation limit classified table pending calls result)
    (invariant : Invariant (SourceDenseRows.keys classified) table pending)
    (success : result = .ready returned) : Invariant (SourceDenseRows.keys classified) returned [] := by
  have retained := evaluation_invariant limit classified closed table pending calls result execution invariant
  rw [success] at retained
  exact retained

/-- Public exploration derives distinct supported keys from classified closure and a declared root. -/
theorem explore_invariant [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (root : State) (present : root ∈ SourceDenseRows.keys classified) (returned : Stored State Symbol)
    (success : explore limit classified root = .ready returned) :
    Invariant (SourceDenseRows.keys classified) returned [] := by
  obtain ⟨_, _, execution⟩ := explore_evaluates limit classified root
  exact evaluation_ready limit classified closed execution (empty_invariant _ root present) success

/-- Source-sized preparation needs no supplied arity, key-length, or recursion bound. -/
theorem prepare_invariant [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (root : State) (present : root ∈ SourceDenseRows.keys classified) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) :
    Invariant (SourceDenseRows.keys classified) returned [] :=
  explore_invariant 1024 classified closed root present returned success

/-- Every returned conjunction key is a distinct list drawn from the finite input inventory. -/
theorem prepare_support [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (root : State) (present : root ∈ SourceDenseRows.keys classified) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) :
    ∀ key ∈ returned.map Prod.fst, KeyWithin (SourceDenseRows.keys classified) key :=
  (prepare_invariant classified closed root present returned success).stored

/-- Every returned key's length is bounded by the actual classified map-key count. -/
theorem prepare_length [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (root : State) (present : root ∈ SourceDenseRows.keys classified) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) :
    ∀ key ∈ returned.map Prod.fst, key.length ≤ (SourceDenseRows.keys classified).length := by
  intro key keyIn
  exact KeyWithin.length_le _ _ (prepare_support classified closed root present returned success key keyIn)

/-- All returned transition children satisfy the same distinctness and inventory properties. -/
theorem prepare_children [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (closed : SourceSizedFiniteKeys.Closed classified)
    (root : State) (present : root ∈ SourceDenseRows.keys classified) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) :
    ∀ entry ∈ returned, ∀ row ∈ entry.2, ∀ child ∈ row.children,
      KeyWithin (SourceDenseRows.keys classified) child := by
  intro entry entryIn row rowIn child childIn
  exact prepare_support classified closed root present returned success child
    ((SourceSizedConjunctionClosure.prepare_complete classified root returned success).childClosed
      entry entryIn row rowIn child childIn)

/-- Current original-table validation and actual classification derive both internal input facts. -/
theorem validated_classified [DecidableEq State] [Ord State]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) :
    SourceSizedFiniteKeys.Closed classified ∧ root ∈ SourceDenseRows.keys classified := by
  constructor
  · exact SourceSizedConjunctionClassified.classifyTable_closed original classified classification
      (SourceSizedStructuralKeys.validated_closed original root validated)
  · rw [SourceSizedConjunctionClassified.keys_eq original classified classification]
    exact SourceSizedStructuralKeys.validated_root original root validated

/-- Actual validation, classification, and preparation derive support in the original finite map. -/
theorem validated_prepare_support [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    ∀ key ∈ returned.map Prod.fst, KeyWithin (SourceDenseRows.keys original) key := by
  obtain ⟨closed, present⟩ := validated_classified original root validated classified classification
  have supported := prepare_support classified closed root present returned success
  rw [SourceSizedConjunctionClassified.keys_eq original classified classification] at supported
  exact supported

/-- Reached key lengths follow from source successes, with no caller resource-bound premise. -/
theorem validated_prepare_length [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    ∀ key ∈ returned.map Prod.fst, key.length ≤ (SourceDenseRows.keys original).length := by
  intro key keyIn
  exact KeyWithin.length_le _ _
    (validated_prepare_support original root validated classified classification returned success key keyIn)

/-- Canonical Map.keys readback preserves the derived original-state and key-length facts. -/
theorem validated_prepare_keys [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    ∀ key ∈ SourceDenseRows.keys returned,
      KeyWithin (SourceDenseRows.keys original) key ∧ key.length ≤ (SourceDenseRows.keys original).length := by
  intro key keyIn
  have within := validated_prepare_support original root validated classified classification returned success key
    ((SourceDenseRows.mem_keys returned key).mp keyIn)
  exact ⟨within, KeyWithin.length_le _ _ within⟩

end MicroCFTA.SourceSizedConjunctionSupport
