import MicroCFTA.SourceSizedConjunctionSupport

/-!
# Original-input bounds on uncapped conjunction tuples

Let R be the maximum of one and the total original row count. Let N be
the number of original map keys. Each reached key has at most N states.
Every original or classified lookup has at most R rows. The complete raw
tuple and intersection-row lists therefore have at most R^N entries.

The accounting trace sums full raw-tuple list lengths at checked pending
heads. It also charges visited and failing heads. This conservative sum
is bounded by the explorer's checking rounds times R^N. These are list
cardinality and component work-count bounds. They do not bound filtering,
native comparisons, allocation, or total execution cost.

The maximum original row arity M bounds the number of checking rounds by
cap * (cap * M) + 2. Thus the total tuple charge also has an expression
that uses only original-input row count, key count, and arity.
-/
namespace MicroCFTA.SourceSizedConjunctionTupleBound
open Language SourceSizedDecided SourceSizedConjunctionWorklist
open SourceSizedConjunctionSupport (KeyWithin Invariant)

variable {State Symbol Payload Formula : Type}

/-- Count every original alternative, including repeated rows and repeated owner entries. -/
def totalRows (table : SourceSizedFiniteKeys.Table State Symbol Payload) : Nat :=
  (table.flatMap fun entry => entry.2).length

/-- Keep the product base positive, including when the original table has no rows. -/
def base (table : SourceSizedFiniteKeys.Table State Symbol Payload) : Nat := max 1 (totalRows table)

/-- The original-input product base is always positive. -/
theorem base_pos (table : SourceSizedFiniteKeys.Table State Symbol Payload) : 0 < base table := by
  have positive := Nat.le_max_left 1 (totalRows table)
  unfold base
  omega

/-- Every merged owner lookup contains at most the total original number of rows. -/
theorem lookup_length_le [DecidableEq State]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (owner : State) :
    (SourceSizedFiniteKeys.lookup table owner).length ≤ totalRows table := by
  induction table with
  | nil => simp [SourceSizedFiniteKeys.lookup, totalRows]
  | cons entry rest ih =>
      simp only [SourceSizedFiniteKeys.lookup, totalRows, List.flatMap_cons, List.length_append] at ih ⊢
      split <;> (try simp only [List.length_nil]) <;> omega

/-- Actual classification keeps the owner lookup length, so its bound uses original rows. -/
theorem classified_lookup_bound [DecidableEq State]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) (owner : State) :
    (SourceSizedFiniteKeys.lookup classified owner).length ≤ base original := by
  have same := congrArg List.length
    (SourceSizedConjunctionClassified.lookup_shapes original classified classification owner)
  simp only [List.length_map] at same
  calc
    _ = (SourceSizedFiniteKeys.lookup original owner).length := same
    _ ≤ totalRows original := lookup_length_le original owner
    _ ≤ base original := Nat.le_max_right _ _

private theorem flatMap_length_bound {A B : Type} (values : List A) (choose : A → List B) (bound : Nat)
    (bounded : ∀ value ∈ values, (choose value).length ≤ bound) :
    (values.flatMap choose).length ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons first rest ih =>
      have head := bounded first (by simp)
      have tail := ih (fun value member => bounded value (List.mem_cons_of_mem _ member))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The literal list product has at most one per-owner bound for each position. -/
theorem products_length_bound {A B : Type} (choices : A → List B) (owners : List A) (width : Nat)
    (bounded : ∀ owner ∈ owners, (choices owner).length ≤ width) :
    (products choices owners).length ≤ width ^ owners.length := by
  induction owners with
  | nil => simp [products]
  | cons owner owners ih =>
      have tail := ih (fun other member => bounded other (List.mem_cons_of_mem _ member))
      have head := bounded owner (by simp)
      calc
        (products choices (owner :: owners)).length
            ≤ (choices owner).length * width ^ owners.length :=
          flatMap_length_bound _ _ _ (fun _ _ => by simpa only [List.length_map] using tail)
        _ ≤ width * width ^ owners.length := Nat.mul_le_mul_right _ head
        _ = width ^ (owner :: owners).length := by
          simp only [List.length_cons, Nat.pow_succ, Nat.mul_comm]

/-- Full first-row and filtered-tail enumeration retains its uncapped product bound. -/
theorem tuples_length_bound [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat)))) (width : Nat)
    (bounded : ∀ owner, (lookup owner).length ≤ width) (key : List State) :
    (SourceSizedConjunctionTuples.tuples lookup key).length ≤ width ^ key.length := by
  cases key with
  | nil => simp [SourceSizedConjunctionTuples.tuples]
  | cons owner owners =>
      have each : ∀ first ∈ lookup owner,
          ((products (fun next => (lookup next).filter (SourceSizedConjunctionTuples.sameToken first)) owners).map
            (first :: ·)).length ≤ width ^ owners.length := by
        intro first _
        rw [List.length_map]
        apply products_length_bound
        intro next _
        exact Nat.le_trans (List.length_filter_le _ _) (bounded next)
      calc
        (SourceSizedConjunctionTuples.tuples lookup (owner :: owners)).length
            ≤ (lookup owner).length * width ^ owners.length := flatMap_length_bound _ _ _ each
        _ ≤ width * width ^ owners.length := Nat.mul_le_mul_right _ (bounded owner)
        _ = width ^ (owner :: owners).length := by
          simp only [List.length_cons, Nat.pow_succ, Nat.mul_comm]

/-- Transition intersection maps each raw tuple to exactly one raw output row. -/
theorem rows_length_eq_tuples [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (lookup : State → List (Row State Symbol (List (List Nat)))) (key : List State) :
    (SourceSizedConjunctionRows.rows lookup key).length = (SourceSizedConjunctionTuples.tuples lookup key).length := by
  cases key with
  | nil => rfl
  | cons owner owners =>
      simp only [SourceSizedConjunctionRows.rows, SourceSizedConjunctionTuples.tuples,
        List.length_flatMap, List.length_map]

/-- A computed bound from the original total row count and original finite key count. -/
def rawBound [DecidableEq State] [Ord State] (original : SourceSizedFiniteKeys.Table State Symbol Payload) : Nat :=
  base original ^ (SourceDenseRows.keys original).length

/-- Distinct original-state keys derive a bound on both complete uncapped lists. -/
theorem key_bound [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (key : List State) (within : KeyWithin (SourceDenseRows.keys original) key) :
    (SourceSizedConjunctionTuples.tuples (SourceSizedFiniteKeys.lookup classified) key).length ≤ rawBound original ∧
      (SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key).length ≤ rawBound original := by
  have tuples := tuples_length_bound (SourceSizedFiniteKeys.lookup classified) (base original)
    (classified_lookup_bound original classified classification) key
  have exponent : base original ^ key.length ≤ rawBound original :=
    Nat.pow_le_pow_right (base_pos original) (KeyWithin.length_le _ _ within)
  have bounded := Nat.le_trans tuples exponent
  refine ⟨bounded, ?_⟩
  rw [rows_length_eq_tuples]
  exact bounded

/-- Every intermediate source product suffix has the same original-input cardinality bound. -/
theorem intermediate_bound [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (key suffix : List State) (within : KeyWithin (SourceDenseRows.keys original) key) (part : suffix.Sublist key)
    (first : Row State Symbol (List (List Nat))) :
    (products (fun owner => (SourceSizedFiniteKeys.lookup classified owner).filter
      (SourceSizedConjunctionTuples.sameToken first)) suffix).length ≤ rawBound original := by
  have suffixBound : (products (fun owner => (SourceSizedFiniteKeys.lookup classified owner).filter
      (SourceSizedConjunctionTuples.sameToken first)) suffix).length ≤ base original ^ suffix.length := by
    apply products_length_bound
    intro owner _
    exact Nat.le_trans (List.length_filter_le _ _) (classified_lookup_bound original classified classification owner)
  exact Nat.le_trans suffixBound (Nat.pow_le_pow_right (base_pos original)
    (Nat.le_trans part.length_le (KeyWithin.length_le _ _ within)))

/-- All stored and pending keys in the actual invariant satisfy the full raw-list bound. -/
theorem invariant_key_bound [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (table : Stored State Symbol) (pending : List (List State))
    (invariant : Invariant (SourceDenseRows.keys classified) table pending)
    (key : List State) (present : key ∈ table.map Prod.fst ∨ key ∈ pending) :
    (SourceSizedConjunctionTuples.tuples (SourceSizedFiniteKeys.lookup classified) key).length ≤ rawBound original ∧
      (SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key).length ≤ rawBound original := by
  have within : KeyWithin (SourceDenseRows.keys classified) key := by
    rcases present with stored | queued
    · exact invariant.stored key stored
    · exact invariant.queued key queued
  rw [SourceSizedConjunctionClassified.keys_eq original classified classification] at within
  exact key_bound original classified classification key within

/-- Conservatively charge the full raw tuple list at each checked pending head. -/
def charge [DecidableEq State] [DecidableEq Symbol]
    (classified : Classified State Symbol) : List (List State) → Nat
  | [] => 0
  | key :: _ => (SourceSizedConjunctionTuples.tuples (SourceSizedFiniteKeys.lookup classified) key).length

/-- The actual source frontier bounds every per-round raw-tuple charge. -/
theorem charge_bound [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (table : Stored State Symbol) (pending : List (List State))
    (invariant : Invariant (SourceDenseRows.keys classified) table pending) :
    charge classified pending ≤ rawBound original := by
  cases pending with
  | nil => exact Nat.zero_le _
  | cons key pending =>
      exact (invariant_key_bound original classified classification table _ invariant key (.inr (by simp))).1

/-- Add raw tuple charges along the concrete source rounds, including visited and failing heads. -/
inductive TupleVolume [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) :
    Stored State Symbol → List (List State) → Nat → Outcome State Symbol → Nat → Prop where
  | ready (checked : step limit classified table pending = .ready returned) :
      TupleVolume limit classified table pending 1 (.ready returned) (charge classified pending)
  | limitExceeded (checked : step limit classified table pending = .limitExceeded) :
      TupleVolume limit classified table pending 1 .limitExceeded (charge classified pending)
  | next (checked : step limit classified table pending = .next nextTable nextPending)
      (following : TupleVolume limit classified nextTable nextPending calls result volume) :
      TupleVolume limit classified table pending (calls + 1) result (charge classified pending + volume)

/-- Accounting describes the same literal source evaluation as the worklist control. -/
theorem TupleVolume.evaluation [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table : Stored State Symbol)
    (pending : List (List State)) (calls : Nat) (result : Outcome State Symbol) (volume : Nat)
    (accounted : TupleVolume limit classified table pending calls result volume) :
    Evaluation limit classified table pending calls result := by
  induction accounted with
  | ready checked => exact .ready checked
  | limitExceeded checked => exact .limitExceeded checked
  | next checked _ ih => exact .next checked ih

/-- An actual source evaluation derives its tuple charge and the rounds-times-raw-bound inequality. -/
theorem evaluation_volume [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (closed : SourceSizedFiniteKeys.Closed classified)
    (table : Stored State Symbol) (pending : List (List State)) (calls : Nat) (result : Outcome State Symbol)
    (execution : Evaluation limit classified table pending calls result) :
    Invariant (SourceDenseRows.keys classified) table pending →
      ∃ volume, TupleVolume limit classified table pending calls result volume ∧ volume ≤ calls * rawBound original := by
  induction execution with
  | ready checked =>
      intro invariant
      refine ⟨_, .ready checked, ?_⟩
      simpa only [Nat.one_mul] using charge_bound original classified classification _ _ invariant
  | limitExceeded checked =>
      intro invariant
      refine ⟨_, .limitExceeded checked, ?_⟩
      simpa only [Nat.one_mul] using charge_bound original classified classification _ _ invariant
  | next checked _ ih =>
      intro invariant
      obtain ⟨volume, accounted, bounded⟩ := ih
        (SourceSizedConjunctionSupport.step_invariant limit classified closed _ _ _ _ invariant checked)
      refine ⟨_, .next checked accounted, ?_⟩
      have total := Nat.add_le_add (charge_bound original classified classification _ _ invariant) bounded
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using total

/-- Actual validation and classification bound complete exploration, whether it succeeds or reaches a cap. -/
theorem explore_volume [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) :
    ∃ calls volume, calls ≤ fuel limit classified + 1 ∧
      Evaluation limit classified [] [[root]] calls (explore limit classified root) ∧
      TupleVolume limit classified [] [[root]] calls (explore limit classified root) volume ∧
      volume ≤ (fuel limit classified + 1) * rawBound original := by
  obtain ⟨closed, present⟩ :=
    SourceSizedConjunctionSupport.validated_classified original root validated classified classification
  obtain ⟨calls, rounds, execution⟩ := explore_evaluates limit classified root
  obtain ⟨volume, accounted, bounded⟩ := evaluation_volume limit original classified classification closed
    [] [[root]] calls _ execution (SourceSizedConjunctionSupport.empty_invariant _ root present)
  exact ⟨calls, volume, rounds, execution, accounted, Nat.le_trans bounded (Nat.mul_le_mul_right _ rounds)⟩

/-- Source-sized preparation derives the same bound with the literal 1024 cap and no caller resource facts. -/
theorem prepare_volume [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) :
    ∃ calls volume, calls ≤ fuel 1024 classified + 1 ∧
      Evaluation 1024 classified [] [[root]] calls (prepare classified root) ∧
      TupleVolume 1024 classified [] [[root]] calls (prepare classified root) volume ∧
      volume ≤ (fuel 1024 classified + 1) * rawBound original :=
  explore_volume 1024 original root validated classified classification

/-- Every successfully returned key has both full uncapped list bounds from original source successes. -/
theorem prepare_key_bound [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    ∀ key ∈ returned.map Prod.fst,
      (SourceSizedConjunctionTuples.tuples (SourceSizedFiniteKeys.lookup classified) key).length ≤ rawBound original ∧
        (SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key).length ≤ rawBound original := by
  intro key member
  exact key_bound original classified classification key
    (SourceSizedConjunctionSupport.validated_prepare_support original root validated classified classification
      returned success key member)

/-- Compute the maximum child arity directly from all original rows. -/
def originalArity (original : SourceSizedFiniteKeys.Table State Symbol Payload) : Nat :=
  (original.flatMap fun entry => entry.2.map fun row => row.children.length).foldr max 0

private theorem member_le_maximum (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

private theorem maximum_le (values : List Nat) (bound : Nat) (bounded : ∀ value ∈ values, value ≤ bound) :
    values.foldr max 0 ≤ bound := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
      have head := bounded first (by simp)
      have tail := ih (fun value member => bounded value (List.mem_cons_of_mem _ member))
      simp only [List.foldr_cons]
      omega

/-- Original merged lookup rows cannot exceed the maximum arity computed from the original input. -/
theorem original_row_arity [DecidableEq State]
    (original : SourceSizedFiniteKeys.Table State Symbol Payload) (owner : State)
    (row : Row State Symbol Payload) (member : row ∈ SourceSizedFiniteKeys.lookup original owner) :
    row.children.length ≤ originalArity original := by
  unfold SourceSizedFiniteKeys.lookup at member
  obtain ⟨entry, entryIn, selected⟩ := List.mem_flatMap.mp member
  have stored : row ∈ entry.2 := by
    split at selected
    · exact selected
    · cases selected
  exact member_le_maximum _ _
    (List.mem_flatMap.mpr ⟨entry, entryIn, List.mem_map.mpr ⟨row, stored, rfl⟩⟩)

/-- Actual complete classification derives its arity bound from original row lookup origins. -/
theorem classified_arity_bound [DecidableEq State]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) :
    maxArity classified ≤ originalArity original := by
  unfold maxArity
  apply maximum_le
  intro arity present
  obtain ⟨entry, entryIn, mapped⟩ := List.mem_flatMap.mp present
  obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp mapped
  have stored : row ∈ SourceSizedFiniteKeys.lookup classified entry.1 :=
    List.mem_flatMap.mpr ⟨entry, entryIn, by simpa only [↓reduceIte] using rowIn⟩
  obtain ⟨originalRow, originalIn, _, _, children⟩ :=
    SourceSizedConjunctionClassified.lookup_origin original classified classification entry.1 row stored
  rw [children]
  exact original_row_arity original entry.1 originalRow originalIn

/-- Bound all source checking rounds from the original input arity and the key cap. -/
def roundBound (limit : Nat) (original : SourceSizedFiniteKeys.Table State Symbol Payload) : Nat :=
  limit * (limit * originalArity original) + 2

/-- Computed classified fuel is bounded by a literal original-input round expression. -/
theorem fuel_bound [DecidableEq State]
    (limit : Nat) (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) :
    fuel limit classified + 1 ≤ roundBound limit original := by
  have arity := Nat.mul_le_mul_left limit
    (Nat.mul_le_mul_left limit (classified_arity_bound original classified classification))
  unfold fuel roundBound
  omega

/-- The complete explorer's round and raw-tuple bounds depend only on original-input values. -/
theorem explore_original_volume [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) :
    ∃ calls volume, calls ≤ roundBound limit original ∧
      Evaluation limit classified [] [[root]] calls (explore limit classified root) ∧
      TupleVolume limit classified [] [[root]] calls (explore limit classified root) volume ∧
      volume ≤ roundBound limit original * rawBound original := by
  obtain ⟨calls, volume, rounds, execution, accounted, bounded⟩ :=
    explore_volume limit original root validated classified classification
  have fuelWithin := fuel_bound limit original classified classification
  exact ⟨calls, volume, Nat.le_trans rounds fuelWithin, execution, accounted,
    Nat.le_trans bounded (Nat.mul_le_mul_right _ fuelWithin)⟩

/-- With the literal cap, component counts use only original row count, key count, and arity. -/
theorem prepare_original_volume [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (original : SourceSizedFiniteKeys.Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State)
    (validated : SourceFTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified) :
    ∃ calls volume, calls ≤ roundBound 1024 original ∧
      Evaluation 1024 classified [] [[root]] calls (prepare classified root) ∧
      TupleVolume 1024 classified [] [[root]] calls (prepare classified root) volume ∧
      volume ≤ roundBound 1024 original * rawBound original :=
  explore_original_volume 1024 original root validated classified classification

end MicroCFTA.SourceSizedConjunctionTupleBound
