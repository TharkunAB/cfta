import MicroCFTA.RecursiveJoinBodyFields

/-!
# Complete mutual recursive inverse with grouped joins

Each body supplies constructor-derived local callback laws. A source key
boundary decreases the requested term height. Height induction then proves
the inverse of the independently compiled term record for every key.
-/
namespace MicroCFTA.RecursiveJoinInverse
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveFieldBounds
open RecursiveJoinRecordBridge RecursiveJoinFields
open RecursiveJoinBodyFields

/-- Remove local callback certificates before constructing the grouped records. -/
def lower (program : Key → CheckedBody Key Root Symbol Root) : Key → RecursiveJoinComposition.Body Key Root Symbol Root :=
  fun key => (program key).body

/-- All value bodies pass the source minimum-based size guard. -/
def Guarded (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → CheckedBody Key Root Symbol Root) : Prop :=
  ∀ key, KeyedSource.guarded (RecursiveJoinFamily.valueProgram (lower program) key)
    (KeyedSource.minima keys complete (RecursiveJoinFamily.valueProgram (lower program))) = true

/-- Each recursive key reads its independent value count and private term selector. -/
def rootField (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root)
    (callbacks : Key → Callback Symbol) (key : Key) : Finite Symbol :=
  ⟨fun size => Decoder.count (KeyedSource.family (RecursiveJoinFamily.valueProgram (lower program)) size key).members.plan,
    fun position => Decoder.decode (KeyedSource.family (RecursiveJoinFamily.termProgram code (lower program)) position.size key).members.plan position.rank,
    callbacks key⟩

/-- Forward family projection proves local root provenance independently of inverse callbacks. -/
theorem root_realizes (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root)
    (callbacks : Key → Callback Symbol) (key : Key) :
    Realizes (fun size => KeyedSource.family (RecursiveJoinFamily.termProgram code (lower program)) size key)
      (termIndex (rootField code program callbacks key)) := by
  constructor
  · intro size
    exact (RecursiveJoinFamily.family_terms code (lower program) size key).1.2.1.symm.trans
      (RecursiveJoinFamily.family_values code (lower program) size key).1.2.1
  · intro position
    rfl

/-- The root selector is total exactly on its independent value-count interval. -/
theorem root_indexed (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root)
    (callbacks : Key → Callback Symbol) (key : Key) : FiniteIndex (rootField code program callbacks key) :=
  realized_indexed _ _ (root_realizes code program callbacks key)

/-- Source size guards identify the whole record with its full recursive body environment. -/
theorem root_knot (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → CheckedBody Key Root Symbol Root) (accepted : Guarded keys complete program)
    (callbacks : Key → Callback Symbol) (key : Key) :
    (rootField code program callbacks key).counts = ((program key).compile (rootField code program callbacks)).counts ∧
    ∀ position, (rootField code program callbacks key).select position =
      (((program key).compile (rootField code program callbacks)).select position).map (KeyedTermBoundary.atKeyTerm (code key)) := by
  have realizes := (program key).realizes _ _ (root_realizes code program callbacks)
  have fields := KeyedNarySource.family_fields keys complete
    (RecursiveJoinFamily.termProgram code (lower program))
    (RecursiveJoinFamily.family_guards keys complete code (lower program) accepted).2
  constructor
  · funext size
    have count := GroupedMergeAssociativity.fields_count _ _ (fields size key)
    change Decoder.count (KeyedSource.family (RecursiveJoinFamily.termProgram code (lower program)) size key).members.plan =
      Decoder.count (KeyedSource.record (RecursiveJoinFamily.termProgram code (lower program) key)
        (fun childKey childSize => KeyedSource.family (RecursiveJoinFamily.termProgram code (lower program)) childSize childKey) size).members.plan at count
    rw [(root_realizes code program callbacks key).1 size] at count
    exact count.trans (realizes.1 size)
  · intro position
    have decoded := KeyedNarySource.fields_decode _ _ (fields position.size key) position.rank
    change (rootField code program callbacks key).select position =
      (Decoder.decode (KeyedSource.record (program key).body.term
        (fun childKey childSize => KeyedSource.family (RecursiveJoinFamily.termProgram code (lower program)) childSize childKey)
        position.size).members.plan position.rank).map (KeyedTermBoundary.atKeyTerm (code key)) at decoded
    rw [realizes.2 position] at decoded
    exact decoded

/-- Each source key boundary spends one fuel unit before entering its body callback. -/
def fuelPositions (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root) : Nat → Key → Callback Symbol
  | 0 => fun _ _ _ => []
  | fuel + 1 => fun key => KeyedTermBoundary.positions (code key)
      ((program key).compile (rootField code program (fuelPositions code program fuel)))

/-- Each fuel step is exactly the source wrapper around the compiled body field. -/
theorem field_succ (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → CheckedBody Key Root Symbol Root) (accepted : Guarded keys complete program) (fuel : Nat) (key : Key) :
    rootField code program (fuelPositions code program (fuel + 1)) key =
      KeyedTermBoundary.field (code key) ((program key).compile (rootField code program (fuelPositions code program fuel))) := by
  have knot := root_knot keys complete code program accepted (fuelPositions code program fuel) key
  simp only [rootField, KeyedTermBoundary.field]
  congr 1
  · exact knot.1
  · exact funext knot.2

/-- Height induction establishes every key's restricted inverse without a global inverse premise. -/
theorem fuel_exact (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → CheckedBody Key Root Symbol Root) (accepted : Guarded keys complete program) (fuel : Nat) :
    ∀ key, ExactBelow fuel (rootField code program (fuelPositions code program fuel) key) := by
  induction fuel with
  | zero =>
      intro key view wanted bound position
      constructor
      · simp [rootField, fuelPositions]
      · rintro ⟨term, selected, projected⟩
        rw [(root_knot keys complete code program accepted (fuelPositions code program 0) key).2 position] at selected
        obtain ⟨child, _, rfl⟩ := Option.map_eq_some_iff.mp selected
        have present := (KeyedTermBoundary.unwrap_some (code key) wanted child).mpr
          (projected.symm.trans (KeyedTermBoundary.project_member _ _ view))
        have descent := KeyedTermBoundary.unwrap_height (code key) wanted child present
        omega
  | succ fuel ih =>
      intro key
      rw [field_succ keys complete code program accepted fuel key]
      apply KeyedTermBoundary.field_exact_below
      exact (program key).exact _ (root_indexed code program _) fuel ih

/-- Every fuel-bounded candidate remains inside the actual value-count interval. -/
theorem fuel_bounded (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → CheckedBody Key Root Symbol Root) (accepted : Guarded keys complete program)
    (leaves : ∀ key, (program key).candidates) (fuel : Nat) :
    ∀ key, RecursiveNaryChoice.Bounded (rootField code program (fuelPositions code program fuel) key) := by
  induction fuel with
  | zero => intro key view wanted row member; simp [rootField, fuelPositions] at member
  | succ fuel ih =>
      intro key
      rw [field_succ keys complete code program accepted fuel key]
      exact KeyedTermBoundary.field_bounded _ _ ((program key).bounded _ ih (leaves key))

/-- Each source key preserves complete candidate order at every fuel amount. -/
theorem fuel_ordered (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root)
    (leaves : ∀ key, (program key).candidates) (fuel : Nat) :
    ∀ key view wanted, (fuelPositions code program fuel key view wanted).Pairwise (fun a b => before a b) := by
  induction fuel with
  | zero => intro key view wanted; exact .nil
  | succ fuel ih =>
      intro key
      exact KeyedTermBoundary.field_ordered _ _ ((program key).ordered _ ih (leaves key))

/-- Distinct source positions survive all fuel steps, including rows with false flags. -/
theorem fuel_distinct (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → CheckedBody Key Root Symbol Root) (accepted : Guarded keys complete program)
    (leaves : ∀ key, (program key).candidates) (fuel : Nat) :
    ∀ key, RecursiveNaryChoice.Unique (rootField code program (fuelPositions code program fuel) key) := by
  induction fuel with
  | zero => intro key view wanted; exact .nil
  | succ fuel ih =>
      intro key
      rw [field_succ keys complete code program accepted fuel key]
      exact KeyedTermBoundary.field_distinct _ _ ((program key).distinct _
        (fuel_bounded keys complete code program accepted leaves fuel) ih (leaves key))

/-- The complete inverse uses the finite requested forest to choose its recursion bound. -/
def positions (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root) (key : Key) : Callback Symbol :=
  fun view wanted => fuelPositions code program (forestHeight wanted) key view wanted

/-- Every checked callback position is exactly an independent compiled term preimage. -/
theorem positions_exact (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → CheckedBody Key Root Symbol Root) (accepted : Guarded keys complete program)
    (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) (position : Position) :
    (position, true) ∈ positions code program key view wanted ↔
      ∃ term, Decoder.decode (KeyedSource.family (RecursiveJoinFamily.termProgram code (lower program)) position.size key).members.plan position.rank = some term ∧
        project view term = wanted :=
  fuel_exact keys complete code program accepted (forestHeight wanted) key view wanted (Nat.le_refl _) position

/-- True and false source candidates stay inside the selected key's actual counted class. -/
theorem positions_bounded (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → CheckedBody Key Root Symbol Root) (accepted : Guarded keys complete program)
    (leaves : ∀ key, (program key).candidates) (key : Key) (view : View) (wanted : List (EngineTerm Symbol))
    (row : Checked) (member : row ∈ positions code program key view wanted) :
    row.1.rank < (rootField code program (positions code program) key).counts row.1.size :=
  fuel_bounded keys complete code program accepted leaves (forestHeight wanted) key view wanted row member

/-- Complete family callbacks retain ascending source size and rank order. -/
theorem positions_ordered (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root)
    (leaves : ∀ key, (program key).candidates) (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) :
    (positions code program key view wanted).Pairwise (fun a b => before a b) :=
  fuel_ordered code program leaves (forestHeight wanted) key view wanted

/-- Family callbacks contain each candidate position at most once before replay filtering. -/
theorem positions_distinct (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → CheckedBody Key Root Symbol Root) (accepted : Guarded keys complete program)
    (leaves : ∀ key, (program key).candidates) (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) :
    RecursiveCallbackDistinct.Distinct (positions code program key view wanted) :=
  fuel_distinct keys complete code program accepted leaves (forestHeight wanted) key view wanted

/-- A height-zero request cannot contain a complete source key boundary. -/
theorem unwrap_zero (code : Nat) (wanted : List (EngineTerm Symbol)) (bound : forestHeight wanted ≤ 0) :
    KeyedTermBoundary.unwrap code wanted = none := by
  cases found : KeyedTermBoundary.unwrap code wanted with
  | none => rfl
  | some child =>
      have descent := KeyedTermBoundary.unwrap_height code wanted child found
      omega

/-- Adequate fuel preserves every candidate row and flag in the mutual join callback. -/
theorem fuel_stable (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root)
    (first second : Nat) (key : Key) (view : View) (wanted : List (EngineTerm Symbol))
    (firstEnough : forestHeight wanted ≤ first) (secondEnough : forestHeight wanted ≤ second) :
    fuelPositions code program first key view wanted = fuelPositions code program second key view wanted := by
  induction first generalizing second key view wanted with
  | zero =>
      have absent := unwrap_zero (code key) wanted firstEnough
      cases second <;> simp [fuelPositions, KeyedTermBoundary.positions, absent]
  | succ first ih =>
      cases second with
      | zero =>
          have absent := unwrap_zero (code key) wanted secondEnough
          simp [fuelPositions, KeyedTermBoundary.positions, absent]
      | succ second =>
          cases found : KeyedTermBoundary.unwrap (code key) wanted with
          | none => simp [fuelPositions, KeyedTermBoundary.positions, found]
          | some child =>
              have descent := KeyedTermBoundary.unwrap_height (code key) wanted child found
              have roots : ∀ childKey, RecursiveNaryCausality.Agree (forestHeight [child])
                  (rootField code program (fuelPositions code program first) childKey)
                  (rootField code program (fuelPositions code program second) childKey) := by
                intro childKey
                refine ⟨rfl, ?_⟩
                intro childView requested small
                exact ih second childKey childView requested (by omega) (by omega)
              have same := ((program key).agree _ _ _ roots).2 .whole [child] (Nat.le_refl _)
              simpa only [fuelPositions, KeyedTermBoundary.positions, found] using same

/-- The terminating inverse satisfies the full simultaneous source callback equation. -/
theorem positions_equation (code : Key → Nat) (program : Key → CheckedBody Key Root Symbol Root)
    (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) :
    positions code program key view wanted = KeyedTermBoundary.positions (code key)
      ((program key).compile (rootField code program (positions code program))) view wanted := by
  change fuelPositions code program (forestHeight wanted) key view wanted = _
  cases height : forestHeight wanted with
  | zero =>
      have absent := unwrap_zero (code key) wanted (by omega)
      simp [fuelPositions, KeyedTermBoundary.positions, absent]
  | succ fuel =>
      cases found : KeyedTermBoundary.unwrap (code key) wanted with
      | none => simp [fuelPositions, KeyedTermBoundary.positions, found]
      | some child =>
          have descent := KeyedTermBoundary.unwrap_height (code key) wanted child found
          have roots : ∀ childKey, RecursiveNaryCausality.Agree (forestHeight [child])
              (rootField code program (fuelPositions code program fuel) childKey)
              (rootField code program (positions code program) childKey) := by
            intro childKey
            refine ⟨rfl, ?_⟩
            intro childView requested small
            exact fuel_stable code program fuel (forestHeight requested) childKey childView requested
              (by omega) (Nat.le_refl _)
          have same := ((program key).agree _ _ _ roots).2 .whole [child] (Nat.le_refl _)
          simpa only [fuelPositions, KeyedTermBoundary.positions, found] using same

end MicroCFTA.RecursiveJoinInverse
