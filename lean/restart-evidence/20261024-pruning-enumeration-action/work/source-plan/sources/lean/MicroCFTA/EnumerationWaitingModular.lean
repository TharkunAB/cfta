import MicroCFTA.EnumerationWaitingMachine
import MicroCFTA.EnumerationIndexSource

/-!
# Modular waiting counts through complete assimilation

Assimilation copies source constraints to the target before it clears the
source slot. Its intermediate counts can exceed both endpoint counts.
The complete modular update still retains the original waiting map.
-/
namespace MicroCFTA.EnumerationWaitingModular
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationWaitingIndex EnumerationWaitingMachine

/-- Read an arbitrary integer count as its signed machine representation. -/
def wrap (bits : Nat) (value : Int) : Int := (BitVec.ofInt (bits + 1) value).toInt

/-- Previously wrapped counts retain exact modular addition. -/
theorem add_wrap (bits : Nat) (value change : Int) :
    wordAdd bits (wrap bits value) change = wrap bits (value + change) := by
  simp only [wordAdd, wrap, BitVec.ofInt_toInt, BitVec.ofInt_add]

/-- A sparse machine map represents the modular image of each mathematical count. -/
def Represents (bits : Nat) (counts : Nat → Int) (waiting : Waiting) : Prop :=
  ∀ uv, waiting uv = encode (wrap bits (counts uv))

/-- Each source update retains the modular count, including intermediate signed overflow. -/
theorem bump_represents (bits : Nat) (counts : Nat → Int) (waiting : Waiting)
    (represented : Represents bits counts waiting) (change : Int) (target : Nat) :
    Represents bits (fun uv => counts uv + if uv = target then change else 0)
      (bumpWord bits change target waiting) := by
  intro uv
  by_cases same : uv = target
  · subst uv
    simp only [bumpWord, ↓reduceIte, EnumerationWaitingIndex.read, represented target, encode_read, add_wrap]
  · simpa [bumpWord, same] using represented uv

/-- The complete ordered source fold computes the exact modular occurrence sum. -/
theorem count_represents (bits : Nat) (counts : Nat → Int) (waiting : Waiting)
    (represented : Represents bits counts waiting) (change : Int) (scs : List Suspended) :
    Represents bits (fun uv => counts uv + change * occurrences uv scs) (countWord bits change scs waiting) := by
  induction scs generalizing counts waiting with
  | nil => simpa [countWord, occurrences] using represented
  | cons first rest ih =>
      have later := ih (fun uv => counts uv + if uv = first.var then change else 0) _
        (bump_represents bits counts waiting represented change first.var)
      intro uv
      change countWord bits change rest (bumpWord bits change first.var waiting) uv = _
      rw [later uv]
      by_cases same : first.var = uv
      · subst uv; simp [occurrences, Int.mul_add, Int.add_assoc]
      · simp [occurrences, same, Ne.symm same]

/-- Valid raw-slot replacement retains modular scan counts without an intermediate range premise. -/
theorem replace_represents (bits : Nat) (values : List (UVarValue Symbol)) (index : Nat)
    (old new : UVarValue Symbol) (stored : values[index]? = some old)
    (waiting : Waiting) (represented : Represents bits (fun uv => total uv values) waiting) :
    Represents bits (fun uv => total uv (values.set index new)) (replaceWord bits old new waiting) := by
  have removed := count_represents bits _ waiting represented (-1) (references old)
  have added := count_represents bits _ _ removed 1 (references new)
  intro uv
  rw [replaceWord, added uv]
  dsimp only
  rw [total_set uv index values old new stored]
  simp only [Int.neg_one_mul, Int.one_mul, Int.sub_eq_add_neg]

/-- Both source assimilation writes restore the complete original modular map, even after transient wrap. -/
theorem assimilation_waiting (bits : Nat) (graph : Graph Symbol Guard) (before : State Symbol Guard)
    (target source : Nat) (oldTarget oldSource merged : UVarValue Symbol) (different : target ≠ source)
    (targetRead : before.values[target]? = some oldTarget) (sourceRead : before.values[source]? = some oldSource)
    (intersection : intersectValues graph oldSource oldTarget = some merged)
    (waiting : Waiting) (represented : Represents bits (fun uv => total uv before.values) waiting) :
    replaceWord bits oldSource .eliminated (replaceWord bits oldTarget merged waiting) = waiting := by
  have sourceAfter : (before.values.set target merged)[source]? = some oldSource := by
    simp [different, sourceRead]
  have first := replace_represents bits before.values target oldTarget merged targetRead waiting represented
  have second := replace_represents bits _ source oldSource .eliminated sourceAfter _ first
  funext uv
  rw [second uv, represented uv]
  have same := EnumerationIndexSource.assimilation_counts graph before target source oldSource oldTarget merged
    different sourceRead targetRead intersection uv
  exact congrArg (fun value => encode (wrap bits value)) same

/-- A fitting nonnegative endpoint count has its exact signed representation. -/
theorem wrap_exact (bits : Nat) (value : Int) (nonnegative : 0 ≤ value) (bounded : value < (2 : Int) ^ bits) :
    wrap bits value = value := by
  simpa [wordAdd, wrap] using wordAdd_exact bits value 0 (by omega) (by omega)

/-- Exact count correctness is needed only at the observed endpoint, not throughout a transient update. -/
theorem correct_of_endpoint (bits : Nat) (values : List (UVarValue Symbol)) (waiting : Waiting)
    (represented : Represents bits (fun uv => total uv values) waiting)
    (bounded : ∀ uv, total uv values < (2 : Int) ^ bits) : Correct values waiting := by
  intro uv
  rw [represented uv, wrap_exact bits _ (total_nonnegative uv values) (bounded uv)]

/-- Below one full word period, a nonnegative count wraps to zero exactly when it is zero. -/
theorem wrap_zero_iff (bits : Nat) (value : Int) (nonnegative : 0 ≤ value)
    (bounded : value < (2 : Int) ^ (bits + 1)) : wrap bits value = 0 ↔ value = 0 := by
  constructor
  · intro zero
    have equal : BitVec.ofInt (bits + 1) value = 0 := BitVec.eq_of_toInt_eq (by simpa [wrap] using zero)
    have digits := congrArg BitVec.toNat equal
    simp [BitVec.toNat_ofInt, Int.natCast_pow, Int.emod_eq_of_lt nonnegative bounded] at digits
    omega
  · rintro rfl; simp [wrap]

/-- Scheduling uses only map keys, so the full word-period bound suffices even for negative stored counts. -/
theorem support_exact (bits : Nat) (values : List (UVarValue Symbol)) (waiting : Waiting)
    (represented : Represents bits (fun uv => total uv values) waiting)
    (bounded : ∀ uv, total uv values < (2 : Int) ^ (bits + 1)) (uv : Nat) :
    waiting uv ≠ none ↔ ∃ value ∈ values, ∃ sc ∈ references value, sc.var = uv := by
  rw [represented uv, ← total_positive]
  have nonnegative := total_nonnegative uv values
  have zero := wrap_zero_iff bits (total uv values) nonnegative (bounded uv)
  by_cases absent : total uv values = 0
  · rw [zero.mpr absent]; simp [encode, absent]
  · have nonzero : wrap bits (total uv values) ≠ 0 := fun value => absent (zero.mp value)
    simp [encode, nonzero]
    omega

/-- The actual machine map supplies the same complete key view as the reachable mathematical index. -/
theorem waitingKeys_exact (bits : Nat) (graph : Graph Symbol Guard)
    (state : EnumerationExpandableIndex.Cached Symbol Guard)
    (reached : EnumerationExpandableIndex.Reachable graph state) (waiting : Waiting)
    (represented : Represents bits (fun uv => total uv state.core.values) waiting)
    (bounded : ∀ uv, total uv state.core.values < (2 : Int) ^ (bits + 1))
    (keys : List Nat) (keyView : ∀ uv, uv ∈ keys ↔ waiting uv ≠ none) :
    EnumerationIndexSelection.WaitingKeys state keys := by
  intro uv
  rw [keyView uv, support_exact bits state.core.values waiting represented bounded uv,
    EnumerationWaitingIndex.support_exact _ _ reached.correct.waiting uv]

/-- A scheduler fed by modular machine counters completes with exactly the original scan result. -/
theorem selection_complete (bits : Nat) (graph : Graph Symbol Guard)
    (state : EnumerationExpandableIndex.Cached Symbol Guard)
    (reached : EnumerationExpandableIndex.Reachable graph state) (waiting : Waiting)
    (represented : Represents bits (fun uv => total uv state.core.values) waiting)
    (bounded : ∀ uv, total uv state.core.values < (2 : Int) ^ (bits + 1))
    (keys : List Nat) (keyView : ∀ uv, uv ∈ keys ↔ waiting uv ≠ none)
    (total : UnionFind.Total state.core.representatives) :
    ∃ fuel result oldAfter newAfter,
      Success (findExpandable graph fuel) state.core result oldAfter ∧
      Success (EnumerationIndexSelection.findIndexed fuel (EnumerationIndexSelection.candidates state) keys)
        state.core result newAfter := by
  obtain ⟨fuel, result, oldAfter, newAfter, oldDone, newDone, _⟩ := EnumerationIndexSelection.selection_complete
    graph state reached keys (waitingKeys_exact bits graph state reached waiting represented bounded keys keyView) total
  exact ⟨fuel, result, oldAfter, newAfter, oldDone, newDone⟩

end MicroCFTA.EnumerationWaitingModular
