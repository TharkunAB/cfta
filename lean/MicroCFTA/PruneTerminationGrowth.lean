import Std

/-!
# Historical growth of residual conjunctions

The old conjunction function removed Top and identical operands only.
Three equal positions can have different residual guard trees. Equality
narrowing intersects each position with the other two positions. The resulting
guard trees keep growing. This model permits either operand order at each
intersection. Interned node identities can select either order in the source.
-/
namespace MicroCFTA.PruneTerminationGrowth

/-- The guard fragment needed for the finite acyclic counterexample. -/
inductive Guard where
  | top
  | same
  | and (left right : Guard)
  | or (left right : Guard)
  deriving DecidableEq, Repr

/-- Count guard constructors, including Boolean constructors. -/
def size : Guard → Nat
  | .top | .same => 1
  | .and left right | .or left right => 1 + size left + size right

/-- The former source conjunction function. -/
def oldCombine (left right : Guard) : Guard :=
  if left = .top then right else
  if right = .top then left else
  if left = right then left else .and left right

/-- Each generated guard is evaluated on the same leaf at its root. -/
def acceptsLeaf : Guard → Bool
  | .top | .same => true
  | .and left right => acceptsLeaf left && acceptsLeaf right
  | .or left right => acceptsLeaf left || acceptsLeaf right

theorem every_guard_accepts (guard : Guard) : acceptsLeaf guard = true := by
  induction guard <;> simp_all [acceptsLeaf]

/-- Either order of the binary conjunction selected by interned node order. -/
inductive Pairing (left right : Guard) : Guard → Prop where
  | forward : Pairing left right (.and left right)
  | reverse : Pairing left right (.and right left)

theorem pairing_size (joined : Pairing left right result) :
    size result = 1 + size left + size right := by
  cases joined <;> simp [size] <;> omega

theorem pairing_not_top (joined : Pairing left right result) : result ≠ .top := by
  cases joined <;> simp

/-- Both permitted orders execute the old function when no shortcut applies. -/
theorem pairing_old (joined : Pairing left right result)
    (leftNotTop : left ≠ .top) (rightNotTop : right ≠ .top) (different : left ≠ right) :
    result = oldCombine left right ∨ result = oldCombine right left := by
  cases joined
  · exact Or.inl (by simp [oldCombine, leftNotTop, rightNotTop, different])
  · exact Or.inr (by simp [oldCombine, leftNotTop, rightNotTop, Ne.symm different])

/-- Read the smaller child of a conjunction. -/
def smaller : Guard → Guard
  | .and left right => if size left < size right then left else right
  | guard => guard

theorem pairing_smaller (joined : Pairing large small result)
    (ordered : size small < size large) : smaller result = small := by
  cases joined <;> simp only [smaller]
  · have : ¬size large < size small := by omega
    simp [this]
  · simp [ordered]

/-- One simultaneous equality-narrowing pass on three distinct child guards. -/
structure Round (a b c a' b' c' : Guard) where
  bc : Guard
  ac : Guard
  ab : Guard
  pairBC : Pairing b c bc
  pairAC : Pairing a c ac
  pairAB : Pairing a b ab
  resultA : Pairing bc a a'
  resultB : Pairing ac b b'
  resultC : Pairing ab c c'

/-- Distinct guard syntax can describe the same language. -/
structure DistinctAt (width : Nat) (a b c : Guard) : Prop where
  sizeA : size a = width
  sizeB : size b = width
  sizeC : size c = width
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c
  aNotTop : a ≠ .top
  bNotTop : b ≠ .top
  cNotTop : c ≠ .top

/-- Every operand order produces distinct guards of size `3 * width + 2`. -/
theorem round_growth (before : DistinctAt width a b c) (step : Round a b c a' b' c') :
    DistinctAt (3 * width + 2) a' b' c' := by
  have inputA := before.sizeA
  have inputB := before.sizeB
  have inputC := before.sizeC
  have sizeBC := pairing_size step.pairBC
  have sizeAC := pairing_size step.pairAC
  have sizeAB := pairing_size step.pairAB
  have sizeA := pairing_size step.resultA
  have sizeB := pairing_size step.resultB
  have sizeC := pairing_size step.resultC
  have smallerA : smaller a' = a := pairing_smaller step.resultA (by omega)
  have smallerB : smaller b' = b := pairing_smaller step.resultB (by omega)
  have smallerC : smaller c' = c := pairing_smaller step.resultC (by omega)
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_,
    pairing_not_top step.resultA, pairing_not_top step.resultB, pairing_not_top step.resultC⟩
  · intro same
    exact before.ab (by rw [←smallerA, ←smallerB, same])
  · intro same
    exact before.ac (by rw [←smallerA, ←smallerC, same])
  · intro same
    exact before.bc (by rw [←smallerB, ←smallerC, same])

/-- No old conjunction shortcut applies at either level of a round. -/
theorem round_old (before : DistinctAt width a b c) (step : Round a b c a' b' c') :
    (step.bc = oldCombine b c ∨ step.bc = oldCombine c b) ∧
    (a' = oldCombine step.bc a ∨ a' = oldCombine a step.bc) := by
  refine ⟨pairing_old step.pairBC before.bNotTop before.cNotTop before.bc, ?_⟩
  apply pairing_old step.resultA (pairing_not_top step.pairBC) before.aNotTop
  intro same
  have sizes := pairing_size step.pairBC
  rw [same] at sizes
  have := before.sizeA
  have := before.sizeB
  have := before.sizeC
  omega

/-- Each of the six intersections uses the historical conjunction function. -/
theorem round_all_old (before : DistinctAt width a b c) (step : Round a b c a' b' c') :
    (step.bc = oldCombine b c ∨ step.bc = oldCombine c b) ∧
    (step.ac = oldCombine a c ∨ step.ac = oldCombine c a) ∧
    (step.ab = oldCombine a b ∨ step.ab = oldCombine b a) ∧
    (a' = oldCombine step.bc a ∨ a' = oldCombine a step.bc) ∧
    (b' = oldCombine step.ac b ∨ b' = oldCombine b step.ac) ∧
    (c' = oldCombine step.ab c ∨ c' = oldCombine c step.ab) := by
  have inputA := before.sizeA
  have inputB := before.sizeB
  have inputC := before.sizeC
  refine ⟨(round_old before step).1,
    pairing_old step.pairAC before.aNotTop before.cNotTop before.ac,
    pairing_old step.pairAB before.aNotTop before.bNotTop before.ab,
    (round_old before step).2, ?_, ?_⟩
  · apply pairing_old step.resultB (pairing_not_top step.pairAC) before.bNotTop
    intro same
    have sizes := pairing_size step.pairAC
    rw [same] at sizes
    omega
  · apply pairing_old step.resultC (pairing_not_top step.pairAB) before.cNotTop
    intro same
    have sizes := pairing_size step.pairAB
    rw [same] at sizes
    omega

/-- The first three source residual guards. -/
def initial : Guard × Guard × Guard :=
  (.same, .and .same .same, .or .same .same)

/-- One permitted source operand order for a complete pass. -/
def pass (state : Guard × Guard × Guard) : Guard × Guard × Guard :=
  let (a, b, c) := state
  (oldCombine (oldCombine c b) a,
   oldCombine (oldCombine c a) b,
   oldCombine (oldCombine b a) c)

/-- The first pass has the observed width and pairwise distinct syntax. -/
theorem first_pass : DistinctAt 9 (pass initial).1 (pass initial).2.1 (pass initial).2.2 := by
  constructor <;> decide +kernel

/-- Select either source operand order before using the historical shortcuts. -/
def oriented (reverse : Bool) (left right : Guard) : Guard :=
  if reverse then oldCombine right left else oldCombine left right

/-- All six independent operand-order choices in the first equality pass. -/
def firstWith (ab ac bc outerA outerB outerC : Bool) : Guard × Guard × Guard :=
  let (a, b, c) := initial
  (oriented outerA (oriented bc b c) a,
   oriented outerB (oriented ac a c) b,
   oriented outerC (oriented ab a b) c)

/-- The initial growth does not depend on interned node identities. -/
theorem first_with_distinct (ab ac bc outerA outerB outerC : Bool) :
    DistinctAt 9 (firstWith ab ac bc outerA outerB outerC).1
      (firstWith ab ac bc outerA outerB outerC).2.1
      (firstWith ab ac bc outerA outerB outerC).2.2 := by
  cases ab <;> cases ac <;> cases bc <;> cases outerA <;> cases outerB <;> cases outerC <;>
    constructor <;> decide +kernel

/-- A nonempty sequence of source rounds after the first pass. -/
inductive Runs : Nat → Nat → Guard → Guard → Guard → Prop where
  | first : Runs 0 9 (firstWith ab ac bc outerA outerB outerC).1
      (firstWith ab ac bc outerA outerB outerC).2.1
      (firstWith ab ac bc outerA outerB outerC).2.2
  | next (previous : Runs rounds width a b c) (step : Round a b c a' b' c') :
      Runs (rounds + 1) (3 * width + 2) a' b' c'

theorem runs_distinct (run : Runs rounds width a b c) : DistinctAt width a b c := by
  induction run with
  | first => exact first_with_distinct _ _ _ _ _ _
  | next _ step ih => exact round_growth ih step

/-- The residual syntax is unbounded, although every guard accepts the same leaf. -/
theorem runs_width (run : Runs rounds width a b c) : width + 1 = 10 * 3 ^ rounds := by
  induction run with
  | first => decide
  | next _ _ ih => simp only [Nat.pow_succ]; omega

/-- No next round can equal its preceding state. -/
theorem round_not_fixed (before : DistinctAt width a b c) (step : Round a b c a' b' c') :
    a' ≠ a := by
  have after := (round_growth before step).sizeA
  intro same
  rw [same, before.sizeA] at after
  omega

end MicroCFTA.PruneTerminationGrowth
