import MicroCFTA.SourceCurrentAllocatedSharedTargetWorker
import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion

/-!
# Successful shared target execution under larger bounds

Successful force and leaf observations retain the same complete shared
state under larger execution bounds. These statements need no heap,
language, or cache-admission premise. They preserve success; they do not
assert that an arbitrary initial state completes.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability
open InternedConstructorTemplates SourceCurrentAllocatedSharedTargetState
open SourceCurrentAllocatedSharedTargetWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A successful force retains its actual stored result and every state field. -/
theorem force_done_stable
    {p h m s n largerP largerH largerM largerS largerN : Nat}
    {record : Record} {values : List (Value Symbol Guard)} {path : Path}
    {before after : State width} {value : Value Symbol Guard}
    (actual : force p h m s n record values path before = .done value after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) (enoughM : m ≤ largerM)
    (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    force largerP largerH largerM largerS largerN record values path before = .done value after := by
  cases present : before.targets path with
  | some result => simpa only [force, present] using actual
  | none =>
      cases executed : SourceCurrentAllocatedTargetWorker.target p h m s n values
          (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
      | done result checked saved =>
          have stable := SourceCurrentAllocatedTargetWorkerCompletion.target_done_stable executed
            enoughP enoughH enoughM enoughS enoughN
          simp only [force, present, executed] at actual
          simpa only [force, present, stable] using actual
      | failed =>
          simp only [force, present, executed] at actual
          cases actual

/-- More native instructions retain any successful complete shared return. -/
theorem step_done_stable {n largerN : Nat} {target input value : Value Symbol Guard}
    {before after : State width}
    (actual : step n target input before = .done value after) (enoughN : n ≤ largerN) :
    step largerN target input before = .done value after := by
  cases executed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) before.checked with
  | done result checked =>
      have stable := SourceEqualityNativeDemand.done_stable n (largerN - n) _ before.checked checked result executed
      rw [show n + (largerN - n) = largerN by omega] at stable
      simp only [step, executed] at actual
      simpa only [step, stable] using actual
  | yielded | failed | blocked | constraintError =>
      simp only [step, executed] at actual
      cases actual

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem bind_done_iff (first : Outcome width)
    (next : Value Symbol Guard → State width → Outcome width)
    (value : Value Symbol Guard) (after : State width) :
    first.bind next = .done value after ↔
      ∃ target middle, first = .done target middle ∧ next target middle = .done value after := by
  cases first with
  | done target middle =>
      constructor
      · intro actual; exact ⟨target, middle, rfl, actual⟩
      · rintro ⟨_, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, impossible, _⟩; cases impossible

/-- Larger target and native bounds preserve force-before-intersection success. -/
theorem leaf_done_stable
    {p h m s n largerP largerH largerM largerS largerN : Nat}
    {record : Record} {values : List (Value Symbol Guard)} {path : Path}
    {input value : Value Symbol Guard} {before after : State width}
    (actual : leaf p h m s n record values path input before = .done value after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) (enoughM : m ≤ largerM)
    (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    leaf largerP largerH largerM largerS largerN record values path input before = .done value after := by
  obtain ⟨target, middle, forced, returned⟩ := (bind_done_iff _ _ value after).mp actual
  simp only [leaf, force_done_stable forced enoughP enoughH enoughM enoughS enoughN, Outcome.bind]
  exact step_done_stable returned enoughN

/-- Two successful leaf bounds identify the same value and complete shared state. -/
theorem leaf_done_unique
    {p h m s n otherP otherH otherM otherS otherN : Nat}
    {record : Record} {values : List (Value Symbol Guard)} {path : Path}
    {input first second : Value Symbol Guard} {before after later : State width}
    (one : leaf p h m s n record values path input before = .done first after)
    (two : leaf otherP otherH otherM otherS otherN record values path input before = .done second later) :
    first = second ∧ after = later := by
  have firstStable := leaf_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
    (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := leaf_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
    (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

end MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability
