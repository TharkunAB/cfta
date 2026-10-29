import MicroCFTA.NumberedTerms
import MicroCFTA.EnumerationDriver
import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationFinalize

/-!
# Finite-assignment cost at actual enumeration storage operations

Only pending graph slots contribute to the cost.
Pure equality slots, completed fragments and eliminated slots contribute zero.
These laws do not bound neutral recursive preparation or callback steps.
-/
namespace MicroCFTA.EnumerationStorageProgress
open Language EnumerationState EnumerationCorrectness
variable {Symbol Guard : Type}

private def weight (assignment : Nat → Term Symbol) (uv : Nat) : UVarValue Symbol → Nat
  | .unenumerated (some _) _ => NumberedTerms.size (assignment uv)
  | _ => 0

private def scanCost (assignment : Nat → Term Symbol) : Nat → List (UVarValue Symbol) → Nat
  | _, [] => 0
  | uv, first :: rest => weight assignment uv first + scanCost assignment (uv + 1) rest

/-- Count assigned constructors at the actual pending graph slots. -/
def pendingSize (state : State Symbol Guard) (assignment : Nat → Term Symbol) : Nat :=
  scanCost assignment 0 state.values

private theorem from_append (assignment : Nat → Term Symbol) (first second : List (UVarValue Symbol))
    (start : Nat) :
    scanCost assignment start (first ++ second) =
      scanCost assignment start first + scanCost assignment (start + first.length) second := by
  induction first generalizing start with
  | nil => simp [scanCost]
  | cons value rest ih =>
      simp [scanCost, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem from_congr (values : List (UVarValue Symbol)) (start : Nat)
    (first second : Nat → Term Symbol)
    (agree : ∀ uv, start ≤ uv → uv < start + values.length → first uv = second uv) :
    scanCost first start values = scanCost second start values := by
  induction values generalizing start with
  | nil => rfl
  | cons value rest ih =>
      have head : first start = second start := agree start (Nat.le_refl _) (by
        simp only [List.length_cons]
        omega)
      have tail : scanCost first (start + 1) rest = scanCost second (start + 1) rest := by
        apply ih (start + 1)
        intro uv lower upper
        apply agree uv (by omega)
        simp only [List.length_cons]
        omega
      simp only [scanCost, weight, head, tail]

private theorem from_set (assignment : Nat → Term Symbol) (values : List (UVarValue Symbol))
    (start target : Nat) (old new : UVarValue Symbol) (stored : values[target]? = some old) :
    scanCost assignment start (values.set target new) + weight assignment (start + target) old =
      scanCost assignment start values + weight assignment (start + target) new := by
  induction values generalizing start target with
  | nil => simp at stored
  | cons value rest ih =>
      cases target with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at stored
          subst value
          simp [scanCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      | succ target =>
          simp only [List.getElem?_cons_succ] at stored
          have tail := ih (start + 1) target stored
          simp only [List.set_cons_succ, scanCost]
          have index : start + (target + 1) = start + 1 + target := by omega
          rw [index]
          omega

private theorem allocated_same (node : Option Nat) (before : State Symbol Guard)
    (assignment : Nat → Term Symbol) :
    pendingSize (allocated node before) assignment = pendingSize before assignment +
      match (generalizing := false) node with
      | none => 0
      | some _ => NumberedTerms.size (assignment before.values.length) := by
  cases node <;> simp [pendingSize, allocated, from_append, scanCost, weight]

private theorem allocated_extended (node : Option Nat) (before : State Symbol Guard)
    (assignment extended : Nat → Term Symbol)
    (aligned : before.counter = before.values.length)
    (agree : ∀ uv < before.counter, extended uv = assignment uv) :
    pendingSize (allocated node before) extended = pendingSize before assignment +
      match (generalizing := false) node with
      | none => 0
      | some _ => NumberedTerms.size (extended before.counter) := by
  have old : pendingSize before extended = pendingSize before assignment := by
    apply from_congr before.values 0 extended assignment
    intro uv _lower upper
    apply agree uv
    omega
  simpa only [old, aligned] using allocated_same node before extended

private theorem size_positive (term : Term Symbol) : 0 < NumberedTerms.size term := by
  cases term with
  | node symbol children => simp only [NumberedTerms.size]; omega

/-- The literal startup has exactly the assigned root cost. -/
theorem initial_pendingSize (root : Nat) (assignment : Nat → Term Symbol) :
    pendingSize (initial root : State Symbol Guard) assignment = NumberedTerms.size (assignment 0) := by
  simp [pendingSize, initial, scanCost, weight]

/-- A literal slot write changes only that slot's pending graph cost. -/
theorem values_set_pendingSize (before : State Symbol Guard) (target : Nat)
    (old new : UVarValue Symbol) (assignment : Nat → Term Symbol)
    (stored : before.values[target]? = some old) :
    pendingSize {before with values := before.values.set target new} assignment +
        (match (generalizing := false) old with
        | .unenumerated (some _) _ => NumberedTerms.size (assignment target)
        | _ => 0) =
      pendingSize before assignment +
        (match (generalizing := false) new with
        | .unenumerated (some _) _ => NumberedTerms.size (assignment target)
        | _ => 0) := by
  simpa only [pendingSize, weight, Nat.zero_add] using
    from_set assignment before.values 0 target old new stored

/-- Actual allocation adds only the fresh graph slot's assigned cost. -/
theorem allocate_pendingSize (node : Option Nat) (before after : State Symbol Guard) (uv : Nat)
    (assignment extended : Nat → Term Symbol)
    (aligned : before.counter = before.values.length)
    (agree : ∀ old < before.counter, extended old = assignment old)
    (success : Success (allocate node) before uv after) :
    pendingSize after extended = pendingSize before assignment +
      match (generalizing := false) node with
      | none => 0
      | some _ => NumberedTerms.size (extended uv) := by
  have exactState : uv = before.counter ∧ after = allocated node before := by
    simpa [Success, allocate_exact, ExceptT.run] using success
  obtain ⟨rfl, rfl⟩ := exactState
  exact allocated_extended node before assignment extended aligned agree

/-- An actual completed write removes the old pending graph slot's full cost. -/
theorem setValue_enumerated_pendingSize (before after : State Symbol Guard) (target handle : Nat)
    (scs : List Suspended) (fragment : Fragments.Fragment Symbol)
    (assignment : Nat → Term Symbol)
    (stored : before.values[target]? = some (.unenumerated (some handle) scs))
    (success : Success (setValue target (.enumerated fragment)) before () after) :
    pendingSize after assignment + NumberedTerms.size (assignment target) = pendingSize before assignment := by
  obtain rfl := (EnumerationDriver.modify_success _ before after).mp success
  simpa only [pendingSize, weight, Nat.zero_add, Nat.add_zero] using
    from_set assignment before.values 0 target (.unenumerated (some handle) scs) (.enumerated fragment) stored

end MicroCFTA.EnumerationStorageProgress

namespace MicroCFTA.SourcePruningEnumerationStorageProgress
open Language EnumerationState EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual native allocation has the same cost as its exact core allocation. -/
theorem allocate_pendingSize
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (node : Option Nat)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (uv : Nat)
    (assignment extended : Nat → Term Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (agree : ∀ old < before.core.counter, extended old = assignment old)
    (observed : SourcePruningEnumerationCachedChild.allocate heap node before = some (uv, after)) :
    pendingSize after.core extended = pendingSize before.core assignment +
      match (generalizing := false) node with
      | none => 0
      | some _ => NumberedTerms.size (extended uv) := by
  simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at observed
  obtain ⟨_flag, _classified, same⟩ := observed
  have uvSame : before.core.counter = uv := congrArg Prod.fst same
  have coreSame : allocated node before.core = after.core := congrArg (fun result => result.2.core) same
  rw [← coreSame, ← uvSame]
  exact EnumerationStorageProgress.allocated_extended node before.core assignment extended aligned agree

/-- Actual own-class allocation adds only zero-cost equality slots. -/
theorem suspendMany_pendingSize
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (suspended : List Suspended)
    (assignment : Nat → Term Symbol)
    (observed : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = some (suspended, after)) :
    pendingSize after.core assignment = pendingSize before.core assignment := by
  induction tries generalizing before after suspended with
  | nil =>
      have same : ([], before) = (suspended, after) := Option.some.inj observed
      have cacheSame : before = after := congrArg Prod.snd same
      simp only [cacheSame]
  | cons trie rest ih =>
      simp only [SourcePruningEnumerationCachedOwn.suspendMany,
        Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocatedRun, result, continued, same⟩ := observed
      have tail := ih allocation.2 result.2 result.1 continued
      have cacheSame : result.2 = after := congrArg Prod.snd same
      simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at allocatedRun
      obtain ⟨_flag, _classified, allocationSame⟩ := allocatedRun
      have coreSame : allocated none before.core = allocation.2.core :=
        congrArg (fun result => result.2.core) allocationSame
      rw [← cacheSame, tail, ← coreSame]
      simpa only [Nat.add_zero] using EnumerationStorageProgress.allocated_same none before.core assignment

/-- An actual successful native finalizer removes the captured pending graph cost. -/
theorem finalize_pendingSize
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target handle : Nat)
    (fragment : Fragments.Fragment Symbol) (scs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (assignment : Nat → Term Symbol)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    pendingSize after.core assignment + NumberedTerms.size (assignment target) =
      pendingSize before.core assignment := by
  simp only [SourcePruningEnumerationFinalize.run, Option.bind_eq_some_iff] at observed
  obtain ⟨_old, _stored, written⟩ := observed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  subst after
  change EnumerationStorageProgress.scanCost assignment 0 (before.core.values.set target (.enumerated fragment)) +
    NumberedTerms.size (assignment target) = EnumerationStorageProgress.scanCost assignment 0 before.core.values
  simpa only [EnumerationStorageProgress.weight, Nat.zero_add, Nat.add_zero] using
    EnumerationStorageProgress.from_set assignment before.core.values 0 target
      (.unenumerated (some handle) scs) (.enumerated fragment) stored

/-- The finalizer alone strictly lowers cost at an actual pending graph target. -/
theorem finalize_pendingSize_lt
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target handle : Nat)
    (fragment : Fragments.Fragment Symbol) (scs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (assignment : Nat → Term Symbol)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    pendingSize after.core assignment < pendingSize before.core assignment := by
  have exactCost := finalize_pendingSize heap fuel target handle fragment scs before after assignment stored observed
  have positive := EnumerationStorageProgress.size_positive (assignment target)
  omega

/-- Opaque allocation and captured-hole finalization can transfer the same cost. -/
theorem opaque_transfer_pendingSize
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target handle freshHandle : Nat)
    (scs : List Suspended) (before middle after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (assignment extended : Nat → Term Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (agree : ∀ old < before.core.counter, extended old = assignment old)
    (fresh : extended before.core.counter = assignment target)
    (allocation : SourcePruningEnumerationCachedChild.allocate heap (some freshHandle) before =
      some (before.core.counter, middle))
    (finalized : SourcePruningEnumerationFinalize.run heap fuel target (.hole before.core.counter) middle =
      some after) :
    pendingSize after.core extended = pendingSize before.core assignment := by
  have allocatedCost := allocate_pendingSize heap (some freshHandle) before middle before.core.counter
    assignment extended aligned agree allocation
  simp only at allocatedCost
  have inside : target < before.core.values.length :=
    (List.getElem?_eq_some_iff.mp stored).elim (fun bound _ => bound)
  have middleStored : middle.core.values[target]? = some (.unenumerated (some handle) scs) := by
    simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at allocation
    obtain ⟨_flag, _classified, same⟩ := allocation
    have coreSame : allocated (some freshHandle) before.core = middle.core :=
      congrArg (fun result => result.2.core) same
    rw [← coreSame]
    simpa only [allocated, List.getElem?_append_left inside] using stored
  have completedCost := finalize_pendingSize heap fuel target handle (.hole before.core.counter) scs
    middle after extended middleStored finalized
  have oldTarget : extended target = assignment target := agree target (by omega)
  rw [fresh] at allocatedCost
  rw [oldTarget] at completedCost
  omega

end MicroCFTA.SourcePruningEnumerationStorageProgress
