import MicroCFTA.SourceSynthesisProgramRolesUnmarkedWrite
import MicroCFTA.SourcePruningEnumerationFinalize

/-!
# Program roles through actual unmarked finalization

One actual finalizer retains its complete stable execution receipt.
The unmarked fragment has no Program-role requirement.
The proof resets ancestry before the same raw write.
Safety remains conditional on the original finalizer prerequisites.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesUnmarkedFinalize
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
open InternedConstructorTemplates SourceSynthesisProgramEnumerationRoles
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol

/-- One complete unmarked finalizer retains all current marked roles and protected roots. -/
theorem complete_unmarked_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (heap : NativeHeap) (before : Cached)
    (target : Nat) (fragment : Fragment) (old : UVarValue Symbol)
    (stored : before.core.values[target]? = some old)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (storage : StorageValid before.core)
    (bounded : FragmentBound before.core.counter fragment)
    (realized : PendingRealized heap before.core)
    (slots : ProgramSlots valid literal heap before.core marked)
    (unmarked : ¬marked target) :
    ∃ (fuel : Nat) (after : Cached),
      (∀ extra, SourcePruningEnumerationFinalize.run heap (fuel + extra) target fragment before = some after) ∧
      ExceptT.run (SourcePruningEnumerationFinalize.finish (EnumGuard := Constraint) target fragment before.core) =
        [.ok (fragment, after.core)] ∧
      after.core = {before.core with
        values := before.core.values.set target (.enumerated fragment),
        expansionAncestry := []} ∧
      after.core.values[target]? = some (.enumerated fragment) ∧
      after.expandable = (fun slot => if slot = target then false else before.expandable slot) ∧
      after.waiting = EnumerationCanonicalWaiting.count roots (-1) (references old) before.waiting ∧
      Roots after.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      (Safe before.core → IsRoot before.core.representatives target → Safe after.core) ∧
      ProgramSlots valid literal heap after.core marked ∧
      ∀ held, marked held → Protected held before.core after.core := by
  obtain ⟨fuel, after, running, raw, core, finalStored, finalFlag, finalWaiting,
    finalPaths, finalCounts, finalFlags, finalStorage, finalRealized, safeFinish⟩ :=
    SourcePruningEnumerationFinalize.complete heap before target fragment old stored roots paths
      counts flags storage bounded realized
  have resetSlots : ProgramSlots valid literal heap
      {before.core with expansionAncestry := []} marked :=
    ⟨slots.bounded, slots.roots, slots.incoming, slots.stored⟩
  have written : Success (EnumerationState.setValue target (.enumerated fragment))
      {before.core with expansionAncestry := []} () after.core :=
    (EnumerationDriver.modify_success _ _ _).mpr core
  have roles := SourceSynthesisProgramRolesUnmarkedWrite.setValue_unmarked_program_slots
    valid literal heap _ after.core marked resetSlots target unmarked (.enumerated fragment)
    (by intro held known sc member; cases member) written
  refine ⟨fuel, after, running, raw, core, finalStored, finalFlag, finalWaiting,
    finalPaths, finalCounts, finalFlags, finalStorage, finalRealized, safeFinish, roles.2.1, ?_⟩
  intro held known
  have receipt := roles.2.2 held known
  exact ⟨receipt.value, receipt.root, receipt.classes⟩

end MicroCFTA.SourceSynthesisProgramRolesUnmarkedFinalize
