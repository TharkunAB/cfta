import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.EnumerationRenderability

/-!
# Graph carriers through actual own allocation and finalization

Own-class allocation retains earlier graph-bearing classes and references.
Finalization stores a fragment whose holes already carry graph provenance.
Residual recording retains that same fragment and its carried holes.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationCarriers EnumerationGraphReferences
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual cached allocation retains every earlier carrier and stored reference. -/
theorem allocate_carriers
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (node : Option Nat)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (uv : Nat)
    (references : ReferencesCarry before.core)
    (observed : allocate heap node before = some (uv, after)) :
    PreservesCarriers before.core after.core ∧ ReferencesCarry after.core := by
  simp only [allocate, Option.map_eq_some_iff] at observed
  obtain ⟨flag, _classified, same⟩ := observed
  have coreSame : allocated node before.core = after.core := congrArg (fun result => result.2.core) same
  rw [← coreSame]
  have preserved := allocation_carriers node before.core
  exact ⟨preserved, references_transport before.core _ references preserved
    (allocation_origin node before.core) rfl⟩

end MicroCFTA.SourcePruningEnumerationCachedChild

namespace MicroCFTA.SourcePruningEnumerationCachedOwn
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCarriers EnumerationGraphReferences
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual ordered own-class suspension retains every earlier carrier and reference. -/
theorem suspendMany_carriers
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (suspended : List Suspended)
    (references : ReferencesCarry before.core)
    (observed : suspendMany heap tries before = some (suspended, after)) :
    PreservesCarriers before.core after.core ∧ ReferencesCarry after.core := by
  induction tries generalizing before after suspended with
  | nil =>
      have same : ([], before) = (suspended, after) := Option.some.inj observed
      have cacheSame : before = after := congrArg Prod.snd same
      subst after
      exact ⟨.refl before.core, references⟩
  | cons trie rest ih =>
      simp only [suspendMany, Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocated, result, continued, same⟩ := observed
      obtain ⟨allocatedCarriers, allocatedReferences⟩ :=
        SourcePruningEnumerationCachedChild.allocate_carriers heap none before allocation.2
          allocation.1 references allocated
      obtain ⟨resultCarriers, resultReferences⟩ := ih allocation.2 result.2 result.1
        allocatedReferences continued
      have cacheSame : result.2 = after := congrArg Prod.snd same
      rw [← cacheSame]
      exact ⟨allocatedCarriers.trans resultCarriers, resultReferences⟩

end MicroCFTA.SourcePruningEnumerationCachedOwn

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCarriers EnumerationGraphReferences EnumerationRenderability
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- The actual final write retains carriers and stores the already carried fragment holes. -/
theorem written_carriers
    (before after : EnumerationState.State Symbol EnumGuard) (target : Nat)
    (fragment : Fragments.Fragment Symbol) (references : ReferencesCarry before)
    (holes : FragmentCarries before fragment)
    (written : after = {before with
      values := before.values.set target (.enumerated fragment)
      expansionAncestry := []}) :
    PreservesCarriers before after ∧ ReferencesCarry after ∧ FragmentCarries after fragment := by
  subst after
  have actual := write_references before target fragment references holes
  exact ⟨actual.1, actual.2, holes.preserve fragment actual.1⟩

/-- An actual indexed finalization retains graph carriers at its exact returned cache. -/
theorem run_carriers
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (references : ReferencesCarry before.core) (holes : FragmentCarries before.core fragment)
    (observed : run heap fuel target fragment before = some after) :
    PreservesCarriers before.core after.core ∧ ReferencesCarry after.core ∧
      FragmentCarries after.core fragment := by
  simp only [run, Option.bind_eq_some_iff] at observed
  obtain ⟨_old, _stored, written⟩ := observed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  subst after
  exact written_carriers before.core _ target fragment references holes rfl

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCarriers EnumerationGraphReferences
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The actual completed-edge residual retains old references and the returned fragment holes. -/
theorem finish_carriers (residual : Option Constraint) (fragment : Fragments.Fragment Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (references : ReferencesCarry before.core) (holes : FragmentCarries before.core fragment) :
    PreservesCarriers before.core (finish residual fragment before).core ∧
      ReferencesCarry (finish residual fragment before).core ∧
      FragmentCarries (finish residual fragment before).core fragment := by
  have actual : Success (recordResidual residual fragment) before.core ()
      (finish residual fragment before).core := by
    rw [Success, finish_raw]
    simp
  have preserved := recordResidual_carriers residual fragment before.core _ actual
  exact ⟨preserved, recordResidual_references residual fragment before.core _ references holes actual,
    holes.preserve fragment preserved⟩

end MicroCFTA.SourcePruningEnumerationSelectedEdge
