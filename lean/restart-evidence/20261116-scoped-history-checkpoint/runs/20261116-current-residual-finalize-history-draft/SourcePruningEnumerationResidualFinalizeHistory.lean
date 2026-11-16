import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation

namespace MicroCFTA.SourcePruningEnumerationFinalize
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {NativeGuard : Type}

/-- Residual recording commutes with the same actual raw-slot finalizer. -/
theorem run_after_residual
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (residual : Option Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    run heap fuel target fragment
        (SourcePruningEnumerationSelectedEdge.finish residual fragment before) =
      (run heap fuel target fragment before).map
        (SourcePruningEnumerationSelectedEdge.finish residual fragment)
 := by
  unfold run
  dsimp only [SourcePruningEnumerationSelectedEdge.finish, EnumerationExpandableIndex.frame]
  cases stored : before.core.values[target]? with
  | none => simp only [stored, Option.bind_none, Option.map_none]
  | some old =>
    simp only [stored, Option.bind_some]
    unfold SourcePruningEnumerationNativeIndex.write
    simp only [SourcePruningEnumerationNativeIndex.candidate, Option.bind_some]
    cases counted : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives
        (-1) (EnumerationSchedule.references old) before.waiting with
    | none => simp only [counted, Option.bind_none, Option.map_none]
    | some waiting =>
      cases residual <;>
        simp only [counted, Option.bind_some, SourcePruningEnumerationNativeIndex.count,
          Option.map_some, SourcePruningEnumerationSelectedEdge.finish,
          EnumerationExpandableIndex.frame]

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.EnumerationDischargeHistory
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Recording a residual retains the structural receipt for the same core values. -/
theorem HeldFragmentHistory.after_residual
    (held handle : Nat) (before : EnumerationState.State Symbol Constraint)
    (middle : EnumerationExpandableIndex.Cached Symbol Constraint)
    (residual : Option Constraint) (fragment : Fragments.Fragment Symbol)
    (history : HeldFragmentHistory held handle before middle.core) :
    HeldFragmentHistory held handle before
      (SourcePruningEnumerationSelectedEdge.finish residual fragment middle).core
 := by
  refine ⟨⟨history.isolated.root, history.isolated.stored, history.isolated.incoming⟩,
    ⟨history.protectedHeld.value, history.protectedHeld.root, history.protectedHeld.classes⟩,
    ?_, ?_⟩
  · intro slot old stored
    have protected := history.expanded slot old stored
    exact ⟨protected.value, protected.root, protected.classes⟩
  · intro slot old stored
    exact history.origin slot old stored

end MicroCFTA.EnumerationDischargeHistory
