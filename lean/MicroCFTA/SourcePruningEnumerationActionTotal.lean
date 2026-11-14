import MicroCFTA.SourcePruningEnumerationAction
import MicroCFTA.EnumerationCompressionFrame

namespace MicroCFTA.SourcePruningEnumerationActionTotal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint

attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem setterRepresentatives (slot : Nat) (content : UVarValue Symbol)
    (input output : EnumerationState.State Symbol Constraint)
    (stored : Success (setValue slot content) input () output) :
    output.representatives = input.representatives := by
  dsimp only [Success, setValue, modify, instMonadStateOfMonadStateOf,
    MonadState.modifyGet, instMonadStateOfStateTOfMonad, MonadStateOf.modifyGet,
    StateT.modifyGet, Pure.pure, Applicative.toPure, Monad.toApplicative,
    ExceptT.instMonad, ExceptT.pure, ExceptT.run, ExceptT.mk,
    EnumerationState.instMonadList_microCFTA, Membership.mem, List.instMembership] at stored
  cases stored with
  | head => rfl
  | tail _ rest => nomatch rest

variable {Typing Key : Type}
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (metadata : SourcePruningRecordTypes.Metadata Typing)

/-- Every successful prepared action preserves total representatives. -/
theorem prepare_total (nativeFuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (oldValue value : Node)
    (heap afterHeap : InternedConstructorTemplates.State Symbol Constraint)
    (operation : EnumerateM Symbol Constraint Unit)
    (input output : EnumerationState.State Symbol Constraint)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue heap = .done (value, some operation) afterHeap)
    (total : UnionFind.Total input.representatives) (successful : Success operation input () output) :
    UnionFind.Total output.representatives := by
  dsimp only [SourcePruningEnumerationAction.prepare, SourcePruningEnumerationAction.prepareWithNarrow] at prepared
  all_goals try (split at prepared)
  all_goals try (split at prepared)
  all_goals try (split at prepared)
  all_goals try (split at prepared)
  all_goals cases prepared
  all_goals first
  | solve
    | dsimp only [Success, reject, ExceptT.run, ExceptT.mk,
        Membership.mem, List.instMembership] at successful
      cases successful
  | exact (pure_frame _ _ _ _ successful).total total
  | have preserved := setterRepresentatives _ _ input output successful
    rw [preserved]
    exact total
  | obtain ⟨selected, intermediate, represented, stored⟩ :=
      (MicroCFTA.EnumerationCorrectness.success_bind
        (MicroCFTA.EnumerationState.representative representativeFuel uv) _ input () output).mp successful
    have frame := representative_frame representativeFuel uv selected input intermediate total represented
    have preserved := setterRepresentatives _ _ intermediate output stored
    rw [preserved]
    exact frame.total total

end MicroCFTA.SourcePruningEnumerationActionTotal
