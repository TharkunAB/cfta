import MicroCFTA.SourcePruningEnumerationSharedPrefixResources
import MicroCFTA.SourcePruningEnumerationSharedPrefixTargetWork

/-!
# Fixed prefix endpoints with exact work and resources

One checkpoint supplies the fixed heap and cache endpoints at every larger fuel.
The stored action can vary. Each observation retains its full PrefixValid proof,
native resource bounds, and exact selected-flag debit.
This result does not choose a common bound for later head or recursive work.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPrefixWork
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationStorageProgress
open InternedConstructorTemplates
open SourcePruningEnumerationSelectedStep SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- The same fixed prefix endpoints retain resources and exact work at every larger fuel. -/
theorem checkpoint_resources_work_stable
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (uv : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ fuel,
      let observed := fun extra => runPrefix holeKey fits admits graph templates stop order metadata
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv caller before memos.query
      ((∃ checked : Cached, ∀ extra,
          observed extra = .parked checked.core (some checked)
            (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata checked checked.core)))) ∨
        (∃ (checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint), ∀ extra,
          observed extra =
            .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
              memos.query (some []) none none none) ∨
        (∃ (checked : Core) (value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
            (after : Cached), value ≠ .empty ∧ ∀ extra, ∃ action : EnumerateM Symbol Constraint Unit,
          observed extra = .narrowed checked (.done (value, some action) heap)
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
            memos.query (some [.ok ((), after.core)]) (some after)
            (some [.ok ((false, metadata), after.core)]) none)) ∧
      ∀ extra,
        PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          formulas solver inventory (fuel + extra) uv caller before memos (observed extra) ∧
        SourcePruningEnumerationSelectedStep.Resources profile property caller (observed extra) ∧
        ∀ (initialBound : Nat) (assignment : Nat → Term Symbol),
          match (generalizing := false) observed extra with
          | .parked _ (some after) _ =>
              pendingSize after.core assignment = pendingSize before.core assignment ∧
              (EnumerationIndexSelection.candidates after).length + 1 =
                (EnumerationIndexSelection.candidates before).length ∧
              SourcePruningEnumerationNativeWork.work initialBound after assignment + 1 =
                SourcePruningEnumerationNativeWork.work initialBound before assignment
          | .narrowed _ _ _ _ _ (some after) _ _ =>
              after.core.counter = before.core.counter ∧
              (∀ other, other ≠ uv → after.expandable other = before.expandable other) ∧
              pendingSize after.core assignment = pendingSize before.core assignment ∧
              (EnumerationIndexSelection.candidates after).length +
                  (if after.expandable uv then 0 else 1) =
                (EnumerationIndexSelection.candidates before).length ∧
              SourcePruningEnumerationNativeWork.work initialBound after assignment +
                  (if after.expandable uv then 0 else 1) =
                SourcePruningEnumerationNativeWork.work initialBound before assignment
          | _ => True := by
  classical
  have picked : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨fuel, branches⟩ := prefix_checkpoint_complete holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory caller memos before
    (order metadata) uv roots packet.context packet.safe packet.pending picked realized paths counts flags
  have valid (extra : Nat) : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata formulas solver inventory (fuel + extra) uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv caller before memos.query) := by
    rcases branches with ⟨checked, stable⟩ | ⟨checked, heap, stable⟩ |
      ⟨checked, value, heap, after, nonempty, stable⟩
    · exact (stable extra).2
    · exact (stable extra).2
    · obtain ⟨action, _actual, correct⟩ := stable extra
      exact correct
  refine ⟨fuel, ?_, ?_⟩
  · rcases branches with ⟨checked, stable⟩ | ⟨checked, heap, stable⟩ |
      ⟨checked, value, heap, after, nonempty, stable⟩
    · exact .inl ⟨checked, fun extra => (stable extra).1⟩
    · exact .inr (.inl ⟨checked, heap, fun extra => (stable extra).1⟩)
    · refine .inr (.inr ⟨checked, value, heap, after, nonempty, ?_⟩)
      intro extra
      obtain ⟨action, actual, _correct⟩ := stable extra
      exact ⟨action, actual⟩
  · intro extra
    refine ⟨valid extra, ?_, ?_⟩
    · exact prefix_resources holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (fuel + extra) uv caller before memos profile property packet.context
        realized bounded known _ (valid extra)
    · intro initialBound assignment
      exact retained_work_target_debit holeKey fits admits graph templates checkEmpty edgesOf stop order
        metadata formulas solver inventory (fuel + extra) uv initialBound assignment caller memos before
        packet chosen _ (valid extra) rfl

end MicroCFTA.SourcePruningEnumerationSharedPrefixWork
