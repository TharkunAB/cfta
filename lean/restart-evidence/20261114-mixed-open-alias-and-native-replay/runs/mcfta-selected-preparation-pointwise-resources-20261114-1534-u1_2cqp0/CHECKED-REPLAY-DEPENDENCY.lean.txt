import MicroCFTA.EnumerationExecution
import MicroCFTA.EnumerationPartialExact
import MicroCFTA.SourcePruningEnumerationSelectedPreparation
import MicroCFTA.SourcePruningEnumerationSelectedValueReplay

/-!
# Exact replay of successful selected preparation

Successful entry retains both exact representative reads and the ancestry write.
Successful native preparation retains its exact returned value and heap.
The common preparation therefore returns the same complete observation at larger bounds.
-/
namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] EnumerationObservations.partialTransportMonadList

/-- A successful entry retains its complete raw observation at every larger bound. -/
theorem enter_success_raw_moreFuel
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel extra uv : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (result : Nat × Nat × List Suspended × InternedConstructorTemplates.Value Symbol NativeGuard)
    (observed : Success (enter heap fuel uv) before result after) :
    ExceptT.run (enter heap (fuel + extra) uv before) =
      ExceptT.run (enter heap fuel uv before) := by
  unfold enter at observed
  obtain ⟨readValue, readAfter, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
  have oldRead := EnumerationPartialExact.getValue_exact fuel uv before readAfter readValue reading
  have newRead := EnumerationPartialExact.getValue_exact (fuel + extra) uv before readAfter readValue
    (EnumerationExecution.getValue_moreFuel fuel extra uv before readValue readAfter reading)
  unfold enter
  rw [bind_single _ _ before readAfter readValue newRead,
    bind_single _ _ before readAfter readValue oldRead]
  cases readValue with
  | eliminated => rfl
  | enumerated _fragment => rfl
  | unenumerated node _bucket =>
      cases node with
      | none => rfl
      | some _handle =>
          obtain ⟨target, compressed, resolving, _finished⟩ := (success_bind _ _ _ _ _).mp continued
          have oldResolve := EnumerationPartialExact.representative_success_exact
            fuel uv readAfter compressed target resolving
          have newResolve := EnumerationPartialExact.representative_success_exact
            (fuel + extra) uv readAfter compressed target
            (EnumerationExecution.representative_moreFuel fuel extra uv readAfter target compressed resolving)
          dsimp only
          rw [bind_single _ _ readAfter compressed target newResolve,
            bind_single _ _ readAfter compressed target oldResolve]

end MicroCFTA.SourcePruningEnumerationEntry

namespace MicroCFTA.SourcePruningEnumerationSelectedPreparation
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A successful common preparation retains its full entry row, native result, and returned heap. -/
theorem successful_run_moreFuel
    (fuel extra uv target handle : Nat) (scs : List Suspended) (decoded value : Node)
    (caller : Caller width) (before : Cached) (entered : Core)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (observed : SourcePruningEnumerationSelectedPreparation.run fuel fuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap))) :
    SourcePruningEnumerationSelectedPreparation.run (fuel + extra) (fuel + extra) uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)) := by
  have entryExact := congrArg Prod.fst observed
  change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
    fuel uv before.core) = [.ok ((target, handle, scs, decoded), entered)] at entryExact
  have entrySuccess : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      fuel uv) before.core (target, handle, scs, decoded) entered := by
    rw [Success, entryExact]
    exact List.mem_singleton_self _
  have laterEntry := (SourcePruningEnumerationEntry.enter_success_raw_moreFuel
    caller.checked.native.machine.heap fuel extra uv before.core entered
    (target, handle, scs, decoded) entrySuccess).trans entryExact
  have nativeExact : SourcePruningEnumerationSelectedValue.run fuel decoded
      caller.checked.native.machine.heap = .done value heap := by
    have nativeObserved := congrArg Prod.snd observed
    simpa only [run, entryExact, Option.some.injEq] using nativeObserved
  have laterNative := SourcePruningEnumerationSelectedValue.run_done_moreFuel fuel extra decoded value
    caller.checked.native.machine.heap heap nativeExact
  simp only [run, laterEntry, laterNative]

end MicroCFTA.SourcePruningEnumerationSelectedPreparation
