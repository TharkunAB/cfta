import MicroCFTA.SourceEqualitySharedTargetState

/-!
# First force and reuse of a shared class target

A cache hit returns the stored physical value without any request. A miss
runs the actual demanded target graph and stores its returned value. Both
branches retain original capture scope and all older returned target slots.
-/
namespace MicroCFTA.SourceEqualitySharedTargetForce
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityDemandTarget SourceEqualityClassTarget
open SourceEqualitySharedTargetState

/-- Returned shared target slots retain their exact earlier physical values. -/
def Retains (before after : State width Symbol Guard) : Prop :=
  ∀ path value, before.targets path = some value → after.targets path = some value

/-- Adjacent shared-target prefixes compose their returned-slot histories. -/
theorem Retains.trans {before middle after : State width Symbol Guard} (first : Retains before middle) (second : Retains middle after) : Retains before after :=
  fun path value present => second path value (first path value present)

/-- One path closure either reuses its returned value or constructs it once at first force. -/
inductive Force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) :
    State width Symbol Guard → Value Symbol Guard → State width Symbol Guard → Prop where
  | hit (present : before.targets path = some value) : Force emptyGuard conjoin clear top record values path before value before
  | miss (absent : before.targets path = none)
      (actual : Target emptyGuard conjoin clear top values (operandPaths record.paths path) before.native value native) :
      Force emptyGuard conjoin clear top record values path before value (store before path value native)

/-- First forcing and reuse derive actual closed target availability and complete retained shared state. -/
theorem Force.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values) (closed : ClosedValues values) (member : path ∈ record.paths) :
    Ready emptyGuard conjoin clear top record values base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧ after.targets path = some value ∧ Retains before after := by
  cases trace with
  | hit present =>
      have available := (ready.receipts path value present).available closed
      exact ⟨ready, pure_keeps _ ready.native.semantic.ready, available.1, available.2, present, fun _ _ stored => stored⟩
  | miss absent actual =>
      have available : Values before.native.machine.heap values := fun value member => ready.captured.available value (known value member)
      have checked := actual.effects ready.native available closed
      refine ⟨ready.store known closed path member value _ actual, checked.2.1, checked.2.2.1, checked.2.2.2, ?_, ?_⟩
      · simp only [SourceEqualitySharedTargetState.store, Cache.put, ite_true]
      · intro other target present
        by_cases same : other = path
        · subst other; rw [absent] at present; cases present
        · simpa only [SourceEqualitySharedTargetState.store, Cache.put, same, ite_false] using present

/-- Native and constructor advances retain every returned target slot verbatim. -/
theorem advance_retains (before : State width Symbol Guard) (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retains before (advance before native) := fun _ _ present => present

/-- Only a first force requires native target word checks; a returned slot requires none. -/
def ForceRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) (before : State width Symbol Guard) : Prop :=
  match before.targets path with
  | some _ => True
  | none => SourceEqualityDemandTargetComplete.TargetRanges emptyGuard conjoin clear top values (operandPaths record.paths path) before.native

/-- Closed captured forests and actual first-demand word checks derive a complete shared target force. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
    (known : Values base values) (closed : ClosedValues values) (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (before : State width Symbol Guard) (ready : Ready emptyGuard conjoin clear top record values base before)
    (ranges : ForceRanges emptyGuard conjoin clear top record values path before) :
    ∃ value after, Force emptyGuard conjoin clear top record values path before value after ∧
      Ready emptyGuard conjoin clear top record values base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧ after.targets path = some value ∧ Retains before after := by
  cases present : before.targets path with
  | some value =>
      have trace : Force emptyGuard conjoin clear top record values path before value before := .hit present
      exact ⟨value, before, trace, trace.effects ready known closed member⟩
  | none =>
      have actualRanges := ranges
      simp only [ForceRanges, present] at actualRanges
      obtain ⟨value, native, actual, _⟩ := SourceEqualityDemandTargetComplete.complete emptyGuard conjoin clear top values
        (operandPaths record.paths path) before.native ready.native actualRanges (fun value member => ready.captured.available value (known value member)) closed
      have trace : Force emptyGuard conjoin clear top record values path before value (store before path value native) := .miss present actual
      exact ⟨value, _, trace, trace.effects ready known closed member⟩

end MicroCFTA.SourceEqualitySharedTargetForce
