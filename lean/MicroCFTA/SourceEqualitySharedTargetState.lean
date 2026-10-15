import MicroCFTA.SourceEqualityClassTargetAPI

/-!
# Class-local shared target state and actual construction receipts

The class input forest stays captured at its original cache. A target slot
contains only a returned physical value. Its invariant retains the literal
construction receipt and cache history. Empty slots require no construction.
-/
namespace MicroCFTA.SourceEqualitySharedTargetState
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityDemandTarget SourceEqualityClassTarget

/-- A class-local state retains the full native state and the returned value of each forced path closure. -/
structure State (width : Nat) (Symbol Guard : Type) where
  native : SourceRecursiveIntersectionThunks.State width Symbol Guard
  targets : EqualityNormalize.Path → Option (Value Symbol Guard)

/-- Capture fresh class closures without constructing any target. -/
def initial (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) : State width Symbol Guard := ⟨native, fun _ => none⟩

/-- A constructor or native prefix advances the actual native state and retains all returned target slots. -/
def advance (state : State width Symbol Guard) (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) : State width Symbol Guard :=
  {state with native := native}

/-- A constructor-only prefix advances its actual heap and retains domain, native memos, and returned target slots. -/
def advanceHeap (state : State width Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard) : State width Symbol Guard :=
  advance state (SourceEqualityNativeScoped.advanceHeap state.native heap)

/-- One completed demand stores its returned target in the same class-local closure slot. -/
def store (state : State width Symbol Guard) (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) : State width Symbol Guard :=
  ⟨native, Cache.put state.targets path value⟩

/-- An actual target receipt retains its earlier full states and history into the present constructor cache. -/
def Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (heap : InternedConstructorTemplates.State Symbol Guard) (path : EqualityNormalize.Path) (value : Value Symbol Guard) : Prop :=
  path ∈ record.paths ∧ ∃ before after : SourceRecursiveIntersectionThunks.State width Symbol Guard,
    IdleReady emptyGuard conjoin before ∧ Values before.machine.heap values ∧
      Target emptyGuard conjoin clear top values (operandPaths record.paths path) before value after ∧ Keeps after.machine.heap heap

/-- A shared target state retains original capture scope and actual receipts for every returned slot. -/
structure Ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (state : State width Symbol Guard) : Prop where
  native : IdleReady emptyGuard conjoin state.native
  captured : Keeps base state.native.machine.heap
  receipts : ∀ path value, state.targets path = some value → Receipt width emptyGuard conjoin clear top record values state.native.machine.heap path value

/-- An empty class-local closure table needs no target receipt. -/
theorem initial_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : IdleReady emptyGuard conjoin native) (captured : Keeps base native.machine.heap) :
    Ready emptyGuard conjoin clear top record values base (initial native) :=
  ⟨ready, captured, by intro path value absent; cases absent⟩

/-- Later actual cache growth retains the same target construction receipt. -/
theorem Receipt.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {before after : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : Receipt width emptyGuard conjoin clear top record values before path value) (keeps : Keeps before after) :
    Receipt width emptyGuard conjoin clear top record values after path value := by
  obtain ⟨member, first, final, ready, available, trace, retained⟩ := receipt
  exact ⟨member, first, final, ready, available, trace, retained.trans keeps⟩

/-- Actual target construction derives closed physical availability in the present cache. -/
theorem Receipt.available [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {heap : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : Receipt width emptyGuard conjoin clear top record values heap path value) (closed : ClosedValues values) :
    Available heap value ∧ value.free = [] := by
  obtain ⟨_, first, final, ready, available, trace, retained⟩ := receipt
  have checked := trace.effects ready available closed
  exact ⟨retained.available value checked.2.2.1, checked.2.2.2⟩

/-- Literal native or constructor prefixes retain every stored target and all source capture premises. -/
theorem Ready.advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {before : State width Symbol Guard} (ready : Ready emptyGuard conjoin clear top record values base before)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) (nextReady : IdleReady emptyGuard conjoin native)
    (keeps : Keeps before.native.machine.heap native.machine.heap) : Ready emptyGuard conjoin clear top record values base (advance before native) :=
  ⟨nextReady, ready.captured.trans keeps, fun path value present => (ready.receipts path value present).grows keeps⟩

/-- A literal constructor heap change retains original scope and every stored target receipt. -/
theorem Ready.heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {before : State width Symbol Guard} (ready : Ready emptyGuard conjoin clear top record values base before)
    (heap : InternedConstructorTemplates.State Symbol Guard) (keeps : Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap) :
    Ready emptyGuard conjoin clear top record values base (advanceHeap before heap) :=
  ready.advance _ (ready.native.advance heap keeps semantic) keeps

/-- First forcing stores only its actual completed target and preserves all older receipt histories. -/
theorem Ready.store [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {before : State width Symbol Guard} (ready : Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (closed : ClosedValues values) (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (value : Value Symbol Guard) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Target emptyGuard conjoin clear top values (operandPaths record.paths path) before.native value after) :
    Ready emptyGuard conjoin clear top record values base (store before path value after) := by
  have available : Values before.native.machine.heap values := fun value member => ready.captured.available value (known value member)
  have checked := trace.effects ready.native available closed
  refine ⟨checked.1, ready.captured.trans checked.2.1, ?_⟩
  intro other target present
  by_cases same : other = path
  · subst other
    have equal : value = target := by simpa only [SourceEqualitySharedTargetState.store, Cache.put, ite_true, Option.some.injEq] using present
    subst target
    exact ⟨member, before.native, after, ready.native, available, trace, pure_keeps _ checked.1.semantic.ready⟩
  · have original : before.targets other = some target := by simpa only [SourceEqualitySharedTargetState.store, Cache.put, same, ite_false] using present
    exact (ready.receipts other target original).grows checked.2.1

end MicroCFTA.SourceEqualitySharedTargetState
