import MicroCFTA.SourceCurrentMemoDemandTarget
import MicroCFTA.SourceCurrentTargetPathComplete

/-!
# Shared returned targets with the actual completed merge table

Each returned slot retains its actual target construction and initial
physical premises. Later heap growth retains that receipt. Later completed
merge entries retain its original result table. Language coverage remains
a separate invariant of the current completed merge table.
-/
namespace MicroCFTA.SourceCurrentMemoSharedTargetState
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceEqualityClassTarget SourceCurrentMemoDemandTarget
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Heap" => InternedConstructorTemplates.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Class-local slots and the completed merge table retain the same full native state. -/
structure State (width : Nat) (Symbol Guard : Type) where
  native : Native width Symbol Guard
  targets : EqualityNormalize.Path → Option (Value Symbol Guard)
  memo : Memo Symbol Guard

def initial (native : Native width Symbol Guard) (memo : Memo Symbol Guard) : State width Symbol Guard :=
  ⟨native, fun _ => none, memo⟩

def advance (state : State width Symbol Guard) (native : Native width Symbol Guard) : State width Symbol Guard :=
  {state with native := native}

def advanceHeap (state : State width Symbol Guard) (heap : Heap Symbol Guard) : State width Symbol Guard :=
  advance state (SourceEqualityNativeScoped.advanceHeap state.native heap)

def store (state : State width Symbol Guard) (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (native : Native width Symbol Guard) (memo : Memo Symbol Guard) : State width Symbol Guard :=
  ⟨native, put state.targets path value, memo⟩

/-- A returned slot retains a literal earlier target and both of its actual cache scopes. -/
def Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (heap : Heap Symbol Guard) (memo : Memo Symbol Guard) (path : EqualityNormalize.Path) (value : Value Symbol Guard) : Prop :=
  path ∈ record.paths ∧ ∃ (before after : Native width Symbol Guard) (initial saved : Memo Symbol Guard),
    IdleReady emptyGuard conjoin before ∧ CostHeap before.machine.heap ∧ Stored before.machine.heap initial ∧
      Values before.machine.heap values ∧ (∀ own ∈ operandPaths record.paths path, ForestClosed own values) ∧
      Target emptyGuard conjoin clear top values (operandPaths record.paths path) before initial value after saved ∧
      Keeps after.machine.heap heap ∧ Extends saved memo

/-- Physical readiness derives every returned target from its retained actual receipt. -/
structure Ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : Heap Symbol Guard) (state : State width Symbol Guard) : Prop where
  native : IdleReady emptyGuard conjoin state.native
  captured : Keeps base state.native.machine.heap
  costs : CostHeap state.native.machine.heap
  stored : Stored state.native.machine.heap state.memo
  receipts : ∀ path value, state.targets path = some value →
    Receipt width emptyGuard conjoin clear top record values state.native.machine.heap state.memo path value

theorem initial_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (base : Heap Symbol Guard)
    (native : Native width Symbol Guard) (memo : Memo Symbol Guard) (ready : IdleReady emptyGuard conjoin native)
    (captured : Keeps base native.machine.heap) (costs : CostHeap native.machine.heap) (stored : Stored native.machine.heap memo) :
    Ready emptyGuard conjoin clear top record values base (initial native memo) :=
  ⟨ready, captured, costs, stored, by intro path value absent; cases absent⟩

theorem Receipt.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {before after : Heap Symbol Guard}
    {memo saved : Memo Symbol Guard} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : Receipt width emptyGuard conjoin clear top record values before memo path value)
    (keeps : Keeps before after) (retained : Extends memo saved) :
    Receipt width emptyGuard conjoin clear top record values after saved path value := by
  obtain ⟨member, first, final, initial, completed, ready, costs, stored, available, domains, trace, growth, entries⟩ := receipt
  exact ⟨member, first, final, initial, completed, ready, costs, stored, available, domains, trace,
    growth.trans keeps, extends_trans entries retained⟩

/-- The historical graph derives closed availability without a new domain premise. -/
theorem Receipt.available [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {heap : Heap Symbol Guard}
    {memo : Memo Symbol Guard} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : Receipt width emptyGuard conjoin clear top record values heap memo path value) :
    Available heap value ∧ value.free = [] := by
  obtain ⟨_, first, final, initial, completed, ready, costs, stored, available, domains, trace, growth, _⟩ := receipt
  have checked := trace.effects ready costs stored available domains
  exact ⟨growth.available value checked.available, checked.closed⟩

/-- Current coverage restricts to every initial table retained by a historical target. -/
theorem Receipt.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {heap : Heap Symbol Guard}
    {memo : Memo Symbol Guard} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : Receipt width emptyGuard conjoin clear top record values heap memo path value)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (covered : CacheCovers holds ambient memo)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms) (satisfied : EqualityNormalize.ClassSat (.node symbol terms) record.paths)
    (selected : (Term.node symbol terms).atPath path = some part) : meaning holds ambient value part := by
  obtain ⟨member, first, final, initial, completed, ready, costs, stored, available, domains, trace, _, entries⟩ := receipt
  have effects := trace.effects ready costs stored available domains
  have initialCovered : CacheCovers holds ambient initial := fun key entry found => covered key entry (entries _ _ (effects.retained _ _ found))
  have inclusion := (trace.included ready costs stored holds ambient initialCovered available domains clearTrue topTrue conjoined).2
  apply inclusion (operandPaths_nonempty record.paths active path) (operandPaths_nonroot record coherent active path)
    symbol terms part accepted
  intro other included
  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp included
  obtain ⟨common, selectedAt, otherAt⟩ := EqualityNormalize.class_pair_equal (.node symbol terms) record.paths active satisfied
    path original member (List.mem_filter.mp originalIn).1
  have samePart := Option.some.inj (selectedAt.symm.trans selected)
  subst common
  simpa only [SourceEqualitySelectedRequired.lookup_natural] using otherAt

theorem Ready.advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap Symbol Guard}
    {before : State width Symbol Guard} (ready : Ready emptyGuard conjoin clear top record values base before)
    (native : Native width Symbol Guard) (nextReady : IdleReady emptyGuard conjoin native)
    (keeps : Keeps before.native.machine.heap native.machine.heap) (costs : CostHeap native.machine.heap) :
    Ready emptyGuard conjoin clear top record values base (advance before native) :=
  ⟨nextReady, ready.captured.trans keeps, costs, ready.stored.grows keeps,
    fun path value present => (ready.receipts path value present).grows keeps (extends_refl _)⟩

theorem Ready.heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap Symbol Guard}
    {before : State width Symbol Guard} (ready : Ready emptyGuard conjoin clear top record values base before)
    (heap : Heap Symbol Guard) (keeps : Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap) (costs : CostHeap heap) :
    Ready emptyGuard conjoin clear top record values base (advanceHeap before heap) :=
  ready.advance _ (ready.native.advance heap keeps semantic) keeps costs

/-- First forcing derives new receipts and retains all earlier target and merge entries. -/
theorem Ready.store [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap Symbol Guard}
    {before : State width Symbol Guard} (ready : Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (value : Value Symbol Guard)
    (native : Native width Symbol Guard) (saved : Memo Symbol Guard)
    (trace : Target emptyGuard conjoin clear top values (operandPaths record.paths path) before.native before.memo value native saved) :
    Ready emptyGuard conjoin clear top record values base (store before path value native saved) := by
  have available : Values before.native.machine.heap values := fun value member => ready.captured.available value (known value member)
  have selectedDomains := SourceCurrentTargetPathComplete.operand_domains record values domains path
  have checked := trace.effects ready.native ready.costs ready.stored available selectedDomains
  refine ⟨checked.ready, ready.captured.trans checked.keeps, checked.costs, checked.stored, ?_⟩
  intro other target present
  by_cases same : other = path
  · subst other
    have equal : value = target := by simpa only [SourceCurrentMemoSharedTargetState.store, put, ite_true, Option.some.injEq] using present
    subst target
    exact ⟨member, before.native, native, before.memo, saved, ready.native, ready.costs, ready.stored, available, selectedDomains,
      trace, pure_keeps _ checked.ready.semantic.ready, extends_refl _⟩
  · have original : before.targets other = some target := by simpa only [SourceCurrentMemoSharedTargetState.store, put, same, ite_false] using present
    exact (ready.receipts other target original).grows checked.keeps checked.retained

end MicroCFTA.SourceCurrentMemoSharedTargetState
