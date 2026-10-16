import MicroCFTA.SourceCurrentAllocatedGateWorker

namespace MicroCFTA.CurrentAllocatedGateChecks
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open SourceCurrentAllocatedGateWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem same_heap (before : Checked width) :
    advanceHeap before before.native.machine.heap = before := by
  cases before
  rfl

-- Empty classes finish at zero fuel and retain every checked component.
example (values : List (Value Symbol Guard)) (before : Checked width) :
    primary 0 values [] before = .done false before ∧ secondary 0 values [] before = .done false before := by
  simp [primary, secondary, SourceCurrentMuEndpoint.classMeets,
    InternedFreshOrdinaryStatefulGate.anyKnown, lift,
    same_heap]

-- Fuel exhaustion retains the exact primary observation rather than returning a Boolean.
example (name : InternedBinderProtocol.Reference) (before : Checked width) :
    primary 0 [.reference name] [[0]] before =
      .failed (.primary (.done none before.native.machine.heap)) before := by
  simp [primary, SourceCurrentMuEndpoint.classMeets, InternedFreshOrdinaryStatefulGate.anyKnown,
    SourceCurrentMuEndpoint.meets, InternedFreshOrdinaryStatefulGate.child,
    SourceCurrentMuEndpoint.nodeMeets, InternedNestedConstruction.Outcome.bind, lift,
    same_heap]

-- The next fuel amount completes the same selected reference and still retains the full state.
example (name : InternedBinderProtocol.Reference) (before : Checked width) :
    primary 1 [.reference name] [[0]] before = .done true before ∧
      secondary 1 [.reference name] [[0]] before = .done true before := by
  simp [primary, secondary, SourceCurrentMuEndpoint.classMeets, InternedFreshOrdinaryStatefulGate.anyKnown,
    SourceCurrentMuEndpoint.meets, InternedFreshOrdinaryStatefulGate.child,
    SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch,
    InternedNestedConstruction.Outcome.bind, lift,
    same_heap]

-- Pending source work preserves its exact key and returned heap in the secondary fault.
example (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class)
    (before : Checked width) (key : InternedBinderProtocol.NodeKey) (heap : State Symbol Guard)
    (pending : SourceCurrentMuEndpoint.classMeets false source reaches fuel values paths
      before.native.machine.heap = .pending key heap) :
    secondary fuel values paths before = .failed (.secondary (.pending key heap)) (advanceHeap before heap) := by
  simp only [secondary, pending, lift]

-- A supplied primary return retains native tables, domains, and the same equality-operation state.
example {fuel : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : primary fuel values paths before = .done answer after) :
    after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.native.machine.domains = before.native.machine.domains ∧ after.operations = before.operations := by
  rw [(primary_done actual).2]
  exact ⟨rfl, rfl, rfl, rfl⟩

-- Two successful secondary bounds retain the answer and every checked state field.
example {fuel larger : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after later : Checked width} {first second : Bool}
    (one : secondary fuel values paths before = .done first after)
    (two : secondary larger values paths before = .done second later) :
    first = second ∧ after.native = later.native ∧ after.operations = later.operations := by
  obtain ⟨answer, state⟩ := secondary_done_unique one two
  cases state
  exact ⟨answer, rfl, rfl⟩

-- Strict primary endpoint receipts derive coherent returned tables from initial validity.
example {fuel : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : primary fuel values paths before = .done answer after)
    (ready : InternedFreshOrdinaryMemoGateTrace.Ready before.native.machine.heap)
    (available : InternedNestedProvenance.Values before.native.machine.heap values)
    (memos : EndpointMemoGateTrace.Memos)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths
        before.native.machine.heap answer after.native.machine.heap,
      ∃ saved, SourceCurrentAllocatedPrimaryReads.ClassReads trace memos saved ∧
        EndpointMemoGateTrace.Valid after.native.machine.heap saved := by
  obtain ⟨trace, saved, reads, kept⟩ := primary_reads actual ready available memos valid
  exact ⟨trace, saved, reads, kept.valid⟩

-- Initial resident values derive a finite current secondary result, then its actual trace.
example (values : List (Value Symbol Guard)) (paths : Class) (before : Checked width)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
    (available : InternedNestedProvenance.Values before.native.machine.heap values) :
    ∃ fuel answer after, secondary fuel values paths before = .done answer after ∧
      SourceCurrentSecondaryTrace.ClassTrace source values paths before.native.machine.heap
        answer after.native.machine.heap := by
  obtain ⟨answer, after, fuel, stable⟩ := secondary_finite values paths before semantic costs available
  have actual := stable fuel (Nat.le_refl _)
  exact ⟨fuel, answer, after, actual, secondary_graph actual⟩

end MicroCFTA.CurrentAllocatedGateChecks
