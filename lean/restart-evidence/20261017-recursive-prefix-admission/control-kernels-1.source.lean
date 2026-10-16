import MicroCFTA.SourceCurrentAllocatedRecursivePrefixControl
set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.RecursivePrefixControlKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedRecursivePrefixControl
open IntersectionFlatMemoKeyDomain
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

open scoped Classical in
/-- Original source records and past domain allocation derive the current physical demand check. -/
theorem current_node
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (inventory : List DomainKey) (initial : Cache.State DomainKey) (before : State (bits + 2))
    (current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory initial before)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (member : request.domain.key ∈ inventory) (ready : NodeReady before.native.machine request)
    (valid : Cache.Valid initial) (nodes : source.nodes.next < 2 ^ bits)
    (edges : source.edges.next ≤ 2 ^ (bits + 2)) (room : initial.next + inventory.length < 2 ^ (bits + 1)) :
    SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2) (.code (requestNode request.domain request.left request.right)) ∧
    SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (requestNode request.domain request.left request.right)) before ∧
    SourceCurrentAllocatedNativeDomainTrace.Entered inventory (.code (requestNode request.domain request.left request.right)) := by
  have local := SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine ready scope member
  exact ⟨words source inventory bits facts initial _ before _ current local valid nodes edges room,
    inputs source inventory bits facts initial _ before _ current local valid nodes edges room,
    entered source inventory _ before.native.machine _ local⟩

open scoped Classical in
/-- A literal checked body yield retains the current state facts and its emitted certificate. -/
theorem body_yield {width : Nat}
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (inventory : List DomainKey) (initial : Cache.State DomainKey) (before after : State width)
    (current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory initial before)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (member : request.domain.key ∈ inventory) (ready : EdgeReady before.native.machine request)
    (body : Code Symbol Guard (EdgeValue Symbol Guard))
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code body) after) :
    SourceCurrentAllocatedRecursivePrefixState.Current source inventory initial after ∧
    Extension before.native.machine after.native.machine ∧
    SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
    SourceCurrentAllocatedNativeFieldClosure.Fields (.code body) after ∧
    Certified source inventory (.code body) after.native.machine (fun final value => EdgeResident final.heap value) := by
  have certificate := edge_body source inventory request before.native.machine scope member ready
  have fields : SourceCurrentAllocatedNativeFieldClosure.Fields (.edgeBody request .pure) before :=
    ⟨ready, fun _ => trivial⟩
  have retained := SourceCurrentAllocatedRecursivePrefixState.yielded (.edgeBody request .pure) (.code body)
    before after current (by trivial) (entered source inventory _ before.native.machine _ certificate) fields yielded
  exact ⟨retained.1, retained.2.1, retained.2.2.2.1, retained.2.2.2.2,
    body_code source inventory facts request before after body current.good.native.machine current.semantic certificate yielded⟩

open scoped Classical in
/-- Actual grown-heap binder readback yields a fully checked original request at the same state. -/
theorem read_to_current_node
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (inventory : List DomainKey) (initial : Cache.State DomainKey) (before : State (bits + 2))
    (current : SourceCurrentAllocatedRecursivePrefixState.Current source inventory initial before)
    (domain : Interned DomainKey) (bindings : OriginalBindings source domain.key)
    (name : Nat) (present : name ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (other : Value Symbol Guard) (original : Original other) (available : Available source other)
    (member : domain.key ∈ inventory) (known : Domain before.native.machine domain)
    (valid : Cache.Valid initial) (nodes : source.nodes.next < 2 ^ bits)
    (edges : source.edges.next ≤ 2 ^ (bits + 2)) (room : initial.next + inventory.length < 2 ^ (bits + 1)) :
    ∃ bound, SourcePreparedSharedRows.read before.native.machine.heap name = some bound ∧
      NodeScope source ⟨domain, bound, other⟩ ∧
      SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2) (.code (requestNode domain bound other)) ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (requestNode domain bound other)) before := by
  obtain ⟨bound, found, boundOriginal, boundAvailable, _⟩ := bindings.read source before.native.machine.heap
    current.good.native.machine.1 current.growth current.history domain.key name present
  have scope : NodeScope source ⟨domain, bound, other⟩ :=
    ⟨boundOriginal, original, boundAvailable, available, bindings⟩
  have ready : NodeReady before.native.machine ⟨domain, bound, other⟩ :=
    ⟨known, boundAvailable.grows source _ current.growth current.history,
      available.grows source _ current.growth current.history⟩
  have checked := current_node bits source facts inventory initial before current ⟨domain, bound, other⟩
    scope member ready valid nodes edges room
  exact ⟨bound, found, scope, checked.1, checked.2.1⟩

#print axioms current_node
#check @current_node
#print axioms body_yield
#check @body_yield
#print axioms read_to_current_node
#check @read_to_current_node
end MicroCFTA.RecursivePrefixControlKernels
