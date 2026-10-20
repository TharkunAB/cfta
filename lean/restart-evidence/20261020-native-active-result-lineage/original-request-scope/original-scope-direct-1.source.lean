import MicroCFTA.SourceCurrentNativeRequestSourceScope
import MicroCFTA.SourceCurrentCompletedBuildRootedWriters

/-!
# Original source execution writers at an actual optional site

The source build returns the exact native entry heap. Every reached
queried Mu operand and named binding retains a rooted writer from that
same source execution. Generated results are separate from these inputs.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalRequestScope
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentCompletedBuildRootedWriters (Written)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The same queried operands and domain names retain full original source execution writers. -/
def RootedScope (original : Syntax Symbol Guard) (source : Heap)
    (queried : NodeRequest Symbol Guard) : Prop :=
  (∀ (entry : Interned NodeKey) (body depth ordinary : Node),
    queried.left = .mu entry body depth ordinary →
      Written original [] empty source entry.key (.mu entry body depth ordinary)) ∧
  (∀ (entry : Interned NodeKey) (body depth ordinary : Node),
    queried.right = .mu entry body depth ordinary →
      Written original [] empty source entry.key (.mu entry body depth ordinary)) ∧
  (∀ name ∈ SourceRecursiveIntersectionDomain.names queried.domain.key,
    ∃ (entry : Interned NodeKey) (body depth ordinary : Node),
      SourcePreparedSharedRows.read source name = some (.mu entry body depth ordinary) ∧
      Written original [] empty source entry.key (.mu entry body depth ordinary))

private theorem available_writer (original : Syntax Symbol Guard) (result : Node) (source : Heap)
    (built : build original [] empty = .done result source)
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (available : Available source (.mu entry body depth ordinary)) :
    Written original [] empty source entry.key (.mu entry body depth ordinary) := by
  apply SourceCurrentCompletedBuildRootedWriters.build_writer original [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context ?_ result source built
    entry.key entry body depth ordinary (available.resident entry rfl)
  intro key chosen storedBody storedDepth storedOrdinary impossible
  cases impossible

private theorem scope_rooted (original : Syntax Symbol Guard) (result : Node) (source : Heap)
    (built : build original [] empty = .done result source)
    (facts : InternedNestedFacts.Facts source) (queried : NodeRequest Symbol Guard)
    (scope : NodeScope source queried) : RootedScope original source queried := by
  refine ⟨?_,?_,?_⟩
  · intro entry body depth ordinary same
    apply available_writer original result source built entry body depth ordinary
    exact same ▸ scope.leftAvailable
  · intro entry body depth ordinary same
    apply available_writer original result source built entry body depth ordinary
    exact same ▸ scope.rightAvailable
  · intro name member
    obtain ⟨value,originalValue,available,complete⟩ := scope.bindings name member
    cases originalValue <;>
      simp only [Value.referenceOf,IntersectionFlatMemoKey.input,Option.some.injEq,reduceCtorEq] at complete <;>
      try contradiction
    case mu entry body depth ordinary originalBody =>
      cases complete
      exact ⟨entry,body,depth,ordinary,
        SourcePreparedSharedRows.read_identity source facts _ available entry.identity rfl,
        available_writer original result source built entry body depth ordinary available⟩

variable [DecidableEq Symbol]

/-- The actual source build attaches writers to the same optional owner's queried input scope. -/
theorem optional (original : Syntax Symbol Guard) (root : Node)
    (bits : Nat) (before siteBefore : Checked (bits + 2))
    (built : build original [] empty = .done root before.native.machine.heap)
    (good : Good before) (history : SourceCurrentNativeEdgeWriterGrowth.History before)
    (left right : Node) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
        2 ^ (bits + 1))
    (fuel : Nat) (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (actual : Steps fuel (.code (requestNode emptyDomain left right)) before
      (.code (.optionalBinder pair siteBody siteNext)) siteBefore) :
    SourceCurrentNativeOptionalChildOrigin.Origin ⟨emptyDomain,left,right⟩ fuel before siteBefore pair siteBody siteNext ∧
      ∀ (queryFuel : Nat) (queried : NodeRequest Symbol Guard)
        (callerNext : Node → Code Symbol Guard Node) (queryBefore : Checked (bits + 2)),
        Trace queryFuel (.code (requestNode emptyDomain left right)) before
          (.code (.node queried callerNext)) queryBefore →
        NodeScope before.native.machine.heap queried ∧
          queried.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap ∧
          RootedScope original before.native.machine.heap queried := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed original root before.native.machine.heap built
  obtain ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,leftId,rightId,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded,_scope,_member⟩ :=
    SourceCurrentNativeRequestSourceScope.optional bits before siteBefore good history semantic
      left right leftAvailable rightAvailable leftClosed rightClosed nodes edges room fuel pair siteBody siteNext actual
  refine ⟨?_,?_⟩
  · exact ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
      first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
      queryStep,recursive,leftId,rightId,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded⟩
  · intro count current next entry prefix
    obtain ⟨scope,member⟩ := SourceCurrentNativeRequestSourceScope.node_prefix bits before good semantic
      left right leftAvailable rightAvailable leftClosed rightClosed nodes edges room current next prefix.steps
    exact ⟨scope,member,scope_rooted original root before.native.machine.heap built good.native.machine.1 current scope⟩

end MicroCFTA.SourceCurrentNativeOriginalRequestScope
