import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges
import MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope
import MicroCFTA.SourceCurrentNativeOptionalChildOrigin
import MicroCFTA.SourceCurrentNativeKeyAdmission
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Fixed-input source scope of actual recursive requests

Initial closed operands supply the source certificate. Actual raw node
prefixes derive the reached request's operand scope and exact binding
membership in that fixed input heap. This result does not identify an
original source-program path.
-/
namespace MicroCFTA.SourceCurrentNativeRequestSourceScope
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeForwardLineage (Forwarded)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial closed inputs derive the fixed-source scope of each actual reached node request. -/
theorem node_prefix (bits : Nat) (before : Checked (bits + 2))
    (good : Good before) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Node) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
        2 ^ (bits + 1))
    {count : Nat} (queried : NodeRequest Symbol Guard) (next : Node → Code Symbol Guard Node)
    {after : Checked (bits + 2)}
    (actual : Steps count (.code (requestNode emptyDomain left right)) before
      (.code (.node queried next)) after) :
    NodeScope before.native.machine.heap queried ∧
      queried.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap := by
  let source := before.native.machine.heap
  let inventory := SourceRecursiveIntersectionSourceInventory.domains source
  let request : NodeRequest Symbol Guard := ⟨emptyDomain,left,right⟩
  have facts := good.native.machine.1
  have resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory before.native.machine.domains :=
    ⟨facts,SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts,good.native.machine.2,nodes,edges,by
      simpa only [inventory,source,SourceRecursiveIntersectionSourceInventory.domains_length] using room⟩
  have current := SourceCurrentAllocatedRecursivePrefixState.initial source inventory before good semantic rfl
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have certificate : SourceCurrentAllocatedRecursivePrefixControl.Certified source inventory
      (.code (requestNode request.domain request.left request.right)) before.native.machine
        (fun final value => Available final.heap value) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine
      ⟨empty_domain _,leftAvailable,rightAvailable⟩ scope (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  exact SourceCurrentAllocatedRecursivePrefixScope.node_scope resources count
    (.code (requestNode request.domain request.left request.right)) before after _ current certificate
    (fun _ => trivial) queried next actual

/-- An actual closed-root optional prefix derives its same owner, child writer and fixed-input scope. -/
theorem optional (bits : Nat) (before siteBefore : Checked (bits + 2))
    (good : Good before) (history : SourceCurrentNativeEdgeWriterGrowth.History before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
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
    let request : NodeRequest Symbol Guard := ⟨emptyDomain,left,right⟩
    ∃ (queryFuel childFuel : Nat) (queried : NodeRequest Symbol Guard)
        (callerNext : Node → Code Symbol Guard Node) (queryBefore : Checked width)
        (handle : Nat) (chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard)
        (first second : Nat),
      let compilerBefore : Checked width := ⟨running, queryBefore.operations⟩
      let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
        queried.domain.key queried.left queried.right first second
      let childBefore : Checked width :=
        {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
      fuel = queryFuel + 2 + childFuel ∧
      Trace queryFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.node queried callerNext)) queryBefore ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.node queried callerNext)) queryBefore ∧
      lookupNode width queried queryBefore.native = (.memoized handle, chosen) ∧
      demandNode handle chosen = (.evaluate queried, running) ∧
      chosen.nodes.cells handle = some ⟨queried, .suspended⟩ ∧
      running.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      running.machine = queryBefore.native.machine ∧
      step (.code (.node queried callerNext)) queryBefore = .yielded
        (.code ((compileNode queried).bind (fun value => .finishNode handle value (callerNext value)))) compilerBefore ∧
      (SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .bothMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .leftMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .rightMu) ∧
      SourceRecursiveIntersectionControl.identity queried.left = some first ∧
      SourceRecursiveIntersectionControl.identity queried.right = some second ∧
      pair = SourceRecursiveIntersectionControl.pair first second ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (compileMu queried.domain queried.left queried.right)) compilerBefore ∧
      step (.code (compileMu queried.domain queried.left queried.right)) compilerBefore =
        .yielded (.code ((requestNode entered.1 (body queried.left) (body queried.right)).bind
          (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
      Trace childFuel (.code (requestNode entered.1 (body queried.left) (body queried.right)))
        childBefore (.code (.pure siteBody)) siteBefore ∧
      (siteNext = fun value => .finishNode handle value (callerNext value)) ∧
      siteBefore.native.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      Forwarded siteBefore ⟨entered.1,body queried.left,body queried.right⟩ childBefore siteBefore siteBody ∧
      NodeScope before.native.machine.heap queried ∧
      queried.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap := by
  let request : NodeRequest Symbol Guard := ⟨emptyDomain,left,right⟩
  have checked := (SourceCurrentNativeKeyAdmission.node_prefix bits before good semantic
    left right leftAvailable rightAvailable leftClosed rightClosed nodes edges room actual).1
  obtain ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,leftId,rightId,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded⟩ :=
    SourceCurrentNativeOptionalChildOrigin.request request fuel before siteBefore
      pair siteBody siteNext good history checked
  have scope := node_prefix bits before good semantic left right leftAvailable rightAvailable
    leftClosed rightClosed nodes edges room queried callerNext earlier.steps
  exact ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,leftId,rightId,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded,scope⟩

end MicroCFTA.SourceCurrentNativeRequestSourceScope
