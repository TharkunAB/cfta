import MicroCFTA.SourceCurrentNativeActiveQueryForwarding
import MicroCFTA.SourceCurrentNativeOptionalChildOrigin
import MicroCFTA.SourceCurrentNativePrefixWriterMaps

/-!
# The same optional child reaches its actual terminal writer

The actual optional prefix recovers one queried owner and entered child.
Its same nonempty child result follows actual swap and reset bodies to a
terminal returned writer at that same optional state.
-/
namespace MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin
open Cache InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeForwardLineage (Forwarded)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One correlated owner tuple retains its same entered child's actual terminal writer. -/
def Origin (request : NodeRequest Symbol Guard) (fuel : Nat) (before siteBefore : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node) : Prop :=
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
      Inputs (.code (.node queried callerNext)) queryBefore ∧
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
      Inputs (.code (compileMu queried.domain queried.left queried.right)) compilerBefore ∧
      step (.code (compileMu queried.domain queried.left queried.right)) compilerBefore =
        .yielded (.code ((requestNode entered.1 (body queried.left) (body queried.right)).bind
          (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
      Trace childFuel (.code (requestNode entered.1 (body queried.left) (body queried.right)))
        childBefore (.code (.pure siteBody)) siteBefore ∧
      (siteNext = fun value => .finishNode handle value (callerNext value)) ∧
      siteBefore.native.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      Forwarded siteBefore ⟨entered.1,body queried.left,body queried.right⟩ childBefore siteBefore siteBody ∧
      ∃ (terminal : NodeRequest Symbol Guard) (terminalHandle : Nat),
        SourceCurrentNativeQueryRowOrigins.Route siteBefore siteBody
          ⟨entered.1,body queried.left,body queried.right⟩ terminal ∧
        siteBefore.native.nodes.cells terminalHandle = some ⟨terminal,.returned siteBody⟩ ∧
        SourceCurrentNativeWriterReadyRetention.Written terminalHandle terminal siteBody siteBefore.native ∧
        SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
        SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
        (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
        (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) ∧
        terminalHandle ≠ handle

/-- An actual optional prefix derives the same nonempty child's terminal writer without internal history. -/
theorem request (request : NodeRequest Symbol Guard) (fuel : Nat) (before siteBefore : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (good : Good before) (history : History before) (nonempty : siteBody ≠ .empty)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) siteBefore) :
    Origin request fuel before siteBefore pair siteBody siteNext := by
  obtain ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,left,right,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded⟩ :=
    SourceCurrentNativeOptionalChildOrigin.request request fuel before siteBefore
      pair siteBody siteNext good history actual
  have maps := SourceCurrentNativePrefixWriterMaps.prefix
    (.code (requestNode request.domain request.left request.right)) before siteBefore
    (.code (.optionalBinder pair siteBody siteNext)) fuel (by intro value; trivial)
    good (by intro value; trivial) history actual
  obtain ⟨terminal,terminalHandle,route,cell,writer,notSwap,notReset,leftCodec,rightCodec⟩ :=
    SourceCurrentNativeActiveQueryForwarding.normalize maps.1 _ siteBody forwarded nonempty
  have distinct : terminalHandle ≠ handle := by
    intro same
    subst terminalHandle
    rw [retained] at cell
    cases cell
  exact ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,left,right,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded,terminal,terminalHandle,route,cell,writer,notSwap,notReset,leftCodec,rightCodec,distinct⟩

end MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin.Origin
#print MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin.Origin
#print axioms MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin.Origin

#check @MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin.request
#print MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin.request
#print axioms MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin.request
