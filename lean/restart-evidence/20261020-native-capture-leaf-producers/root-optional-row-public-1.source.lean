import MicroCFTA.SourceCurrentNativeActiveRowProduction
import MicroCFTA.SourceCurrentNativeOptionalTerminalOrigin
import MicroCFTA.SourceCurrentNativePrefixWriterMaps

/-!
# The same optional child retains exhaustive actual row producers

One recovered optional owner and terminal writer supply each selected row.
All supported terminal branches retain their actual source fragments.
The statement requires no branch or History premise at the active reader.
-/
namespace MicroCFTA.SourceCurrentNativeOptionalRowProduction
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

/-- One optional owner and terminal writer retain every selected row producer. -/
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
        terminalHandle ≠ handle ∧
        ∀ (rowIndex : Nat) (row : EdgeValue Symbol Guard),
          (InternedEdgeResidency.nodeEdges siteBody)[rowIndex]? = some row →
          SourceCurrentNativeActiveRowProduction.Cases siteBefore terminal siteBody terminalHandle rowIndex row

/-- An actual optional prefix derives row producers from its same selected terminal writer. -/
theorem request (request : NodeRequest Symbol Guard) (fuel : Nat) (before siteBefore : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (good : Good before) (history : History before) (nonempty : siteBody ≠ .empty)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) siteBefore) :
    Origin request fuel before siteBefore pair siteBody siteNext := by
  obtain ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,left,right,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded,
    terminal,terminalHandle,route,cell,writer,notSwap,notReset,leftCodec,rightCodec,distinct⟩ :=
    SourceCurrentNativeOptionalTerminalOrigin.request request fuel before siteBefore
      pair siteBody siteNext good history nonempty actual
  have maps := SourceCurrentNativePrefixWriterMaps.prefix
    (.code (requestNode request.domain request.left request.right)) before siteBefore
    (.code (.optionalBinder pair siteBody siteNext)) fuel (by intro value; trivial)
    good (by intro value; trivial) history actual
  refine ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,left,right,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded,
    terminal,terminalHandle,route,cell,writer,notSwap,notReset,leftCodec,rightCodec,distinct,?_⟩
  intro rowIndex row rowSelected
  exact SourceCurrentNativeActiveRowProduction.terminal maps.1 maps.2.1 terminal siteBody
    terminalHandle writer notSwap notReset rowIndex row rowSelected

end MicroCFTA.SourceCurrentNativeOptionalRowProduction

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentNativeOptionalRowProduction.Origin
#print MicroCFTA.SourceCurrentNativeOptionalRowProduction.Origin
#print axioms MicroCFTA.SourceCurrentNativeOptionalRowProduction.Origin

#check @MicroCFTA.SourceCurrentNativeOptionalRowProduction.request
#print MicroCFTA.SourceCurrentNativeOptionalRowProduction.request
#print axioms MicroCFTA.SourceCurrentNativeOptionalRowProduction.request
