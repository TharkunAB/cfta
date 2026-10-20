import MicroCFTA.SourceCurrentNativeOptionalOwner
import MicroCFTA.SourceEqualityNativeDemandMemo
import MicroCFTA.SourceEqualityNativeDemandRunning

/-!
# The actual captured owner stays evaluating at its optional site

Initial native Shape protects allocated handles. The actual earlier
prefix derives Shape at the captured compiler entry. The same completed
entered-child trace retains the captured evaluating cell at the site.
No future owner return or desired active-cell premise is required.
-/
namespace MicroCFTA.SourceCurrentNativeOwnerSiteRetention
open Cache InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionNative (Shape)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem prefix_shape (fuel : Nat) (control next : Control A)
    (before after : Checked width) (shape : Shape before.native)
    (actual : Trace fuel control before next after) : Shape after.native := by
  have preserved := SourceEqualityNativeDemandMemo.execute_preserves fuel control before shape
  have executed := SourceEqualityNativeDemand.Steps.execute fuel control next before after actual.steps
  simpa only [executed, Outcome.state] using preserved.1

/-- An actual node optional prefix retains the same captured owner and its evaluating cell at the site. -/
theorem request (request : NodeRequest Symbol Guard) (fuel : Nat) (before siteBefore : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (shape : Shape before.native)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) siteBefore) :
  ∃ (queryFuel childFuel : Nat) (queried : NodeRequest Symbol Guard)
      (callerNext : Node → Code Symbol Guard Node) (queryBefore : Checked width)
      (handle : Nat) (chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard)
      (captured : NodeRequest Symbol Guard) (first second : Nat),
    let compilerBefore : Checked width := ⟨running, queryBefore.operations⟩
    let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
      captured.domain.key captured.left captured.right first second
    let childBefore : Checked width :=
      {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
    fuel = queryFuel + 2 + childFuel ∧
    Trace queryFuel (.code (requestNode request.domain request.left request.right)) before (.code (.node queried callerNext)) queryBefore ∧
    Inputs (.code (.node queried callerNext)) queryBefore ∧
    lookupNode width queried queryBefore.native = (.memoized handle, chosen) ∧
    demandNode handle chosen = (.evaluate captured, running) ∧
    chosen.nodes.cells handle = some ⟨captured, .suspended⟩ ∧
    running.nodes.cells handle = some ⟨captured, .evaluating⟩ ∧
    running.machine = queryBefore.native.machine ∧
    step (.code (.node queried callerNext)) queryBefore = .yielded
      (.code ((compileNode captured).bind (fun value => .finishNode handle value (callerNext value)))) compilerBefore ∧
    (SourceRecursiveIntersectionControl.decision captured.domain.key captured.left captured.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision captured.domain.key captured.left captured.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision captured.domain.key captured.left captured.right = .rightMu) ∧
    SourceRecursiveIntersectionControl.identity captured.left = some first ∧
    SourceRecursiveIntersectionControl.identity captured.right = some second ∧
    pair = SourceRecursiveIntersectionControl.pair first second ∧
    Inputs (.code (compileMu captured.domain captured.left captured.right)) compilerBefore ∧
    step (.code (compileMu captured.domain captured.left captured.right)) compilerBefore =
      .yielded (.code ((requestNode entered.1 (body captured.left) (body captured.right)).bind
        (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
    Trace childFuel (.code (requestNode entered.1 (body captured.left) (body captured.right)))
      childBefore (.code (.pure siteBody)) siteBefore ∧
    siteNext = fun value => .finishNode handle value (callerNext value) ∧
    siteBefore.native.nodes.cells handle = some ⟨captured, .evaluating⟩ := by
  obtain ⟨queryFuel, childFuel, queried, callerNext, queryBefore, handle, chosen, running,
    captured, first, second, total, earlier, inputs, selected, demanded, suspended, evaluating,
    machine, queryStep, recursive, left, right, pairEq, enterInputs, enterStep, child, continuation⟩ :=
    SourceCurrentNativeOptionalOwner.request request fuel before siteBefore pair siteBody siteNext actual
  have queryShape := prefix_shape queryFuel _ _ before queryBefore shape earlier
  have chosenShape : Shape chosen := by
    simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_shape queried queryBefore.native queryShape
  have runningShape : Shape running := by
    simpa only [demanded] using SourceRecursiveIntersectionNative.demandNode_shape handle chosen chosenShape
  let compilerBefore : Checked width := ⟨running, queryBefore.operations⟩
  let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
    captured.domain.key captured.left captured.right first second
  let childBefore : Checked width :=
    {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
  have childShape : Shape childBefore.native := runningShape
  have childEvaluating : childBefore.native.nodes.cells handle = some ⟨captured, .evaluating⟩ := evaluating
  have retained := SourceEqualityNativeDemandRunning.trace_retains childFuel
    (.code (requestNode entered.1 (body captured.left) (body captured.right))) childBefore siteBefore siteBody
    child.steps (by intro value; trivial) childShape
  exact ⟨queryFuel, childFuel, queried, callerNext, queryBefore, handle, chosen, running,
    captured, first, second, total, earlier, inputs, selected, demanded, suspended, evaluating,
    machine, queryStep, recursive, left, right, pairEq, enterInputs, enterStep, child, continuation,
    retained.2.1 handle captured childEvaluating⟩

end MicroCFTA.SourceCurrentNativeOwnerSiteRetention
