import MicroCFTA.SourceCurrentNativeOptionalPrefix
import MicroCFTA.SourceCurrentAllocatedNativeMuSource

/-!
# Correlated compiler-owner receipts at an optional instruction

One receipt retains the actual query, full capture, domain entry and child
return. Prefix and continuation transport keep the same optional site.
The receipt does not require a future owner return or identify source syntax.
-/
namespace MicroCFTA.SourceCurrentNativeOptionalOwnerReceipt
open Cache InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {A B : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The same actual captured query owns the entered Mu call and its exact child return. -/
def Owner (fuel : Nat) (control : Control A) (before : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard A)
    (siteBefore : Checked width) : Prop :=
  ∃ (queryFuel childFuel : Nat) (queried : NodeRequest Symbol Guard)
      (callerNext : Node → Code Symbol Guard A) (queryBefore : Checked width)
      (handle : Nat) (chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard)
      (captured : NodeRequest Symbol Guard) (first second : Nat),
    let compilerBefore : Checked width := ⟨running, queryBefore.operations⟩
    let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
      captured.domain.key captured.left captured.right first second
    let childBefore : Checked width :=
      {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
    fuel = queryFuel + 2 + childFuel ∧
    Trace queryFuel control before (.code (.node queried callerNext)) queryBefore ∧
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
    siteNext = fun value => .finishNode handle value (callerNext value)

/-- Appending code retains the same query, capture, entered body return and optional occurrence. -/
theorem bind {fuel : Nat} {control : Control A} {before siteBefore : Checked width}
    {pair : Nat × Nat} {siteBody : Node} {siteNext : Node → Code Symbol Guard A}
    (owner : Owner fuel control before pair siteBody siteNext siteBefore)
    (next : A → Code Symbol Guard B) :
    Owner fuel (control.bind next) before pair siteBody
      (fun value => (siteNext value).bind next) siteBefore := by
  rcases owner with ⟨queryFuel, childFuel, queried, callerNext, queryBefore, handle, chosen, running,
    captured, first, second, total, earlier, inputs, selected, demanded, suspended, evaluating,
    machine, queryStep, recursive, left, right, pairEq, enterInputs, enterStep, child, continuation⟩
  have boundStep := step_bind (.code (.node queried callerNext)) next queryBefore
  rw [queryStep] at boundStep
  have mapped : step (.code (.node queried (fun value => (callerNext value).bind next))) queryBefore =
      .yielded (.code ((compileNode captured).bind
        (fun value => .finishNode handle value ((callerNext value).bind next))))
        (⟨running, queryBefore.operations⟩ : Checked width) := by
    simpa only [Control.bind, Code.bind, appendStep, Code.bind_assoc] using boundStep
  refine ⟨queryFuel, childFuel, queried, (fun value => (callerNext value).bind next), queryBefore,
    handle, chosen, running, captured, first, second, total, earlier.bind next, inputs, selected,
    demanded, suspended, evaluating, machine, mapped, recursive, left, right, pairEq,
    enterInputs, enterStep, child, ?_⟩
  rw [continuation]
  rfl

/-- An actual earlier prefix retains the same later compiler-owner receipt and exact fuel sum. -/
theorem prepend {fuel prefixFuel : Nat} {control middle : Control A}
    {before current siteBefore : Checked width} {pair : Nat × Nat} {siteBody : Node}
    {siteNext : Node → Code Symbol Guard A}
    (earlier : Trace prefixFuel control before middle current)
    (owner : Owner fuel middle current pair siteBody siteNext siteBefore) :
    Owner (prefixFuel + fuel) control before pair siteBody siteNext siteBefore := by
  rcases owner with ⟨queryFuel, childFuel, queried, callerNext, queryBefore, handle, chosen, running,
    captured, first, second, total, queriedPrefix, inputs, selected, demanded, suspended, evaluating,
    machine, queryStep, recursive, left, right, pairEq, enterInputs, enterStep, child, continuation⟩
  exact ⟨prefixFuel + queryFuel, childFuel, queried, callerNext, queryBefore, handle, chosen, running,
    captured, first, second, by omega, earlier.trans queriedPrefix, inputs, selected, demanded,
    suspended, evaluating, machine, queryStep, recursive, left, right, pairEq, enterInputs,
    enterStep, child, continuation⟩

end MicroCFTA.SourceCurrentNativeOptionalOwnerReceipt
