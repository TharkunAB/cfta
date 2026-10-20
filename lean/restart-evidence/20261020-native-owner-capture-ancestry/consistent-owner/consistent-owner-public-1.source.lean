import MicroCFTA.SourceCurrentNativeOwnerSiteRetention

/-!
# Exact queried owners at an actual optional instruction

Initial physical cache validity follows the actual checked prefix.
The same selected owner then retains the queried request at its compiler
entry and at the selected optional instruction.
-/
namespace MicroCFTA.SourceCurrentNativeConsistentOptionalOwner
open Cache InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem trace_valid {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (valid : Physical before.native) :
    Physical after.native := by
  induction actual with
  | refl => exact valid
  | cons control state next current final result count inputs one tail ih =>
      apply ih
      simpa only [one, Outcome.state] using
        SourceCurrentAllocatedNativePhysicalExecution.step_valid control state valid inputs

/-- The same actual owner captures its queried request and retains its evaluating cell at the site. -/
theorem request (request : NodeRequest Symbol Guard) (fuel : Nat) (before siteBefore : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (valid : Physical before.native)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) siteBefore) :
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
      siteBefore.native.nodes.cells handle = some ⟨queried, .evaluating⟩ := by
  obtain ⟨queryFuel, childFuel, queried, callerNext, queryBefore, handle, chosen, running,
    captured, first, second, total, earlier, inputs, selected, demanded, suspended, evaluating,
    machine, queryStep, recursive, left, right, pairEq, enterInputs, enterStep, child, continuation,
    retained⟩ := SourceCurrentNativeOwnerSiteRetention.request request fuel before siteBefore
      pair siteBody siteNext valid.shape actual
  have queryValid := trace_valid earlier valid
  obtain ⟨key, keyEq, _, _⟩ :=
    SourceRecursiveIntersectionNative.lookupNode_memoized queried queryBefore.native chosen handle selected
  have same := SourceCurrentAllocatedNativePhysicalCache.node_started queried captured
    queryBefore.native chosen running handle queryValid inputs.1 (inputs.2 key keyEq) selected demanded
  subst captured
  exact ⟨queryFuel, childFuel, queried, callerNext, queryBefore, handle, chosen, running,
    first, second, total, earlier, inputs, selected, demanded, suspended, evaluating,
    machine, queryStep, recursive, left, right, pairEq, enterInputs, enterStep, child, continuation, retained⟩

end MicroCFTA.SourceCurrentNativeConsistentOptionalOwner

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
#check @MicroCFTA.SourceCurrentNativeConsistentOptionalOwner.request
#print MicroCFTA.SourceCurrentNativeConsistentOptionalOwner.request
#print axioms MicroCFTA.SourceCurrentNativeConsistentOptionalOwner.request
