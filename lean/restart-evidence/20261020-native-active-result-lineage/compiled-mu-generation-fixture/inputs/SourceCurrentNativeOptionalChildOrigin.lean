import MicroCFTA.SourceCurrentNativeConsistentOptionalOwner
import MicroCFTA.SourceCurrentNativePrefixWriterMaps
import MicroCFTA.SourceCurrentNativeForwardLineage

/-!
# Exact completed child writers at an active optional site

An actual root prefix supplies the returned-writer maps at its reached
state. Its recovered owner retains the queried request and evaluating
cell. The same entered-child return supplies its direct compiler body or
its exact returned cell and historical writer at that site.
-/
namespace MicroCFTA.SourceCurrentNativeOptionalChildOrigin
open Cache InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (effects bind_inverse)
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

private theorem stopped {before after : Checked width} (input : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard) (good : Good before)
    (actual : Trace fuel (.code (requestNode input.domain input.left input.right)) before (.code (.pure result)) after) :
    (SourceRecursiveIntersectionMemo.requestKey width input.domain input.left input.right = none ∧
      ∃ count, Trace count (.code (compileNode input)) before (.code (.pure result)) after) ∨
    ∃ handle, after.native.nodes.cells handle = some ⟨input,.returned result⟩ := by
  cases actual with
  | cons _ _ resume reached _ _ rest inputs one tail =>
    cases key : SourceRecursiveIntersectionMemo.requestKey width input.domain input.left input.right with
    | none =>
      have selected := lookupNode_bypass width input before.native key
      obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
        simpa only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,lift] using one)
      exact Or.inl ⟨rfl,rest,by simpa only [code_bind_pure] using tail⟩
    | some requested =>
      have safe := inputs.2 requested key
      cases selected : lookupNode width input before.native with
      | mk selection chosen =>
        cases selection with
        | direct original =>
          simp only [lookupNode,key] at selected
          cases selected
        | memoized handle =>
          cases demanded : demandNode handle chosen with
          | mk observation running =>
            cases observation with
            | absent | busy =>
              simp only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,demanded,lift] at one
              cases one
            | ready value =>
              have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready input before.native chosen running handle value
                good.native inputs.1 safe selected demanded
              obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
                simpa only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,demanded,lift] using one)
              obtain ⟨rfl,rfl,rfl⟩ := pure_trace rest value result _ after tail.steps
              exact Or.inr ⟨handle,by simpa only [receipt.2.1] using receipt.1⟩
            | evaluate original =>
              have same := SourceCurrentAllocatedNativePhysicalCache.node_started input original before.native chosen running handle
                good.native inputs.1 safe selected demanded
              subst original
              obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
                simpa only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,demanded,lift] using one)
              obtain ⟨inner,outer,value,current,_,bodyTrace,frameTrace⟩ := bind_inverse rest
                (.code (compileNode input)) (fun value => .finishNode handle value (.pure value))
                ⟨running,before.operations⟩ after result tail
              have chosenGood := SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid before.native good.native input inputs.1 safe
              simp only [selected] at chosenGood
              have runningGood := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid chosen chosenGood handle
              simp only [demanded] at runningGood
              have owner := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running input demanded).2
              have retained := SourceEqualityNativeDemandProtectedPrefix.node_body_owner inner handle input
                ⟨running,before.operations⟩ current value runningGood.shape owner bodyTrace.steps
              cases frameTrace with
              | cons _ _ next final _ _ count _ frameStep remaining =>
                obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj frameStep
                obtain ⟨rfl,rfl,rfl⟩ := pure_trace count value result _ after remaining.steps
                exact Or.inr ⟨handle,retained.2⟩

/-- The same optional site retains its queried owner and actual completed child writer. -/
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
      Forwarded siteBefore ⟨entered.1,body queried.left,body queried.right⟩ childBefore siteBefore siteBody

/-- Initial history and the actual prefix derive the same site origin without internal history. -/
theorem request (request : NodeRequest Symbol Guard) (fuel : Nat) (before siteBefore : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) siteBefore) :
    Origin request fuel before siteBefore pair siteBody siteNext := by
  obtain ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,left,right,pairEq,enterInputs,enterStep,child,continuation,retained⟩ :=
    SourceCurrentNativeConsistentOptionalOwner.request request fuel before siteBefore
      pair siteBody siteNext good.native actual
  let compilerBefore : Checked width := ⟨running,queryBefore.operations⟩
  let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
    queried.domain.key queried.left queried.right first second
  let childBefore : Checked width :=
    {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
  have queryFacts := effects earlier good (by intro value; trivial)
  have queryGood := queryFacts.1
  have compilerTrace : Trace 1 (.code (.node queried callerNext)) queryBefore
      (.code ((compileNode queried).bind (fun value => .finishNode handle value (callerNext value)))) compilerBefore :=
    .cons _ _ _ _ _ _ 0 inputs queryStep (.refl _ _)
  have compilerGood := (effects compilerTrace queryGood queryFacts.2.2.2.2).1
  have enterTrace : Trace 1 (.code (compileMu queried.domain queried.left queried.right)) compilerBefore
      (.code ((requestNode entered.1 (body queried.left) (body queried.right)).bind
        (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore :=
    .cons _ _ _ _ _ _ 0 enterInputs enterStep (.refl _ _)
  have childGood := (effects enterTrace compilerGood
    (SourceCurrentAllocatedNativeCodeFields.compileMu_fields _ _ _ _)).1
  have maps := SourceCurrentNativePrefixWriterMaps.prefix
    (.code (requestNode request.domain request.left request.right)) before siteBefore
    (.code (.optionalBinder pair siteBody siteNext)) fuel (by intro value; trivial)
    good (by intro value; trivial) history actual
  have forwarded : Forwarded siteBefore ⟨entered.1,body queried.left,body queried.right⟩
      childBefore siteBefore siteBody := by
    refine ⟨⟨childFuel,child⟩,?_⟩
    rcases stopped ⟨entered.1,body queried.left,body queried.right⟩ childFuel siteBody childGood child with direct | ⟨childHandle,stored⟩
    · exact .inl direct
    · exact .inr ⟨childHandle,stored,maps.1 childHandle _ siteBody stored⟩
  exact ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,left,right,pairEq,enterInputs,enterStep,child,continuation,retained,forwarded⟩

end MicroCFTA.SourceCurrentNativeOptionalChildOrigin
