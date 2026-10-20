import MicroCFTA.SourceCurrentNativeOptionalPrefix
import MicroCFTA.SourceRecursiveIntersectionNativeObservations
import MicroCFTA.SourceRecursiveIntersectionNativeShape

/-!
# Actual query prefixes before optional-binder instructions

A node prefix retains the direct original request or the same captured
running node request. An edge prefix retains its actual checked edge body.
Both started cases expose the unbound prefix and exact finish continuation.
The result does not identify a captured request with the current query.
-/
namespace MicroCFTA.SourceCurrentNativeQueryOptionalPrefix
open Cache InternedConstructorTemplates
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeOptionalPrefix (bound_optional_cases)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem pure_no_optional {A : Type} {fuel : Nat} {before after : Checked width}
    (value : A) (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard A)
    (actual : Trace fuel (.code (.pure value)) before (.code (.optionalBinder pair body siteNext)) after) : False := by
  cases actual with
  | cons control initial next current final result count inputs one tail => cases one

private theorem finish_node_no_optional {fuel : Nat} {before after : Checked width}
    (handle : Nat) (value : Node) (pair : Nat × Nat) (body : Node)
    (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code (.finishNode handle value (.pure value))) before
      (.code (.optionalBinder pair body siteNext)) after) : False := by
  cases actual with
  | cons control initial next current final result count inputs one tail =>
    have first : step (.code (.finishNode handle value (.pure value))) before =
        .yielded (.code (.pure value))
          {before with native := SourceRecursiveIntersectionThunks.finishNode handle value before.native} := rfl
    have same := Outcome.yielded.inj (first.symm.trans one)
    rcases same.1 with rfl
    rcases same.2 with rfl
    exact pure_no_optional value pair body siteNext tail

private theorem finish_edge_no_optional {fuel : Nat} {before after : Checked width}
    (handle : Nat) (value : Edge) (pair : Nat × Nat) (body : Node)
    (siteNext : Node → Code Symbol Guard Edge)
    (actual : Trace fuel (.code (.finishEdge handle value (.pure value))) before
      (.code (.optionalBinder pair body siteNext)) after) : False := by
  cases actual with
  | cons control initial next current final result count inputs one tail =>
    have first : step (.code (.finishEdge handle value (.pure value))) before =
        .yielded (.code (.pure value))
          {before with native := SourceRecursiveIntersectionThunks.finishEdge handle value before.native} := rfl
    have same := Outcome.yielded.inj (first.symm.trans one)
    rcases same.1 with rfl
    rcases same.2 with rfl
    exact pure_no_optional value pair body siteNext tail

/-- An unbound node-query prefix keeps its direct source or exact captured running compiler prefix. -/
theorem node {fuel : Nat} (request : NodeRequest Symbol Guard) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair body siteNext)) after) :
    Inputs (.code (requestNode request.domain request.left request.right)) before ∧
    ((∃ compilerFuel,
      fuel = compilerFuel + 1 ∧
      SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none ∧
      lookupNode width request before.native = (.direct request,before.native) ∧
      step (.code (requestNode request.domain request.left request.right)) before =
        .yielded (.code (compileNode request)) before ∧
      Trace compilerFuel (.code (compileNode request)) before (.code (.optionalBinder pair body siteNext)) after) ∨
    (∃ compilerFuel handle chosen running captured compilerBefore innerNext,
      fuel = compilerFuel + 1 ∧
      lookupNode width request before.native = (.memoized handle,chosen) ∧
      demandNode handle chosen = (.evaluate captured,running) ∧
      chosen.nodes.cells handle = some ⟨captured,.suspended⟩ ∧
      running.nodes.cells handle = some ⟨captured,.evaluating⟩ ∧
      running.machine = before.native.machine ∧
      compilerBefore = ⟨running,before.operations⟩ ∧
      step (.code (requestNode request.domain request.left request.right)) before =
        .yielded ((.code (compileNode captured) : Control Node).bind
          (fun value => .finishNode handle value (.pure value))) compilerBefore ∧
      Trace compilerFuel (.code (compileNode captured)) compilerBefore
        (.code (.optionalBinder pair body innerNext)) after ∧
      siteNext = fun value => (innerNext value).bind (fun result => .finishNode handle result (.pure result)))) := by
  cases actual with
  | cons control initial next current final result count inputs one tail =>
    refine ⟨inputs,?_⟩
    cases selected : lookupNode width request before.native with
    | mk selection chosen =>
      cases selection with
      | direct captured =>
        obtain ⟨sameRequest,sameState⟩ :=
          SourceRecursiveIntersectionNative.lookupNode_direct request captured before.native chosen selected
        subst captured
        subst chosen
        have same := Outcome.yielded.inj (by simpa only [step,requestNode,
          SourceRecursiveIntersectionNative.step,selected,lift] using one)
        rcases same.1 with rfl
        rcases same.2 with rfl
        have unresolved : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none := by
          cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
          | none => rfl
          | some key => simp only [lookupNode,requested] at selected; cases selected
        refine .inl ⟨count,rfl,unresolved,rfl,?_,?_⟩
        · simpa only [code_bind_pure] using one
        · simpa only [code_bind_pure] using tail
      | memoized handle =>
        cases demanded : demandNode handle chosen with
        | mk observation running =>
          cases observation with
          | absent | busy =>
            simp only [step,requestNode,SourceRecursiveIntersectionNative.step,selected,demanded,lift] at one
            cases one
          | ready value =>
            have same := Outcome.yielded.inj (by simpa only [step,requestNode,
              SourceRecursiveIntersectionNative.step,selected,demanded,lift] using one)
            rcases same.1 with rfl
            rcases same.2 with rfl
            exact False.elim (pure_no_optional value pair body siteNext tail)
          | evaluate captured =>
            have same := Outcome.yielded.inj (by simpa only [step,requestNode,
              SourceRecursiveIntersectionNative.step,selected,demanded,lift] using one)
            rcases same.1 with rfl
            rcases same.2 with rfl
            rcases bound_optional_cases count (.code (compileNode captured))
                (fun value => .finishNode handle value (.pure value))
                ⟨running,before.operations⟩ after pair body siteNext tail with
                ⟨innerNext,unbound,sameNext⟩ | ⟨innerFuel,outerFuel,value,middle,total,completed,suffix⟩
            · have cells := SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running captured demanded
              have runningMachine : running.machine = chosen.machine := by
                simpa only [demanded] using SourceRecursiveIntersectionNative.demandNode_machine handle chosen
              have chosenMachine : chosen.machine = before.native.machine := by
                simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request before.native
              exact .inr ⟨count,handle,chosen,running,captured,⟨running,before.operations⟩,innerNext,
                rfl,rfl,demanded,cells.1,cells.2,runningMachine.trans chosenMachine,rfl,one,unbound,sameNext⟩
            · exact False.elim (finish_node_no_optional handle value pair body siteNext suffix)

/-- An unbound edge-query prefix keeps the same captured checked body and protected finish continuation. -/
theorem edge {fuel : Nat} (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (pair : Nat × Nat) (body : Node) (siteNext : Node → Code Symbol Guard Edge)
    (actual : Trace fuel (.code (requestEdge request.domain request.left request.right)) before
      (.code (.optionalBinder pair body siteNext)) after) :
    Inputs (.code (requestEdge request.domain request.left request.right)) before ∧
    ∃ compilerFuel handle chosen running captured compilerBefore innerNext,
      fuel = compilerFuel + 1 ∧
      lookupEdge width request before.native = (handle,chosen) ∧
      demandEdge handle chosen = (.evaluate captured,running) ∧
      chosen.edges.cells handle = some ⟨captured,.suspended⟩ ∧
      running.edges.cells handle = some ⟨captured,.evaluating⟩ ∧
      running.machine = before.native.machine ∧
      compilerBefore = ⟨running,before.operations⟩ ∧
      step (.code (requestEdge request.domain request.left request.right)) before =
        .yielded ((Control.edgeBody captured (.pure : Edge → Code Symbol Guard Edge)).bind
          (fun value => .finishEdge handle value (.pure value))) compilerBefore ∧
      Trace compilerFuel (.edgeBody captured .pure) compilerBefore
        (.code (.optionalBinder pair body innerNext)) after ∧
      siteNext = fun value => (innerNext value).bind (fun result => .finishEdge handle result (.pure result)) := by
  cases actual with
  | cons control initial next current final result count inputs one tail =>
    refine ⟨inputs,?_⟩
    cases selected : lookupEdge width request before.native with
    | mk handle chosen =>
      cases demanded : demandEdge handle chosen with
      | mk observation running =>
        cases observation with
        | absent | busy =>
          simp only [step,requestEdge,selected,demanded] at one
          cases one
        | ready value =>
          have same := Outcome.yielded.inj (by simpa only [step,requestEdge,selected,demanded] using one)
          rcases same.1 with rfl
          rcases same.2 with rfl
          exact False.elim (pure_no_optional value pair body siteNext tail)
        | evaluate captured =>
          have same := Outcome.yielded.inj (by simpa only [step,requestEdge,selected,demanded] using one)
          rcases same.1 with rfl
          rcases same.2 with rfl
          rcases bound_optional_cases count (.edgeBody captured (.pure : Edge → Code Symbol Guard Edge))
              (fun value => .finishEdge handle value (.pure value))
              ⟨running,before.operations⟩ after pair body siteNext tail with
              ⟨innerNext,unbound,sameNext⟩ | ⟨innerFuel,outerFuel,value,middle,total,completed,suffix⟩
          · have cells := SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running captured demanded
            have runningMachine : running.machine = chosen.machine := by
              simpa only [demanded] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
            have chosenMachine : chosen.machine = before.native.machine := by
              simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
            exact ⟨count,handle,chosen,running,captured,⟨running,before.operations⟩,innerNext,
              rfl,rfl,demanded,cells.1,cells.2,runningMachine.trans chosenMachine,rfl,one,unbound,sameNext⟩
          · exact False.elim (finish_edge_no_optional handle value pair body siteNext suffix)

end MicroCFTA.SourceCurrentNativeQueryOptionalPrefix
