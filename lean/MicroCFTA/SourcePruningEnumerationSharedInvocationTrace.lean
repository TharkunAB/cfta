import MicroCFTA.SourcePruningEnumerationSharedEagerOutputBlocks

namespace MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild consumeSelected ordinaryNonterminal)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "Row" => (Symbol × List Input × Option Constraint) × Cached
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Done" => Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "Stopped" => Observation width → Option Cached → Result Output Reason width
local notation "TupleDone" => List Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "TupleStopped" => List Fragment → Observation width → Option Cached → Result Output Reason width
set_option autoImplicit false

/-- Record which existing child policy the invocation uses. -/
inductive Policy where
  | eager
  | shallow
  | guarded (parent : Node)

/-- Record the exact terminal child continuation arguments. -/
inductive ChildExit (width : Nat) where
  | done (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
  | stopped (observation : Observation width) (candidate : Option Cached)

/-- Record the exact terminal tuple continuation arguments. -/
inductive TupleExit (width : Nat) where
  | done (fragments : List Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
  | stopped (completed : List Fragment) (observation : Observation width) (candidate : Option Cached)

/-- Retain the completed head fragment in the literal tuple callback. -/
def TupleExit.prepend (fragment : Fragment) : TupleExit width → TupleExit width
  | .done fragments reached saved after => .done (fragment :: fragments) reached saved after
  | .stopped completed observation candidate => .stopped (fragment :: completed) observation candidate

/-- Read the selected actual child continuation's output list. -/
def childExitOutputs (done : Done) (stopped : Stopped) : ChildExit width → List Output
  | .done fragment reached saved after => outputs (done fragment reached saved after)
  | .stopped observation candidate => outputs (stopped observation candidate)

/-- Read the selected actual tuple continuation's output list. -/
def tupleExitOutputs (done : TupleDone) (stopped : TupleStopped) : TupleExit width → List Output
  | .done fragments reached saved after => outputs (done fragments reached saved after)
  | .stopped completed observation candidate => outputs (stopped completed observation candidate)

/-- Classify exactly the shared dispatch outcomes that invoke the stopped continuation. -/
def ShallowStopped (observation : Observation width) (candidate : Option Cached) : Prop :=
  match observation, candidate with
  | (.ok (some [.ok _]), _, _, _, _), some _ => False
  | _, _ => True

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Select existing child code. This definition adds no recursive implementation. -/
noncomputable def runPolicy (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    Policy → List Suspended → Node → Caller width → Cached → Queries → Done → Stopped → Result Output Reason width
  | .eager => eagerChild checkEmpty r n p h k edgesOf
  | .shallow => shallowVisit checkEmpty r n p h k
  | .guarded parent => fun scs incoming caller before queries done stopped =>
      if _lower : MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent then
        eagerChild checkEmpty r n p h k edgesOf scs incoming caller before queries done stopped
      else shallowVisit checkEmpty r n p h k scs incoming caller before queries done stopped

/- Note [Indexed invocation ancestry]
The relations record calls to the existing child operations.
Each constructor retains its actual control observation.
The local index belongs to that constructor's terminal callback.
Tuple constructors link the child index to the literal remaining tuple.
There is no constructor from output equality alone.
runPolicy selects existing code and adds no recursive worker.
-/

mutual
/-- Derive an indexed terminal child invocation from literal existing control steps. -/
inductive ChildInvocationAt (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    Policy → List Suspended → Node → Caller width → Cached → Queries → Done → Stopped →
      Nat → Output → ChildExit width → Nat → Prop where
  | shallow_done
      {scs : List Suspended} {incoming : Node} {caller reached : Caller width}
      {before after : Cached} {queries saved : Queries} {done : Done} {stopped : Stopped}
      {index : Nat} {output : Output} {fragment : Fragment} {returned read : Core}
      {waiting : EnumerationWaitingIndex.Waiting}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after))
      (observed : (outputs (done fragment reached saved after))[index]? = some output) :
      ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output (.done fragment reached saved after) index
  | shallow_stopped
      {scs : List Suspended} {incoming : Node} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped} {index : Nat} {output : Output}
      {observation : Observation width} {candidate : Option Cached}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        (observation, candidate))
      (shape : ShallowStopped observation candidate)
      (observed : (outputs (stopped observation candidate))[index]? = some output) :
      ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output (.stopped observation candidate) index
  | guarded_lower
      {parent incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (lower : MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (child : ChildInvocationAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output exit localIndex) :
      ChildInvocationAt checkEmpty r n p h k edgesOf (.guarded parent) scs incoming caller before queries
        done stopped index output exit localIndex
  | guarded_else
      {parent incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (lower : ¬MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (child : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex) :
      ChildInvocationAt checkEmpty r n p h k edgesOf (.guarded parent) scs incoming caller before queries
        done stopped index output exit localIndex
  | eager_fallback
      {incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (fallback : ordinaryNonterminal scs incoming = false)
      (child : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex) :
      ChildInvocationAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output exit localIndex
  | eager_ordinary
      {incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index rowIndex localIndex : Nat} {output : Output}
      {attempted remaining : List Edge} {edge : Edge} {rowCaller : Caller width} {rowQueries : Queries}
      {processed : List (Receipt width)} {earlier : List Output} {rowResult : Result Output Reason width}
      {fragment : Fragment} {reached : Caller width} {saved : Queries} {after : Cached}
      (ordinary : ordinaryNonterminal scs incoming = true)
      (order : edgesOf incoming = attempted ++ edge :: remaining)
      (past : scan (fun selected current capturedQueries captured =>
        visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
          (consumeSelected done current capturedQueries) scs selected current captured capturedQueries)
        before attempted caller queries = .complete processed earlier rowCaller rowQueries)
      (rowRun : visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries = rowResult)
      (row : SelectedInvocationAt checkEmpty r n p h k edgesOf (.guarded incoming)
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries
        rowIndex output (.complete fragment reached saved after) localIndex)
      (offset : index = earlier.length + rowIndex)
      (observed : (outputs (done fragment reached saved after))[localIndex]? = some output) :
      ChildInvocationAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output (.done fragment reached saved after) localIndex

/-- Derive tuple ancestry by linking each actual child callback to its literal tail. -/
inductive ChildrenInvocationAt (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    Policy → TupleDone → TupleStopped → List (Node × List Suspended) → Caller width → Cached → Queries →
      Nat → Output → TupleExit width → Nat → Prop where
  | nil
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {caller : Caller width} {before : Cached} {queries : Queries} {index : Nat} {output : Output}
      (observed : (outputs (done [] caller queries before))[index]? = some output) :
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped [] caller before queries
        index output (.done [] caller queries before) index
  | cons_done
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
      {fragment : Fragment} {index childIndex localIndex : Nat} {output : Output} {exit : TupleExit width}
      (child : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped [] observation candidate)
        index output (.done fragment reached saved after) childIndex)
      (tail : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) rest reached after saved
        childIndex output exit localIndex) :
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped ((incoming, bucket) :: rest)
        caller before queries index output (TupleExit.prepend fragment exit) localIndex
  | cons_stopped
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller : Caller width} {before : Cached} {queries : Queries}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (child : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun current captured => stopped [] current captured)
        index output (.stopped observation candidate) localIndex) :
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped ((incoming, bucket) :: rest)
        caller before queries index output (.stopped [] observation candidate) localIndex

/-- Derive the consumer receipt from the same literal preparation and tuple trace. -/
inductive SelectedInvocationAt (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    Policy → (Receipt width → Result Output Reason width) → List Suspended → Edge →
      Caller width → Cached → Queries → Nat → Output → Receipt width → Nat → Prop where
  | unhandled_none
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = none)
      (observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output .unhandled index
  | unhandled_many
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {first second : Row} {rest : List Row} {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some (first :: second :: rest))
      (observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output .unhandled index
  | rejected
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = some [])
      (observed : (outputs (consume (.rejected caller queries before)))[index]? = some output) :
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output (.rejected caller queries before) index
  | singleton_done
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller reached : Caller width}
      {before middle after : Cached} {queries saved : Queries}
      {symbol : Symbol} {staged : List Input} {residual : Option Constraint} {fragments : List Fragment}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (children : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun completed observation candidate => consume (.stopped completed observation candidate))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.done fragments reached saved after) localIndex) :
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output (.complete (.node symbol fragments) reached saved
          (SelectedEdge.finish residual (.node symbol fragments) after)) localIndex
  | singleton_stopped
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width}
      {before middle : Cached} {queries : Queries} {symbol : Symbol}
      {staged : List Input} {residual : Option Constraint} {completed : List Fragment}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (children : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun finished current captured => consume (.stopped finished current captured))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.stopped completed observation candidate) localIndex) :
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output (.stopped completed observation candidate) localIndex
end

end MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
