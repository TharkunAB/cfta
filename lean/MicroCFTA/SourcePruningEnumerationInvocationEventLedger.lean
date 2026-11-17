import MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
import MicroCFTA.SourcePruningEnumerationSharedChildInvocationOrigins
import MicroCFTA.SourcePruningEnumerationSharedInvocationCombinators

namespace MicroCFTA.SourcePruningEnumerationInvocationEventLedger
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedChildVisitors (visitChildren)
open SourcePruningEnumerationSharedEagerChildren (consumeSelected ordinaryNonterminal)
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

/- Note [One invocation event ledger]
The event list records actual operation arguments and returned data.
The mutual ledger relations retain those observations in one derivation.
They do not use a Prop proof as the identity of hidden event data.
A consumer must eliminate one ledger derivation for all its witnesses.

The path records nested staged child positions. Tuple position starts at zero.
It is a position tag, not a globally unique runtime event identifier.
The ordered event list and actual caller/cache cuts distinguish occurrences.
Only the chosen ordinary row contributes enum events.
Its completed sibling prefix supplies the actual native caller and queries.
The tuple concatenates child events and the actual remaining tuple events.
A selected success adds residual finish after its exact child events.
Shallow dispatch stays an explicit operation cut with its entire raw receipt.

No callback effects after the terminal exit are included here.
The outer history must attach that actual continuation separately.
The relations add no runtime evaluator or semantic model.
-/

/-- Retain actual inputs and outputs of each operation cut on one invocation. -/
inductive Event (width : Nat) where
  | prepare (path : List Nat) (scs : List Suspended) (edge : Edge)
      (caller : Caller width) (before : Cached) (queries : Queries) (rows : Option (List Row))
  | residual (path : List Nat) (guard : Option Constraint) (fragment : Fragment)
      (caller : Caller width) (queries : Queries) (before after : Cached)
  | dispatch (path : List Nat) (checkEmpty : Bool) (r n p h k : Nat)
      (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached)
      (queries : Queries) (observed : Observation width) (candidate : Option Cached)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Each retained operation cut is the literal existing operation. -/
def AuthenticEvent : Event width → Prop
  | .prepare _ scs edge caller before _ rows =>
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = rows
  | .residual _ guard fragment _ _ before after => after = SelectedEdge.finish guard fragment before
  | .dispatch _ checkEmpty r n p h k scs incoming caller before queries observed candidate =>
      ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries = (observed, candidate)

mutual
/-- Record every selected preparation before one actual child terminal callback. -/
inductive ChildLedgerAt (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    Policy → List Suspended → Node → Caller width → Cached → Queries → Done → Stopped →
      Nat → Output → ChildExit width → Nat → List Nat → List (Event width) → Prop where
  | shallow_done
      {path : List Nat} {scs : List Suspended} {incoming : Node} {caller reached : Caller width}
      {before after : Cached} {queries saved : Queries} {done : Done} {stopped : Stopped}
      {index : Nat} {output : Output} {fragment : Fragment} {returned read : Core}
      {waiting : EnumerationWaitingIndex.Waiting}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after))
      (observed : (outputs (done fragment reached saved after))[index]? = some output) :
      ChildLedgerAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output (.done fragment reached saved after) index path
        [.dispatch path checkEmpty r n p h k scs incoming caller before queries
          (.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting) (some after)]
  | shallow_stopped
      {path : List Nat} {scs : List Suspended} {incoming : Node} {caller : Caller width}
      {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index : Nat} {output : Output} {observation : Observation width} {candidate : Option Cached}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries = (observation, candidate))
      (shape : ShallowStopped observation candidate)
      (observed : (outputs (stopped observation candidate))[index]? = some output) :
      ChildLedgerAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output (.stopped observation candidate) index path
        [.dispatch path checkEmpty r n p h k scs incoming caller before queries observation candidate]
  | guarded_lower
      {path : List Nat} {events : List (Event width)} {parent incoming : Node} {scs : List Suspended}
      {caller : Caller width} {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (lower : MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (child : ChildLedgerAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output exit localIndex path events) :
      ChildLedgerAt checkEmpty r n p h k edgesOf (.guarded parent) scs incoming caller before queries
        done stopped index output exit localIndex path events
  | guarded_else
      {path : List Nat} {events : List (Event width)} {parent incoming : Node} {scs : List Suspended}
      {caller : Caller width} {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (lower : ¬MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (child : ChildLedgerAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex path events) :
      ChildLedgerAt checkEmpty r n p h k edgesOf (.guarded parent) scs incoming caller before queries
        done stopped index output exit localIndex path events
  | eager_fallback
      {path : List Nat} {events : List (Event width)} {incoming : Node} {scs : List Suspended}
      {caller : Caller width} {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (fallback : ordinaryNonterminal scs incoming = false)
      (child : ChildLedgerAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex path events) :
      ChildLedgerAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output exit localIndex path events
  | eager_ordinary
      {path : List Nat} {events : List (Event width)} {incoming : Node} {scs : List Suspended}
      {caller : Caller width} {before : Cached} {queries : Queries} {done : Done} {stopped : Stopped}
      {index rowIndex localIndex : Nat} {output : Output}
      {attempted remaining : List Edge} {edge : Edge} {rowCaller : Caller width} {rowQueries : Queries}
      {processed : List (Receipt width)} {earlier : List Output} {rowResult : Result Output Reason width}
      {fragment : Fragment} {reached : Caller width} {saved : Queries} {after : Cached}
      (ordinary : ordinaryNonterminal scs incoming = true)
      (rowOrder : edgesOf incoming = attempted ++ edge :: remaining)
      (past : scan (fun selected current capturedQueries captured =>
        SourcePruningEnumerationSharedChildVisitors.visitSelected
          (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
          (consumeSelected done current capturedQueries) scs selected current captured capturedQueries)
        before attempted caller queries = .complete processed earlier rowCaller rowQueries)
      (rowRun : SourcePruningEnumerationSharedChildVisitors.visitSelected
        (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries = rowResult)
      (row : SelectedLedgerAt checkEmpty r n p h k edgesOf (.guarded incoming)
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries
        rowIndex output (.complete fragment reached saved after) localIndex path events)
      (offset : index = earlier.length + rowIndex)
      (observed : (outputs (done fragment reached saved after))[localIndex]? = some output) :
      ChildLedgerAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output (.done fragment reached saved after) localIndex path events

/-- Record the exact child positions and the actual tuple tail in order. -/
inductive ChildrenLedgerAt (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    Policy → TupleDone → TupleStopped → List (Node × List Suspended) → Caller width → Cached → Queries →
      Nat → Output → TupleExit width → Nat → List Nat → Nat → List (Event width) → Prop where
  | nil
      {path : List Nat} {position : Nat} {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {caller : Caller width} {before : Cached} {queries : Queries} {index : Nat} {output : Output}
      (observed : (outputs (done [] caller queries before))[index]? = some output) :
      ChildrenLedgerAt checkEmpty r n p h k edgesOf policy done stopped [] caller before queries
        index output (.done [] caller queries before) index path position []
  | cons_done
      {path : List Nat} {position : Nat} {childEvents tailEvents : List (Event width)}
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
      {fragment : Fragment} {index childIndex localIndex : Nat} {output : Output} {exit : TupleExit width}
      (child : ChildLedgerAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped [] observation candidate)
        index output (.done fragment reached saved after) childIndex (path ++ [position]) childEvents)
      (tail : ChildrenLedgerAt checkEmpty r n p h k edgesOf policy
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) rest reached after saved
        childIndex output exit localIndex path (position + 1) tailEvents) :
      ChildrenLedgerAt checkEmpty r n p h k edgesOf policy done stopped ((incoming, bucket) :: rest)
        caller before queries index output (TupleExit.prepend fragment exit) localIndex
        path position (childEvents ++ tailEvents)
  | cons_stopped
      {path : List Nat} {position : Nat} {childEvents : List (Event width)}
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller : Caller width} {before : Cached} {queries : Queries}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (child : ChildLedgerAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun current captured => stopped [] current captured)
        index output (.stopped observation candidate) localIndex (path ++ [position]) childEvents) :
      ChildrenLedgerAt checkEmpty r n p h k edgesOf policy done stopped ((incoming, bucket) :: rest)
        caller before queries index output (.stopped [] observation candidate) localIndex path position childEvents

/-- Retain each actual own preparation and the same tuple's residual finish. -/
inductive SelectedLedgerAt (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    Policy → (Receipt width → Result Output Reason width) → List Suspended → Edge →
      Caller width → Cached → Queries → Nat → Output → Receipt width → Nat →
        List Nat → List (Event width) → Prop where
  | unhandled_none
      {path : List Nat} {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = none)
      (observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedLedgerAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output .unhandled index path [.prepare path scs edge caller before queries none]
  | unhandled_many
      {path : List Nat} {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {first second : Row} {rest : List Row} {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some (first :: second :: rest))
      (observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedLedgerAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output .unhandled index path
        [.prepare path scs edge caller before queries (some (first :: second :: rest))]
  | rejected
      {path : List Nat} {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = some [])
      (observed : (outputs (consume (.rejected caller queries before)))[index]? = some output) :
      SelectedLedgerAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output (.rejected caller queries before) index path
        [.prepare path scs edge caller before queries (some [])]
  | singleton_done
      {path : List Nat} {events : List (Event width)}
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller reached : Caller width}
      {before middle after : Cached} {queries saved : Queries}
      {symbol : Symbol} {staged : List Input} {residual : Option Constraint} {fragments : List Fragment}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (children : ChildrenLedgerAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun completed observation candidate => consume (.stopped completed observation candidate))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.done fragments reached saved after) localIndex path 0 events) :
      SelectedLedgerAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output (.complete (.node symbol fragments) reached saved
          (SelectedEdge.finish residual (.node symbol fragments) after)) localIndex path
        ([.prepare path scs edge caller before queries (some [((symbol, staged, residual), middle)])] ++
          events ++ [.residual path residual (.node symbol fragments) reached saved after
            (SelectedEdge.finish residual (.node symbol fragments) after)])
  | singleton_stopped
      {path : List Nat} {events : List (Event width)}
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width}
      {before middle : Cached} {queries : Queries} {symbol : Symbol}
      {staged : List Input} {residual : Option Constraint} {completed : List Fragment}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (children : ChildrenLedgerAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun finished current captured => consume (.stopped finished current captured))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.stopped completed observation candidate) localIndex path 0 events) :
      SelectedLedgerAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
        index output (.stopped completed observation candidate) localIndex path
        ([.prepare path scs edge caller before queries (some [((symbol, staged, residual), middle)])] ++ events)
end

theorem selected_ledger_first_preparation
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (policy : Policy) (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
    (index consumerIndex : Nat) (output : Output) (receipt : Receipt width)
    (path : List Nat) (events : List (Event width))
    (ledger : SelectedLedgerAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
      index output receipt consumerIndex path events) :
    ∃ rows, events.head? = some (.prepare path scs edge caller before queries rows) ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = rows
 := by
  cases ledger <;> exact ⟨_, rfl, by assumption⟩

end MicroCFTA.SourcePruningEnumerationInvocationEventLedger
