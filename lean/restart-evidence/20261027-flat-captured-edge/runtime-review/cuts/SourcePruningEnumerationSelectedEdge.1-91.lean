import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.SourcePruningEnumerationTraversalCompletion

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

/-- Retain prefix rejection, unsupported preparation, stopped children and a completed edge. -/
inductive Result (width : Nat) where
  /-- The prefix does not supply the supported singleton packet. -/
  | unhandled
  /-- The arity check rejects before any child runs. -/
  | rejected (caller : Caller width) (queries : Queries) (after : Cached)
  /-- Retain the exact first stopping child observation and optional cache. -/
  | stopped (completedPrefix : List Fragment)
      (observation : SourcePruningEnumerationChildDispatch.Observation width) (candidate : Option Cached)
  /-- Every child succeeds and the edge residual is recorded. -/
  | complete (fragment : Fragment) (caller : Caller width) (queries : Queries) (after : Cached)

/-- Record the residual in the actual completed cache. -/
def finish (residual : Option Constraint) (fragment : Fragment) (before : Cached) : Cached :=
  EnumerationExpandableIndex.frame {before.core with obligations :=
    match residual with
    | none => before.core.obligations
    | some guard => (guard, fragment) :: before.core.obligations} before

/-- Residual recording has exactly the source action's successful singleton result. -/
theorem finish_raw (residual : Option Constraint) (fragment : Fragment) (before : Cached) :
    ExceptT.run (recordResidual residual fragment before.core) = [.ok ((), (finish residual fragment before).core)] := by
  cases residual <;> rfl

/-- A bounded completed fragment permits the exact residual update. -/
theorem finish_safe (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (safe : Safe before.core) (bounded : FragmentBound before.core.counter fragment) :
    Safe (finish residual fragment before).core := by
  apply (recordResidual_safe residual fragment before.core _ safe bounded ?_).1
  rw [Success, finish_raw]
  simp

/-- Residual recording retains every existing root, its stored value and its class. -/
theorem finish_protected (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (held : Nat) (root : IsRoot before.core.representatives held) :
    EnumerationDriver.Protected held before.core (finish residual fragment before).core :=
  ⟨rfl, root, fun _ => Iff.rfl⟩

private theorem node_bound (limit : Nat) (symbol : Symbol) (fragments : List Fragment)
    (bounded : ∀ fragment ∈ fragments, FragmentBound limit fragment) :
    FragmentBound limit (.node symbol fragments) := by
  induction fragments with
  | nil => trivial
  | cons first rest ih =>
      exact ⟨bounded first (by simp), ih (fun fragment member => bounded fragment (by simp [member]))⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Run the actual own-class prefix, ordered native children and final residual update. -/
noncomputable def run (checkEmpty : Bool) (r n p h k : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Result width :=
  match SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => .unhandled
  | some [] => .rejected caller queries before
  | some [((symbol, staged, residual), middle)] =>
      match SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
          (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
      | .stopped fragments observation candidate => .stopped fragments observation candidate
      | .complete fragments afterCaller saved after =>
          let fragment := Fragments.Fragment.node symbol fragments
          .complete fragment afterCaller saved (finish residual fragment after)
  | _ => .unhandled

/-- Numeric admission is required at the actual successful own-class prefix endpoint. -/
def Ranges (checkEmpty : Bool) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Prop :=
  ∀ symbol staged residual middle,
    SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((symbol, staged, residual), middle)] →
    SourcePruningEnumerationTraversalCompletion.Ranges checkEmpty
      (staged.map (fun input => (input.1, input.2.1))) caller middle queries
