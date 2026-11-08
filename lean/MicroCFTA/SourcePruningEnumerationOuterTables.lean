import MicroCFTA.SourcePruningEnumerationSelectedStep
import MicroCFTA.SourcePruningEnumerationFold
import MicroCFTA.SourceCurrentOuterEdgeIdle

/-!
# Exact outer tables through enumeration queries

Incoming merges execute native requestNode and the tuple Empty check.
Selected narrowing changes the constructor heap. These operations retain
both complete outer result tables, including on failed observations.
The ordered source fold retains the same tables after every prefix.

These laws do not assume caller validity or successful execution. They do
not claim preservation by an arbitrary continuation hook. Full recursive
driver endpoint transport and native demand correspondence are separate.
-/
namespace MicroCFTA.SourcePruningEnumerationOuterTables
local notation "Caller" => SourceCurrentAllocatedPartialState.State

/-- Both complete outer result tables remain equal to their entry tables. -/
def Same (before after : Caller width) : Prop :=
  after.nodeResults = before.nodeResults ∧ after.edgeResults = before.edgeResults

/-- An unchanged caller retains both tables. -/
theorem Same.refl (before : Caller width) : Same before before := ⟨rfl, rfl⟩

/-- Exact table equality composes in execution order. -/
theorem Same.trans {before middle after : Caller width}
    (first : Same before middle) (last : Same middle after) : Same before after :=
  ⟨last.1.trans first.1, last.2.trans first.2⟩

/-- Exact edge-table equality retains the existing idle predicate. -/
theorem Same.edge_idle {before after : Caller width}
    (same : Same before after) (idle : SourceCurrentOuterEdgeIdle.EdgeIdle before) :
    SourceCurrentOuterEdgeIdle.EdgeIdle after := by
  intro handle owner found
  rw [same.2] at found
  exact idle handle owner found

end MicroCFTA.SourcePruningEnumerationOuterTables

namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationOuterTables (Same)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Every raw incoming outcome retains both complete outer result tables. -/
theorem run_tables (checkEmpty : Bool) (r n p h : Nat)
    (caller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    Same caller (run checkEmpty r n p h caller before target incoming incomingScs queries).2.1 := by
  unfold run
  repeat' first
    | exact ⟨rfl, rfl⟩
    | split
    | (dsimp only; split)

/-- Every incoming success, rejection and failure retains outer edge idle. -/
theorem run_edge_idle (checkEmpty : Bool) (r n p h : Nat)
    (caller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (idle : SourceCurrentOuterEdgeIdle.EdgeIdle caller) :
    SourceCurrentOuterEdgeIdle.EdgeIdle
      (run checkEmpty r n p h caller before target incoming incomingScs queries).2.1 :=
  (run_tables checkEmpty r n p h caller before target incoming incomingScs queries).edge_idle idle

end MicroCFTA.SourcePruningEnumerationIncomingNode

namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationOuterTables (Same)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Checked" => SourceEqualityNativeDemand.State
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem afterQuery_tables (checkEmpty : Bool) (p h source target : Nat)
    (sourceScs targetScs : List Suspended) (query : Node) (queried : Checked width)
    (caller : Caller width) (queries : Queries) :
    Same caller (afterQuery (EnumGuard := EnumGuard) checkEmpty p h source target
      sourceScs targetScs query queried caller queries).2.1 := by
  unfold afterQuery
  repeat' first
    | exact ⟨rfl, rfl⟩
    | split
    | (dsimp only; split)

/-- Every dispatcher outcome retains both tables, including native and tuple failure. -/
theorem dispatch_tables (checkEmpty : Bool) (n p h : Nat)
    (caller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) :
    Same caller (dispatch checkEmpty n p h caller before source target queries).2.1 := by
  unfold dispatch
  dsimp only
  repeat' first
    | exact ⟨rfl, rfl⟩
    | apply afterQuery_tables
    | split
    | (dsimp only; split)

/-- The actual dispatcher retains edge idle at every returned caller. -/
theorem dispatch_edge_idle (checkEmpty : Bool) (n p h : Nat)
    (caller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (idle : SourceCurrentOuterEdgeIdle.EdgeIdle caller) :
    SourceCurrentOuterEdgeIdle.EdgeIdle (dispatch checkEmpty n p h caller before source target queries).2.1 :=
  (dispatch_tables checkEmpty n p h caller before source target queries).edge_idle idle

end MicroCFTA.SourcePruningEnumerationDispatch

namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationOuterTables (Same)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Every literal ordered merge fold retains both tables at its exact stopping caller. -/
theorem run_tables (checkEmpty : Bool) (n p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries) :
    Same caller (run checkEmpty n p h sources caller before target queries).2.1 := by
  induction sources generalizing caller before queries with
  | nil => exact .refl _
  | cons source rest ih =>
      rcases observed : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
        caller before source target queries with ⟨result, reached, saved⟩
      have head := SourcePruningEnumerationDispatch.dispatch_tables
        checkEmpty n p h caller before source target queries
      rw [observed] at head
      dsimp only at head
      cases result with
      | error fault => simpa only [run, observed] using head
      | ok response =>
          cases response with
          | none => simpa only [run, observed] using head
          | some action =>
              simp only [run, observed]
              repeat' first
                | exact head
                | (apply Same.trans head; apply ih)
                | split
                | (dsimp only; split)

end MicroCFTA.SourcePruningEnumerationFold

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationOuterTables (Same)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every selected prefix with a native caller retains both complete entry tables. -/
theorem runPrefix_tables
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (r c n representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    match runPrefix holeKey fits admits graph templates stop order metadata
      r c n representativeFuel indexFuel callbackFuel uv caller before queries with
    | .narrowed _ _ after _ _ _ _ _ => Same caller after
    | _ => True := by
  generalize observed : runPrefix holeKey fits admits graph templates stop order metadata
    r c n representativeFuel indexFuel callbackFuel uv caller before queries = result
  cases result with
  | stopped => trivial
  | parked => trivial
  | narrowed =>
      unfold runPrefix at observed
      repeat' first
        | (cases observed <;> exact ⟨rfl, rfl⟩)
        | split at observed
        | (dsimp only at observed; split at observed)

end MicroCFTA.SourcePruningEnumerationSelectedStep
