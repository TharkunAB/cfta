import MicroCFTA.SourceEqualityPartialConstraintKey
import MicroCFTA.SourceEqualityPartialWorker
import MicroCFTA.FlatMemoThunkRunning

/-!
# Recursive partial reduction with published result thunks

The request key contains the inherited constraint identity and node reference.
The worker publishes a request before it executes the body. Child calls and
rows retain the returned native state, constraint interner, and result memo.
Busy cells, source errors, and exhausted bounds remain distinct observations.
This is a sequential demand adapter. It does not specify GHC scheduling.
-/
namespace MicroCFTA.SourceEqualityPartialMemoWorker
open Cache InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- A result-memo key retains both source equality identities. -/
abbrev Key := Option Nat × InternedBinderProtocol.NodeRef

/-- A published thunk retains the complete original arguments. -/
structure Request where
  inherited : SourceEqualityPrecheck.Constraint
  value : Value Symbol Guard

/-- The result memo stores complete source node values. -/
abbrev Memo := FlatMemoThunk.State Key Request (Value Symbol Guard)

/-- Every recursive continuation carries all three mutable source components. -/
structure State (width : Nat) : Type 1 where
  native : NativeState width Symbol Guard
  constraints : Cache.State SourceEqualityPartialConstraintKey.Key
  memo : Memo

/-- Unfinished execution retains its actual reason and the current memo state. -/
inductive Observation (width : Nat) : Type 1 where
  | exhausted (request : Request) (handle : Nat) (state : State width)
  | busy (key : Key) (handle : Nat) (state : State width)
  | absent (key : Key) (handle : Nat) (state : State width)
  | guarded (observation : SourceEqualityGuardedEdgeWorker.Result width FullSyntax.Formula)
      (constraints : Cache.State SourceEqualityPartialConstraintKey.Key) (memo : Memo)
  | pending (key : InternedBinderProtocol.NodeKey) (state : State width)

/-- Successful answers and source errors retain the complete returned state. -/
inductive Result (width : Nat) (Output : Type) : Type 1 where
  | done (answer : Except String Output) (state : State width)
  | incomplete (observation : Observation width)

/-- Continue a successful result without changing errors or unfinished observations. -/
def Result.bind (first : Result width First)
    (next : First → State width → Result width Output) : Result width Output :=
  match first with
  | .done (.ok value) state => next value state
  | .done (.error message) state => .done (.error message) state
  | .incomplete observation => .incomplete observation

/-- The initial result memo and constraint interner contain no entries. -/
def initial (native : NativeState width Symbol Guard) : State width :=
  ⟨native, Cache.emptyState, FlatMemoThunk.empty⟩

/-- Request preparation interns the physical constraint payload before memo lookup. -/
def prepare (request : Request) (before : State width) : Key × State width :=
  let found := SourceEqualityPartialConstraintKey.identify request.inherited before.constraints
  ((found.1, request.value.referenceOf), { before with constraints := found.2 })

/-- Indexed source child traversal threads both memo tables and native effects. -/
def childrenWalk (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard))
    (payload : SourceEqualityPrecheck.Constraint) : Nat → List (Value Symbol Guard) → State width → Result width (List (Value Symbol Guard))
  | _, [], state => .done (.ok []) state
  | index, value :: values, state =>
      (call (SourceEqualityDescend.descend payload index) value state).bind fun result middle =>
        (childrenWalk call payload (index + 1) values middle).bind fun results after => .done (.ok (result :: results)) after

/-- Contradiction produces an equally sized empty forest without recursive requests. -/
def children (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard))
    (payload : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (before : State width) : Result width (List (Value Symbol Guard)) :=
  match payload with
  | none => .done (.ok (values.map (fun _ => .empty))) before
  | some records => childrenWalk call (some records) 0 values before

/-- Inherited child processing uses the complete physical guard and original edge labels. -/
noncomputable def descendants [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard))
    (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : State width) : Result width (EdgeValue Symbol Guard) :=
  match SourceEqualityPhysicalPayload.own edge.entry.key.constraint with
  | .error message => .done (.error message) before
  | .ok own => match SourceEqualityInheritedPayload.combine inherited own with
    | .error message => .done (.error message) before
    | .ok payload => (children call payload edge.children before).bind fun values middle =>
        let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap
        .done (.ok built.1) { middle with native := advanceHeap middle.native built.2 }

/-- The existing native narrowing worker precedes inherited recursive requests. -/
noncomputable def edge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard))
    (g e p h c n : Nat) (value : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : State width) : Result width (EdgeValue Symbol Guard) :=
  match SourceEqualityGuardedEdgeWorker.run SourceMemoGate.unconstrained SourceEqualityConstraintConstructors.top
      SourceEqualityPCSNativeEdge.conjoin SourceMemoGate.plain SourceEqualityConstraintConstructors.top g e p h c n value inherited before.native with
  | .done (.ok narrowed) middle => descendants call narrowed inherited { before with native := middle }
  | .done (.error message) middle => .done (.error message) { before with native := middle }
  | observation => .incomplete (.guarded observation before.constraints before.memo)

/-- Ordered rows retain every completed row's full returned state. -/
noncomputable def rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard))
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) : List (EdgeValue Symbol Guard) → State width → Result width (List (EdgeValue Symbol Guard))
  | [], before => .done (.ok []) before
  | value :: values, before =>
      (edge call g e p h c n value inherited before).bind fun result middle =>
        (rows call g e p h c n inherited values middle).bind fun results after => .done (.ok (result :: results)) after

/-- Execute the source body after publication and demand of its result thunk. -/
noncomputable def step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard))
    (g e p h c n : Nat) (request : Request) (before : State width) : Result width (Value Symbol Guard) :=
  match request.value with
  | .empty => .done (.ok .empty) before
  | .reference _ => .done (.error "reducePartially: unexpected Rec") before
  | .union .. => .done (.ok request.value) before
  | .mu entry body depth ordinary =>
      match SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.native.machine.heap with
      | .done result heap => .done (.ok result) { before with native := advanceHeap before.native heap }
      | .pending key heap => .incomplete (.pending key { before with native := advanceHeap before.native heap })
  | .node entry edges depth free =>
      (rows call g e p h c n request.inherited edges before).bind fun results middle =>
        let built := SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle.native
        .done (.ok built.1) { middle with native := built.2 }

/-- Only a successful source body completes a result thunk. -/
def finish (handle : Nat) (result : Result width (Value Symbol Guard)) : Result width (Value Symbol Guard) :=
  match result with
  | .done (.ok value) after => .done (.ok value) { after with memo := FlatMemoThunk.finish handle value after.memo }
  | .done (.error message) after => .done (.error message) after
  | .incomplete observation => .incomplete observation

/-- Publish and demand the original request before invoking its bounded body. -/
noncomputable def request (body : Nat → Request → State width → Result width (Value Symbol Guard))
    (candidate : Request) (before : State width) : Result width (Value Symbol Guard) :=
  let prepared := prepare candidate before
  let published := FlatMemoThunk.lookupOrInsert prepared.1 candidate prepared.2.memo
  let demanded := FlatMemoThunk.demand published.1 published.2
  let running := { prepared.2 with memo := demanded.2 }
  match demanded.1 with
  | .absent => .incomplete (.absent prepared.1 published.1 running)
  | .busy => .incomplete (.busy prepared.1 published.1 running)
  | .ready value => .done (.ok value) running
  | .evaluate original => finish published.1 (body published.1 original running)

/-- Bounds limit new body evaluation. Existing completed hits require no body bound. -/
noncomputable def run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (g e p h c n : Nat) : Nat → SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard)
  | 0, inherited, value, before => request (fun handle original running =>
      .incomplete (.exhausted original handle running)) ⟨inherited, value⟩ before
  | fuel + 1, inherited, value, before => request (fun _ => step (run g e p h c n fuel) g e p h c n) ⟨inherited, value⟩ before

/-- A source error does not become a successful cached node. -/
theorem finish_error (handle : Nat) (message : String) (after : State width) :
    finish handle (.done (.error message) after) = .done (.error message) after := rfl

/-- An unfinished source observation is preserved without a completion update. -/
theorem finish_incomplete (handle : Nat) (observation : Observation width) :
    finish handle (.incomplete observation) = .incomplete observation := rfl

/-- Contradiction bypasses all child requests and leaves every state component unchanged. -/
theorem children_contradiction (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard))
    (values : List (Value Symbol Guard)) (before : State width) :
    children call none values before = .done (.ok (values.map (fun _ => .empty))) before := rfl

/-- A completed hit returns the stored value without invoking the supplied body. -/
theorem request_ready (body : Nat → Request → State width → Result width (Value Symbol Guard))
    (candidate original : Request) (before prepared : State width) (key : Key) (handle : Nat) (value : Value Symbol Guard)
    (preparation : prepare candidate before = (key, prepared))
    (published : prepared.memo.table key = some handle)
    (returned : prepared.memo.cells handle = some ⟨original, .returned value⟩) :
    request body candidate before = .done (.ok value) prepared := by
  simp only [request, preparation, FlatMemoThunk.lookup_hit key candidate prepared.memo handle published,
    FlatMemoThunk.demand_ready handle prepared.memo original value returned]

/-- A running hit retains the actual key and handle without invoking the body. -/
theorem request_busy (body : Nat → Request → State width → Result width (Value Symbol Guard))
    (candidate original : Request) (before prepared : State width) (key : Key) (handle : Nat)
    (preparation : prepare candidate before = (key, prepared))
    (published : prepared.memo.table key = some handle)
    (running : prepared.memo.cells handle = some ⟨original, .evaluating⟩) :
    request body candidate before = .incomplete (.busy key handle prepared) := by
  simp only [request, preparation, FlatMemoThunk.lookup_hit key candidate prepared.memo handle published,
    FlatMemoThunk.demand_busy handle prepared.memo original running]

end MicroCFTA.SourceEqualityPartialMemoWorker
