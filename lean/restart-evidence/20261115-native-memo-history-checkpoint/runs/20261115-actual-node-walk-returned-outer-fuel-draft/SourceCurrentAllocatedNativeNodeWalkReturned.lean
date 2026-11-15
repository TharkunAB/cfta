import MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyReturned
import MicroCFTA.SourceRecursiveIntersectionCompile

/-!
# Returned cache laws through actual node row and union walks

The first child can use the full remaining body budget.
Each child descends from the original outer node-query budget.
Actual outer prefixes retain the body finish continuation.
All supplied-fuel endpoints retain both existing Returned laws.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeWalkReturned
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open IntersectionFlatMemoKeyDomain (DomainKey)
open SourceRecursiveIntersectionKernel (pairs)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "RowPair" => EdgeValue Symbol Guard × EdgeValue Symbol Guard
variable {width : Nat} {Item Answer : Type}

set_option autoImplicit false

private theorem work_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (job : Work Symbol Guard (Value Symbol Guard)) (state : Checked width)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (fuel : Nat) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel (.code (.work job .pure)) state).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute fuel (.code (.work job .pure)) state).state.native.edges := by
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      let built := run job state.native.machine.heap
      let after : Checked width :=
        ⟨advance state.native {state.native.machine with heap := built.2}, state.operations⟩
      have one : SourceEqualityNativeDemand.step (.code (.work job .pure)) state =
          .yielded (.code (.pure built.1)) after := by rfl
      have endpoint : (SourceEqualityNativeDemand.execute (fuel + 1)
          (.code (.work job .pure)) state).state = after := by
        rw [SourceEqualityNativeDemand.execute, one]
        cases fuel <;> rfl
      rw [endpoint]
      exact ⟨nodes, edges⟩

private theorem walk_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (parent : NodeRequest Symbol Guard) (original : Checked width) (outerFuel : Nat)
    (call : Item → Code Symbol Guard Answer) (allJobs jobs : List Item)
    (before : Checked width) (remaining stepsBefore : Nat)
    (build : List Answer → Work Symbol Guard (Value Symbol Guard))
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (origin : Steps stepsBefore (.code (.node parent .pure)) original
      (.code (((SourceRecursiveIntersectionCode.walk call jobs).bind
        (fun values => .work (build values) .pure)).bind finishNext)) before)
    (positive : 0 < stepsBefore) (bounded : stepsBefore + remaining ≤ outerFuel)
    (included : ∀ item ∈ jobs, item ∈ allJobs)
    (nodes : Returned nodeLaw before.native.nodes) (edges : Returned edgeLaw before.native.edges)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore →
      stepsBefore + childFuel ≤ outerFuel → childFuel < outerFuel →
      ∀ item ∈ allJobs,
      ∀ (next : Answer → Code Symbol Guard (Value Symbol Guard)) (first : Checked width),
      Steps stepsBefore (.code (.node parent .pure)) original
        (.code ((call item).bind next)) first →
      Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel (.code (call item)) first).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel (.code (call item)) first).state.native.edges) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute remaining
      (.code ((SourceRecursiveIntersectionCode.walk call jobs).bind
        (fun values => .work (build values) .pure))) before).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute remaining
      (.code ((SourceRecursiveIntersectionCode.walk call jobs).bind
        (fun values => .work (build values) .pure))) before).state.native.edges := by
  induction jobs generalizing before remaining stepsBefore build with
  | nil =>
      simpa only [SourceRecursiveIntersectionCode.walk, Code.bind] using
        work_returned nodeLaw edgeLaw (build []) before nodes edges remaining
  | cons item rest ih =>
      let next : Answer → Code Symbol Guard (Value Symbol Guard) := fun value =>
        (SourceRecursiveIntersectionCode.walk call rest).bind
          (fun values => .work (build (value :: values)) .pure)
      let lifted : Answer → Code Symbol Guard (Value Symbol Guard) :=
        fun value => (next value).bind finishNext
      have sameCode : (SourceRecursiveIntersectionCode.walk call (item :: rest)).bind
          (fun values => .work (build values) .pure) = (call item).bind next := by
        simp only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, next]
      have atChild : Steps stepsBefore (.code (.node parent .pure)) original
          (.code ((call item).bind lifted)) before := by
        simpa only [sameCode, Code.bind_assoc, lifted] using origin
      rw [sameCode]
      rcases SourceCurrentAllocatedNativeEdgeBodyReturned.bind_endpoint_state_cases
          remaining (.code (call item)) next before with
        same | ⟨steps, value, middle, shorter, called, same⟩
      · simp only [Control.bind] at same
        rw [same]
        exact children stepsBefore remaining positive bounded (by omega)
          item (included item List.mem_cons_self) lifted before atChild nodes edges
      · simp only [Control.bind] at same
        have completed := trace_done steps _ before middle value called
        have atMiddle := children stepsBefore (steps + 1) positive (by omega) (by omega)
          item (included item List.mem_cons_self) lifted before atChild nodes edges
        rw [completed] at atMiddle
        have advanced := called.bind _ _ _ _ _ lifted
        have tailOrigin : Steps (stepsBefore + steps) (.code (.node parent .pure)) original
            (.code (((SourceRecursiveIntersectionCode.walk call rest).bind
              (fun values => .work (build (value :: values)) .pure)).bind finishNext)) middle :=
          atChild.trans _ _ _ _ _ _ _ _ advanced
        have restIncluded : ∀ candidate ∈ rest, candidate ∈ allJobs := by
          intro candidate member
          exact included candidate (List.mem_cons_of_mem _ member)
        have later := ih middle (remaining - steps) (stepsBefore + steps)
          (fun values => build (value :: values)) tailOrigin (by omega) (by omega)
          restIncluded atMiddle.1 atMiddle.2
        rw [same]
        exact later

/-- Actual row-body endpoints preserve both laws using child induction at the original outer query fuel. -/
theorem compile_rows_returned_all_fuels
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (parent : NodeRequest Symbol Guard) (original : Checked width) (outerFuel : Nat)
    (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (bodyState : Checked width) (bodyFuel : Nat)
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (entered : Steps 1 (.code (.node parent .pure)) original
      (.code ((compileRows domain left right).bind finishNext)) bodyState)
    (smaller : bodyFuel < outerFuel)
    (nodes : Returned nodeLaw bodyState.native.nodes) (edges : Returned edgeLaw bodyState.native.edges)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore →
      stepsBefore + childFuel ≤ outerFuel → childFuel < outerFuel →
      ∀ pair ∈ pairs left right,
      ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (first : Checked width),
      Steps stepsBefore (.code (.node parent .pure)) original
        (.code ((requestEdge domain pair.1 pair.2).bind next)) first →
      Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestEdge domain pair.1 pair.2)) first).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestEdge domain pair.1 pair.2)) first).state.native.edges) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute bodyFuel
      (.code (compileRows domain left right)) bodyState).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute bodyFuel
      (.code (compileRows domain left right)) bodyState).state.native.edges := by
  simpa only [compileRows] using walk_returned nodeLaw edgeLaw parent original outerFuel
    (fun pair : RowPair => requestEdge domain pair.1 pair.2) (pairs left right) (pairs left right)
    bodyState bodyFuel 1 makeNode finishNext entered (by decide) (by omega)
    (by intro pair member; exact member) nodes edges children

/-- Either actual union-member walk preserves both laws at every body fuel under the original query budget. -/
theorem union_walk_returned_all_fuels
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (parent : NodeRequest Symbol Guard) (original : Checked width) (outerFuel : Nat)
    (domain : Interned DomainKey) (members : List (Value Symbol Guard)) (other : Value Symbol Guard) (onLeft : Bool)
    (bodyState : Checked width) (bodyFuel : Nat)
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (entered : Steps 1 (.code (.node parent .pure)) original
      (.code (((SourceRecursiveIntersectionCode.walk
        (fun member => if onLeft then requestNode domain member other else requestNode domain other member) members).bind
        (fun values => .work (makeUnion values) .pure)).bind finishNext)) bodyState)
    (smaller : bodyFuel < outerFuel)
    (nodes : Returned nodeLaw bodyState.native.nodes) (edges : Returned edgeLaw bodyState.native.edges)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore →
      stepsBefore + childFuel ≤ outerFuel → childFuel < outerFuel →
      ∀ member ∈ members,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (first : Checked width),
      Steps stepsBefore (.code (.node parent .pure)) original
        (.code ((if onLeft then requestNode domain member other else requestNode domain other member).bind next)) first →
      Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (if onLeft then requestNode domain member other else requestNode domain other member)) first).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (if onLeft then requestNode domain member other else requestNode domain other member)) first).state.native.edges) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute bodyFuel
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun member => if onLeft then requestNode domain member other else requestNode domain other member) members).bind
        (fun values => .work (makeUnion values) .pure))) bodyState).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute bodyFuel
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun member => if onLeft then requestNode domain member other else requestNode domain other member) members).bind
        (fun values => .work (makeUnion values) .pure))) bodyState).state.native.edges := by
  exact walk_returned nodeLaw edgeLaw parent original outerFuel
    (fun member => if onLeft then requestNode domain member other else requestNode domain other member)
    members members bodyState bodyFuel 1 makeUnion finishNext entered (by decide) (by omega)
    (by intro member included; exact included) nodes edges children

end MicroCFTA.SourceCurrentAllocatedNativeNodeWalkReturned
