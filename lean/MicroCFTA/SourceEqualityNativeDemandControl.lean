import MicroCFTA.SourceEqualityNativeDemand
import MicroCFTA.SourceRecursiveIntersectionNativeObservations

/-!
# Published edge bodies and delayed native continuations

Completed and busy hits retain the entire operation state. A miss keeps
the original completion handle in its demanded body. Missing field storage
retains that body for later evaluation. Actual original constructor receipts
supply finite ready or rejected continuations without another publication.
-/
namespace MicroCFTA.SourceEqualityNativeDemand
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- A completed native hit returns its complete value without any cache replay. -/
theorem edge_ready_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request original : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (handle : Nat) (value : EdgeValue Symbol Guard)
    (linked : state.native.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = some handle)
    (returned : state.native.edges.cells handle = some ⟨original, .returned value⟩) :
    step (.code (.edge request next)) state = .yielded (.code (next value)) state := by
  simp only [step, lookupEdge, FlatMemoThunk.lookupOrInsert, linked, demandEdge, FlatMemoThunk.demand, returned]

/-- A busy hit retains its original request continuation and the entire actual state. -/
theorem edge_busy_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request original : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (handle : Nat)
    (linked : state.native.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = some handle)
    (running : state.native.edges.cells handle = some ⟨original, .evaluating⟩) :
    step (.code (.edge request next)) state = .blocked (.native (.edgeBusy handle)) (.code (.edge request next)) state := by
  simp only [step, lookupEdge, FlatMemoThunk.lookupOrInsert, linked, demandEdge, FlatMemoThunk.demand, running]

/-- Starting the actual published edge retains its original finish handle before checking the body. -/
theorem edge_evaluate [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request actual : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (handle : Nat) (chosen current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (selected : lookupEdge width request state.native = (handle, chosen))
    (started : demandEdge handle chosen = (.evaluate actual, current)) :
    step (.code (.edge request next)) state =
      .yielded (.edgeBody actual (fun value => .finishEdge handle value (next value))) {state with native := current} := by
  simp only [step, selected, started]

/-- Unavailable original storage retains the already demanded body, without a second lookup. -/
theorem body_missing_left (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (arity : request.left.children.length = request.right.children.length)
    (missing : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok none) :
    body request next state = .blocked (.missingField request.left.entry.key.constraint) (.edgeBody request next) state := by
  unfold body
  rw [ite_eq_right (not_not_intro arity), missing]

/-- Actual rejection creates only sentinel code and retains every reached equality allocation. -/
theorem body_rejected (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (arity : request.left.children.length = request.right.children.length) (first second : Allocated)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected) :
    body request next state = sentinel request next
      {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length state.operations).2} := by
  unfold body
  rw [ite_eq_right (not_not_intro arity), left, right]
  simp only [rejected]

/-- Only an actual ready combined constraint creates the ordered child request code. -/
theorem body_ready (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (arity : request.left.children.length = request.right.children.length) (first second combined : Allocated)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (ready : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined)) :
    body request next state =
      .yielded (.code ((SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined).bind next))
        {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length state.operations).2} := by
  unfold body
  rw [ite_eq_right (not_not_intro arity), left, right]
  simp only [ready]

/-- Normalized fields already in storage give a finite continuation without a semantic answer oracle. -/
theorem body_complete (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (first second : Allocated)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second)) :
    ∃ code after, body request next state = .yielded (.code code) {state with operations := after} := by
  by_cases mismatch : request.left.children.length ≠ request.right.children.length
  · rw [body_mismatch request next state mismatch]
    exact ⟨_, _, rfl⟩
  · have arity := Classical.not_not.mp mismatch
    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints leftCached first left).1
    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints rightCached second right).1
    obtain ⟨branch, completed, _, _, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le
      first second request.left.children.length request.right.children.length state.operations valid firstReady secondReady
    unfold body
    rw [ite_eq_right mismatch, left, right]
    cases branch <;> simp only [completed] <;> exact ⟨_, _, rfl⟩

/-- Actual earlier field constructors and retained canonical tables discharge both original lookups. -/
theorem body_of_constructed (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (leftBefore leftAfter rightBefore rightAfter : Cache.State SourceEqualityPartialConstraintKey.Key)
    (leftValid : Cache.Valid leftBefore) (rightValid : Cache.Valid rightBefore)
    (first second : SourceEqualityConstraintAllocation.Value)
    (left : SourceEqualityConstraintAllocation.construct request.left.entry.key.constraint.equalities leftBefore = (.ok first, leftAfter))
    (right : SourceEqualityConstraintAllocation.construct request.right.entry.key.constraint.equalities rightBefore = (.ok second, rightAfter))
    (leftGrows : Cache.Extends leftAfter.table state.operations.constraints.table)
    (rightGrows : Cache.Extends rightAfter.table state.operations.constraints.table) :
    ∃ code after, body request next state = .yielded (.code code) {state with operations := after} := by
  have loadedLeft := (SourceEqualityConstraintFieldLookup.load_of_construct_grows _ leftCached leftBefore leftValid
    first leftAfter state.operations.constraints left leftGrows).1
  have loadedRight := (SourceEqualityConstraintFieldLookup.load_of_construct_grows _ rightCached rightBefore rightValid
    second rightAfter state.operations.constraints right rightGrows).1
  exact body_complete request next state valid leftCached rightCached _ _ loadedLeft loadedRight

end MicroCFTA.SourceEqualityNativeDemand
