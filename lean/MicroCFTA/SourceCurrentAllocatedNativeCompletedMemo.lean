import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceEqualityNativeDemandNodeReadback
import MicroCFTA.SourceEqualityNativeDemandRunning
import MicroCFTA.SourceEqualityNativeDemandMemo

/-!
# Returned memo cells from actual completed checked requests

Actual completion identifies a ready hit or the protected original finish.
The literal request key remains published through the body. Repeating that
cacheable request returns its result with the whole checked state unchanged.
An unresolved key retains the direct-body path and has no warm-hit claim.
These observations do not assert GHC publication or machine-key capacity.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- Actual finite completion retains all earlier returned cells and published keys. -/
theorem done_retained [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (before after : Checked width) (value : Output)
    (shape : SourceRecursiveIntersectionNative.Shape before.native)
    (done : execute fuel control before = .done value after) :
    SourceEqualityNativeDemandMemo.Retained before.native after.native := by
  have retained := (SourceEqualityNativeDemandMemo.execute_preserves fuel control before shape).2
  simpa only [done, Outcome.state] using retained

/-- A cacheable completed request derives its literal publication and exact returned original cell. -/
theorem completed_node [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done value after) :
    ∃ handle, after.native.nodes.table key = some handle ∧
      after.native.nodes.cells handle = some ⟨request, .returned value⟩ := by
  obtain ⟨_, _, actual⟩ := SourceEqualityNativeDemandNodeReadback.of_done fuel request before after value done
  cases actual with
  | direct count after value unresolved body => rw [unresolved] at requested; cases requested
  | ready actualKey handle original value found published returned =>
      have sameKey : actualKey = key := Option.some.inj (found.symm.trans requested)
      subst actualKey
      have same := SourceCurrentAllocatedNativePhysicalCache.node_request_exact before.native valid request ready key
        ⟨requested, safe⟩ handle published _ returned
      change original = request at same
      exact ⟨handle, published, same ▸ returned⟩
  | started count handle chosen running original middle value selected demanded suspended evaluating machine body =>
      have same := SourceCurrentAllocatedNativePhysicalCache.node_started request original before.native chosen running handle
        valid ready safe selected demanded
      subst original
      obtain ⟨actualKey, found, published, _⟩ :=
        SourceRecursiveIntersectionNative.lookupNode_memoized request before.native chosen handle selected
      have sameKey : actualKey = key := Option.some.inj (found.symm.trans requested)
      subst actualKey
      have chosenShape : SourceRecursiveIntersectionNative.Shape chosen := by
        simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_shape request before.native valid.shape
      have runningShape : SourceRecursiveIntersectionNative.Shape running := by
        simpa only [demanded] using SourceRecursiveIntersectionNative.demandNode_shape handle chosen chosenShape
      have demandedKeys := (SourceEqualityNativeDemandMemo.demandNode_retained handle chosen).nodeKeys key handle published
      have runningKeys : running.nodes.table key = some handle := by simpa only [demanded] using demandedKeys
      have bodyDone := trace_done count (.code (compileNode request)) ⟨running, before.operations⟩ middle value body
      have bodyRetention := done_retained (count + 1) (.code (compileNode request))
        ⟨running, before.operations⟩ middle value runningShape bodyDone
      have middleKeys := bodyRetention.nodeKeys key handle runningKeys
      have finalKeys := (SourceEqualityNativeDemandMemo.finishNode_retained handle value middle.native).nodeKeys key handle middleKeys
      have finalCell := (SourceEqualityNativeDemandRunning.node_body_cell (count + 1) handle request
        ⟨running, before.operations⟩ middle value runningShape evaluating bodyDone).2
      exact ⟨handle, finalKeys, finalCell⟩

/-- A literal returned cell gives an exact two-step warm return with no checked-state effects. -/
theorem warm_node [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Checked width) (value : Value Symbol Guard)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (handle : Nat)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (published : state.native.nodes.table key = some handle)
    (returned : state.native.nodes.cells handle = some ⟨request, .returned value⟩) :
    execute 2 (.code (requestNode request.domain request.left request.right)) state = .done value state := by
  have selected : lookupNode width request state.native = (.memoized handle, state.native) := by
    simp only [lookupNode, requested, FlatMemoThunk.lookupOrInsert, published]
  have demanded : demandNode handle state.native = (.ready value, state.native) := by
    simp only [demandNode, FlatMemoThunk.demand, returned]
  simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, requestNode,
    SourceRecursiveIntersectionNative.step, selected, demanded, lift]

/-- Actual cacheable completion derives a later unchanged warm return without a supplied final cell. -/
theorem completed_repeat [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done value after) :
    (∃ handle, after.native.nodes.table key = some handle ∧
      after.native.nodes.cells handle = some ⟨request, .returned value⟩) ∧
      execute 2 (.code (requestNode request.domain request.left request.right)) after = .done value after := by
  obtain ⟨handle, published, returned⟩ := completed_node fuel request before after value valid ready safe key requested done
  exact ⟨⟨handle, published, returned⟩, warm_node request after value key handle requested published returned⟩

/-- An unresolved root key bypasses publication and retains only its actual direct body trace. -/
theorem uncacheable_call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (unresolved : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done value after) :
    lookupNode width request before.native = (.direct request, before.native) ∧
      ∃ count, count + 1 < fuel ∧
        Steps count (.code (compileNode request)) before (.code (.pure value)) after := by
  refine ⟨lookupNode_bypass width request before.native unresolved, ?_⟩
  obtain ⟨_, bounded, actual⟩ := SourceEqualityNativeDemandNodeReadback.of_done fuel request before after value done
  cases actual with
  | direct count after value _ body => exact ⟨count, bounded, body⟩
  | ready key handle original value requested published returned => rw [unresolved] at requested; cases requested
  | started count handle chosen running original middle value selected demanded suspended evaluating machine body =>
      simp only [lookupNode, unresolved] at selected
      cases selected

/-- Completed calls either take the direct path or derive a literal final memo cell. -/
theorem completed_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : NodeReady before.native.machine request)
    (safe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done value after) :
    (SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none ∧
      ∃ count, count + 1 < fuel ∧ Steps count (.code (compileNode request)) before (.code (.pure value)) after) ∨
    (∃ key handle, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key ∧
      after.native.nodes.table key = some handle ∧ after.native.nodes.cells handle = some ⟨request, .returned value⟩ ∧
      execute 2 (.code (requestNode request.domain request.left request.right)) after = .done value after) := by
  cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => exact .inl ⟨rfl, (uncacheable_call fuel request before after value requested done).2⟩
  | some key =>
      obtain ⟨⟨handle, published, returned⟩, repeated⟩ := completed_repeat fuel request before after value valid ready
        (safe key requested) key requested done
      exact .inr ⟨key, handle, rfl, published, returned, repeated⟩

/-- A completed physical trace derives initial key checks and the unchanged warm return. -/
theorem repeat_of_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (count : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace count
      (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    (∃ handle, after.native.nodes.table key = some handle ∧
      after.native.nodes.cells handle = some ⟨request, .returned value⟩) ∧
      execute 2 (.code (requestNode request.domain request.left request.right)) after = .done value after := by
  have done := trace_done count _ before after value trace.steps
  cases trace with
  | cons _ _ next current _ _ rest inputs one tail =>
      exact completed_repeat (rest + 2) request before after value valid inputs.1
        (inputs.2 key requested) key requested done

end MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
