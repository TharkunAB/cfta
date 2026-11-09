import MicroCFTA.SourceCurrentSharedOuterInitialActual
import MicroCFTA.SourceCurrentSharedOuterInitialPrefix
import MicroCFTA.SourceCurrentSharedOuterInitialParentFailure
import MicroCFTA.SourceCurrentSharedOuterLocalFaults

/-!
# Initial resources at every adequately bounded shared outer return

The literal outcome retains its exact caller state. Successful siblings
supply their actual Post before the next phase starts. The initial lower
bounds exclude Parent faults. Outer exhaustion and memo diagnostics keep
the reached protocol state. One phase Room supplies the original forecast.
No whole-call success or future caller invariant is an input.
-/
namespace MicroCFTA.SourceCurrentSharedOuterInitialOutcomePost
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedSharedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentSharedOuterExecutionAncestry (Reached caller)
open SourceCurrentSharedOuterPrefixInvariants (Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
local notation "run" => SourceCurrentSharedOuterActiveAncestry.run
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def Returned (seed : Seed) (before after : Caller (bits+2)) : Prop :=
  ∃ next final, Post formulas solver next before after final ∧
    Frame formulas solver next after.checked ∧ Fits seed.2 after.checked ∧
    Carrier (fun guard => guard ∈ seed.1) after.checked.native.machine.heap

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem erased_state (observed : Outcome A (bits+2)) :
    (observed.bind (fun _ after => .done () after)).state = observed.state := by
  cases observed <;> rfl

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem erase_failed {observed : Outcome A (bits+2)}
    (failed : observed.bind (fun _ after => .done () after) = .failed fault after) :
    observed = .failed fault after := by
  cases observed <;> simp_all [Outcome.bind]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem erase_done {observed : Outcome A (bits+2)}
    (done : observed.bind (fun _ after => .done () after) = .done () after) :
    ∃ value, observed = .done value after := by
  cases observed with
  | failed => cases done
  | done value reached => cases done; exact ⟨value, rfl⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem bind_failed (first : Outcome A (bits+2))
    (next : A → Caller (bits+2) → Outcome B (bits+2))
    (failed : first.bind next = .failed fault after) :
    first = .failed fault after ∨
      ∃ value middle, first = .done value middle ∧ next value middle = .failed fault after := by
  cases first with
  | failed => simp only [Outcome.bind] at failed; cases failed; exact .inl rfl
  | done value middle => exact .inr ⟨value, middle, rfl, failed⟩

private theorem failed_return
    {g s r e p h m c n budget : Nat} {first : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2)
    (fault : Fault (bits+2)) (after : Caller (bits+2))
    (parentFree : ∀ observation, fault ≠ .parent observation)
    (failed : run g s r e p h m c n budget first = .failed fault after) :
    Returned formulas solver (forecast budget first seed) (caller first) after := by
  let resources := fun last (past : Reached g s r e p h m c n budget first last) =>
    SourceCurrentSharedOuterInitialPrefix.reached formulas solver seed past initial frame fits known inputs room
  have retained (last : Phase (bits+2)) (past : Reached g s r e p h m c n budget first last) :
      Returned formulas solver (forecast budget first seed) (caller first) (caller last) := by
    obtain ⟨next, final, current, trace, post, returned, numeric, carrier, ready,
      below, subset, currentRoom, rootFits, rootKnown, need⟩ := resources last past
    exact ⟨next, final, post, returned, rootFits, rootKnown⟩
  let nodeAt (fuel : Nat) : Prop := ∀ request before,
    Reached g s r e p h m c n budget first (.node fuel request before) → ∀ fault after,
      (∀ observation, fault ≠ .parent observation) →
      nodeCall fuel g s r e p h m c n budget request before = .failed fault after →
      Returned formulas solver (forecast budget first seed) (caller first) after
  let bodyAt (fuel : Nat) : Prop := ∀ request before,
    Reached g s r e p h m c n budget first (.body fuel request before) → ∀ fault after,
      (∀ observation, fault ≠ .parent observation) →
      nodeBody fuel g s r e p h m c n budget request before = .failed fault after →
      Returned formulas solver (forecast budget first seed) (caller first) after
  let rowsAt (fuel : Nat) : Prop := ∀ inherited originals before,
    Reached g s r e p h m c n budget first (.rows fuel inherited originals before) → ∀ fault after,
      (∀ observation, fault ≠ .parent observation) →
      rows fuel g s r e p h m c n budget inherited originals before = .failed fault after →
      Returned formulas solver (forecast budget first seed) (caller first) after
  let descendantsAt (fuel : Nat) : Prop := ∀ inherited edge before,
    Reached g s r e p h m c n budget first (.descendants fuel inherited edge before) → ∀ fault after,
      (∀ observation, fault ≠ .parent observation) →
      descendants fuel g s r e p h m c n budget inherited edge before = .failed fault after →
      Returned formulas solver (forecast budget first seed) (caller first) after
  let childrenAt (fuel : Nat) : Prop := ∀ combined values before,
    Reached g s r e p h m c n budget first (.children fuel combined values before) → ∀ fault after,
      (∀ observation, fault ≠ .parent observation) →
      children fuel g s r e p h m c n budget combined values before = .failed fault after →
      Returned formulas solver (forecast budget first seed) (caller first) after
  let walkAt (fuel : Nat) : Prop := ∀ combined index values before,
    Reached g s r e p h m c n budget first (.walk fuel combined index values before) → ∀ fault after,
      (∀ observation, fault ≠ .parent observation) →
      walk fuel g s r e p h m c n budget combined index values before = .failed fault after →
      Returned formulas solver (forecast budget first seed) (caller first) after
  have edgeReturn (fuel : Nat) (inherited : EqValue) (original : Edge) (rest : List Edge)
      (before : Caller (bits+2))
      (past : Reached g s r e p h m c n budget first (.rows (fuel+1) inherited (original::rest) before))
      fault after (parentFree : ∀ observation, fault ≠ .parent observation)
      (failed : edgeCall fuel g s r e p h m c n budget ⟨inherited,original⟩ before = .failed fault after) :
      Returned formulas solver (forecast budget first seed) (caller first) after := by
    rcases started : beginEdge ⟨inherited,original⟩ before with ⟨handle, action, running⟩
    cases action with
    | ready value => simp only [edgeCall, started] at failed; cases failed
    | busy | absent =>
      simp only [edgeCall, started] at failed
      cases failed
      obtain ⟨next, final, current, trace, post, returned, numeric, carrier, ready,
        below, subset, currentRoom, rootFits, rootKnown, need⟩ := resources _ past
      have sound := SourceCurrentAllocatedPartialMemoSound.beginEdge_sound formulas solver
        ⟨inherited,original⟩ before post.context.sound ready.1 (ready.2 original List.mem_cons_self)
      have components := beginEdge_components ⟨inherited,original⟩ before
      rw [started] at sound components
      dsimp only at sound components
      obtain ⟨checked, merge, fourth, _nodes⟩ := components
      exact ⟨next, final, post.trans (Post.rebase post.context checked merge fourth sound),
        (by simpa only [checked, caller] using returned), (by simpa only [checked, caller] using rootFits),
        (by simpa only [checked, caller] using rootKnown)⟩
    | evaluate owner =>
      simp only [edgeCall, started, edgeBody] at failed
      split at failed <;> simp only [Outcome.bind] at failed
      · cases failed
      · cases failed
        exact False.elim (parentFree _ rfl)
  have complete : ∀ fuel, nodeAt fuel ∧ bodyAt fuel ∧ rowsAt fuel ∧
      descendantsAt fuel ∧ childrenAt fuel ∧ walkAt fuel := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      have walkReturn : walkAt fuel := by
        intro combined index values before past fault after parentFree failed
        cases values with
        | nil => simp only [walk] at failed; cases failed
        | cons value rest =>
          cases fuel with
          | zero =>
            simp only [walk] at failed
            cases failed
            exact retained _ past
          | succ fuel =>
            simp only [walk] at failed
            rcases bind_failed _ _ failed with headFailed | ⟨head, middle, headDone, later⟩
            · exact (ih fuel (Nat.lt_succ_self _)).1 _ _ (past.snoc .walk_head) _ _ parentFree headFailed
            · rcases bind_failed _ _ later with tailFailed | ⟨outputs, final, tailDone, impossible⟩
              · exact (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 _ _ _ _
                  (past.snoc (.walk_tail headDone)) _ _ parentFree tailFailed
              · cases impossible
      have childrenReturn : childrenAt fuel := by
        intro combined values before past fault after parentFree failed
        cases combined with
        | contradiction => simp only [SourceCurrentAllocatedSharedPartialWorker.children] at failed; cases failed
        | live identity records =>
          simp only [SourceCurrentAllocatedSharedPartialWorker.children] at failed
          exact walkReturn _ _ _ _ (past.snoc (.children_walk (by intro impossible; cases impossible)))
            _ _ parentFree failed
      have descendantsReturn : descendantsAt fuel := by
        intro inherited edge before past fault after parentFree failed
        obtain ⟨next, final, current, trace, post, numeric, fits, known, ready, rest⟩ := resources _ past
        obtain ⟨combined, receipt⟩ := SourceCurrentAllocatedInheritedPrefix.resident_finite formulas solver next
          edge inherited before.checked post.context.ready post.context.admitted ready.2 ready.1
        simp only [descendants, receipt.actual] at failed
        rcases bind_failed _ _ failed with childFailed | ⟨outputs, middle, childDone, impossible⟩
        · exact childrenReturn _ _ _ (past.snoc (.descendants_children receipt.actual)) _ _ parentFree childFailed
        · cases impossible
      have rowsReturn : rowsAt fuel := by
        intro inherited originals before past fault after parentFree failed
        cases originals with
        | nil => simp only [rows] at failed; cases failed
        | cons original rest =>
          cases fuel with
          | zero =>
            simp only [rows] at failed
            cases failed
            exact retained _ past
          | succ fuel =>
            simp only [rows] at failed
            rcases bind_failed _ _ failed with edgeFailed | ⟨narrowed, middle, edgeDone, later⟩
            · exact edgeReturn fuel inherited original rest before past _ _ parentFree edgeFailed
            · rcases bind_failed _ _ later with childFailed | ⟨result, returned, childDone, suffix⟩
              · exact (ih fuel (Nat.lt_succ_self _)).2.2.2.1 _ _ _
                  (past.snoc (.rows_edge edgeDone)) _ _ parentFree childFailed
              · rcases bind_failed _ _ suffix with tailFailed | ⟨outputs, final, tailDone, impossible⟩
                · exact (ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _
                    (past.snoc (.rows_tail edgeDone childDone)) _ _ parentFree tailFailed
                · cases impossible
      have bodyReturn : bodyAt fuel := by
        intro request before past fault after parentFree failed
        rcases request with ⟨inherited, value⟩
        cases value with
        | empty | union => simp only [nodeBody] at failed; cases failed
        | reference name =>
          simp only [nodeBody] at failed
          cases failed
          exact retained _ past
        | mu entry body depth ordinary =>
          obtain ⟨next, final, current, trace, post, numeric, fits, known, ready, rest⟩ := resources _ past
          have rebuilt := (SourceCurrentAllocatedMuRebuild.resident_rebuild before.checked post.context.ready
            post.context.probes entry body depth ordinary ready.2).1
          simp only [nodeBody, rebuilt] at failed
          cases failed
        | node entry originals depth free =>
          cases fuel with
          | zero =>
            simp only [nodeBody] at failed
            cases failed
            exact retained _ past
          | succ fuel =>
            simp only [nodeBody] at failed
            rcases bind_failed _ _ failed with rowsFailed | ⟨outputs, middle, rowsDone, impossible⟩
            · exact (ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ (past.snoc (.body_rows rfl)) _ _ parentFree rowsFailed
            · cases impossible
      have nodeReturn : nodeAt fuel := by
        intro request before past fault after parentFree failed
        rcases started : beginNode request before with ⟨handle, action, running⟩
        cases action with
        | ready value => simp only [nodeCall, started] at failed; cases failed
        | busy | absent =>
          simp only [nodeCall, started] at failed
          cases failed
          obtain ⟨next, final, current, trace, post, returned, numeric, carrier, ready,
            below, subset, currentRoom, rootFits, rootKnown, need⟩ := resources _ past
          have sound := SourceCurrentAllocatedPartialMemoSound.beginNode_sound formulas solver
            request before post.context.sound ready.1 ready.2
          have components := beginNode_components request before
          rw [started] at sound components
          dsimp only at sound components
          obtain ⟨checked, merge, fourth, _edges⟩ := components
          exact ⟨next, final, post.trans (Post.rebase post.context checked merge fourth sound),
            (by simpa only [checked, caller] using returned), (by simpa only [checked, caller] using rootFits),
            (by simpa only [checked, caller] using rootKnown)⟩
        | evaluate original =>
          simp only [nodeCall, started] at failed
          rcases bind_failed _ _ failed with bodyFailed | ⟨result, middle, bodyDone, impossible⟩
          · exact bodyReturn _ _ (past.snoc (.node_evaluate started)) _ _ parentFree bodyFailed
          · cases impossible
      exact ⟨nodeReturn, bodyReturn, rowsReturn, descendantsReturn, childrenReturn, walkReturn⟩
  cases first with
  | node fuel request before => exact (complete fuel).1 _ _ (.refl _) _ _ parentFree (erase_failed failed)
  | body fuel request before => exact (complete fuel).2.1 _ _ (.refl _) _ _ parentFree (erase_failed failed)
  | rows fuel inherited values before => exact (complete fuel).2.2.1 _ _ _ (.refl _) _ _ parentFree (erase_failed failed)
  | descendants fuel inherited edge before => exact (complete fuel).2.2.2.1 _ _ _ (.refl _) _ _ parentFree (erase_failed failed)
  | children fuel combined values before => exact (complete fuel).2.2.2.2.1 _ _ _ (.refl _) _ _ parentFree (erase_failed failed)
  | walk fuel combined index values before => exact (complete fuel).2.2.2.2.2 _ _ _ _ (.refl _) _ _ parentFree (erase_failed failed)

private theorem successful_return
    {g s r e p h m c n budget : Nat} {first : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2)
    {after : Caller (bits+2)} (done : run g s r e p h m c n budget first = .done () after) :
    Returned formulas solver (forecast budget first seed) (caller first) after := by
  cases first with
  | node fuel request before =>
      obtain ⟨result, actual⟩ := erase_done
        (observed := nodeCall fuel g s r e p h m c n budget request before) done
      obtain ⟨next, final, _graph, _reads, post, returned, numeric, carrier, _rest⟩ :=
        SourceCurrentSharedOuterInitialActual.node_call formulas solver fuel seed
          initial frame fits known inputs.1 inputs.2 room actual
      exact ⟨next, final, post, returned, numeric, carrier⟩
  | body fuel request before =>
      obtain ⟨result, actual⟩ := erase_done
        (observed := nodeBody fuel g s r e p h m c n budget request before) done
      obtain ⟨next, final, _graph, _reads, post, returned, numeric, carrier, _rest⟩ :=
        SourceCurrentSharedOuterInitialActual.node_body formulas solver fuel seed
          initial frame fits known inputs.1 inputs.2 room actual
      exact ⟨next, final, post, returned, numeric, carrier⟩
  | rows fuel inherited values before =>
      obtain ⟨result, actual⟩ := erase_done
        (observed := rows fuel g s r e p h m c n budget inherited values before) done
      obtain ⟨next, final, _graph, _reads, post, returned, numeric, carrier, _rest⟩ :=
        SourceCurrentSharedOuterInitialActual.rows formulas solver fuel seed
          initial frame fits known inputs.1 inputs.2 room actual
      exact ⟨next, final, post, returned, numeric, carrier⟩
  | descendants fuel inherited value before =>
      obtain ⟨result, actual⟩ := erase_done
        (observed := descendants fuel g s r e p h m c n budget inherited value before) done
      obtain ⟨next, final, _graph, _reads, post, returned, numeric, carrier, _rest⟩ :=
        SourceCurrentSharedOuterInitialActual.descendants formulas solver fuel seed
          initial frame fits known inputs.1 inputs.2 room actual
      exact ⟨next, final, post, returned, numeric, carrier⟩
  | children fuel combined values before =>
      obtain ⟨result, actual⟩ := erase_done
        (observed := children fuel g s r e p h m c n budget combined values before) done
      obtain ⟨next, final, _graph, _reads, post, returned, numeric, carrier, _rest⟩ :=
        SourceCurrentSharedOuterInitialActual.children formulas solver fuel seed
          initial frame fits known inputs.1 inputs.2 room actual
      exact ⟨next, final, post, returned, numeric, carrier⟩
  | walk fuel combined index values before =>
      obtain ⟨result, actual⟩ := erase_done
        (observed := walk fuel g s r e p h m c n budget combined index values before) done
      obtain ⟨next, final, _graph, _reads, post, returned, numeric, carrier, _rest⟩ :=
        SourceCurrentSharedOuterInitialActual.walk formulas solver fuel seed
          initial frame fits known inputs.1 inputs.2 room actual
      exact ⟨next, final, post, returned, numeric, carrier⟩

private theorem outcome_return
    {g s r e p h m c n budget : Nat} {first : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2)
    (gBound : phaseNeed budget first seed ≤ g) (sBound : phaseNeed budget first seed ≤ s)
    (rBound : phaseNeed budget first seed ≤ r) (eBound : phaseNeed budget first seed ≤ e)
    (pBound : phaseNeed budget first seed ≤ p) (hBound : phaseNeed budget first seed ≤ h)
    (mBound : phaseNeed budget first seed ≤ m) (cBound : phaseNeed budget first seed ≤ c)
    (nBound : phaseNeed budget first seed ≤ n) :
    Returned formulas solver (forecast budget first seed) (caller first)
      (run g s r e p h m c n budget first).state := by
  cases observed : run g s r e p h m c n budget first with
  | done value after =>
      cases value
      exact successful_return formulas solver seed initial frame fits known inputs room observed
  | failed fault after =>
      have parentFree : ∀ observation, fault ≠ .parent observation := by
        intro observation same
        exact SourceCurrentSharedOuterInitialParentFailure.no_parent_failure formulas solver seed
          initial frame fits known inputs room gBound sBound rBound eBound pBound hBound mBound cBound nBound
          observation after (by simpa only [same] using observed)
      exact failed_return formulas solver seed initial frame fits known inputs room fault after parentFree observed

/-- Every adequately bounded node call outcome retains its exact caller Post and initial resources. -/
theorem node_call (fuel : Nat)
    {g s r e p h m c n budget : Nat} {request : NodeRequest} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (room : Room bits (forecast budget (.node fuel request before) seed).2)
    (gBound : phaseNeed budget (.node fuel request before) seed ≤ g)
    (sBound : phaseNeed budget (.node fuel request before) seed ≤ s)
    (rBound : phaseNeed budget (.node fuel request before) seed ≤ r)
    (eBound : phaseNeed budget (.node fuel request before) seed ≤ e)
    (pBound : phaseNeed budget (.node fuel request before) seed ≤ p)
    (hBound : phaseNeed budget (.node fuel request before) seed ≤ h)
    (mBound : phaseNeed budget (.node fuel request before) seed ≤ m)
    (cBound : phaseNeed budget (.node fuel request before) seed ≤ c)
    (nBound : phaseNeed budget (.node fuel request before) seed ≤ n) :
    let after := (SourceCurrentAllocatedSharedPartialWorker.nodeCall fuel g s r e p h m c n budget request before).state
    ∃ next final, Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits (forecast budget (.node fuel request before) seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (forecast budget (.node fuel request before) seed).1) after.checked.native.machine.heap := by
  have returned := outcome_return formulas solver (first := .node fuel request before) seed
    initial frame fits known ⟨inherited, available⟩ room
    gBound sBound rBound eBound pBound hBound mBound cBound nBound
  simpa only [Returned, SourceCurrentSharedOuterActiveAncestry.run, erased_state, caller] using returned

/-- Every adequately bounded node body outcome retains its exact caller Post and initial resources. -/
theorem node_body (fuel : Nat)
    {g s r e p h m c n budget : Nat} {request : NodeRequest} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (room : Room bits (forecast budget (.body fuel request before) seed).2)
    (gBound : phaseNeed budget (.body fuel request before) seed ≤ g)
    (sBound : phaseNeed budget (.body fuel request before) seed ≤ s)
    (rBound : phaseNeed budget (.body fuel request before) seed ≤ r)
    (eBound : phaseNeed budget (.body fuel request before) seed ≤ e)
    (pBound : phaseNeed budget (.body fuel request before) seed ≤ p)
    (hBound : phaseNeed budget (.body fuel request before) seed ≤ h)
    (mBound : phaseNeed budget (.body fuel request before) seed ≤ m)
    (cBound : phaseNeed budget (.body fuel request before) seed ≤ c)
    (nBound : phaseNeed budget (.body fuel request before) seed ≤ n) :
    let after := (SourceCurrentAllocatedSharedPartialWorker.nodeBody fuel g s r e p h m c n budget request before).state
    ∃ next final, Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits (forecast budget (.body fuel request before) seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (forecast budget (.body fuel request before) seed).1) after.checked.native.machine.heap := by
  have returned := outcome_return formulas solver (first := .body fuel request before) seed
    initial frame fits known ⟨inherited, available⟩ room
    gBound sBound rBound eBound pBound hBound mBound cBound nBound
  simpa only [Returned, SourceCurrentSharedOuterActiveAncestry.run, erased_state, caller] using returned

/-- Every adequately bounded rows outcome retains its exact caller Post and initial resources. -/
theorem rows (fuel : Nat)
    {g s r e p h m c n budget : Nat} {inherited : EqValue} {values : List Edge} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Edges before.checked.native.machine.heap values)
    (room : Room bits (forecast budget (.rows fuel inherited values before) seed).2)
    (gBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ g)
    (sBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ s)
    (rBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ r)
    (eBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ e)
    (pBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ p)
    (hBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ h)
    (mBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ m)
    (cBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ c)
    (nBound : phaseNeed budget (.rows fuel inherited values before) seed ≤ n) :
    let after := (SourceCurrentAllocatedSharedPartialWorker.rows fuel g s r e p h m c n budget inherited values before).state
    ∃ next final, Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits (forecast budget (.rows fuel inherited values before) seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (forecast budget (.rows fuel inherited values before) seed).1) after.checked.native.machine.heap := by
  have returned := outcome_return formulas solver (first := .rows fuel inherited values before) seed
    initial frame fits known ⟨inheritedReady, available⟩ room
    gBound sBound rBound eBound pBound hBound mBound cBound nBound
  simpa only [Returned, SourceCurrentSharedOuterActiveAncestry.run, erased_state, caller] using returned

/-- Every adequately bounded descendants outcome retains its exact caller Post and initial resources. -/
theorem descendants (fuel : Nat)
    {g s r e p h m c n budget : Nat} {inherited : EqValue} {value : Edge} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Resident before.checked.native.machine.heap value)
    (room : Room bits (forecast budget (.descendants fuel inherited value before) seed).2)
    (gBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ g)
    (sBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ s)
    (rBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ r)
    (eBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ e)
    (pBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ p)
    (hBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ h)
    (mBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ m)
    (cBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ c)
    (nBound : phaseNeed budget (.descendants fuel inherited value before) seed ≤ n) :
    let after := (SourceCurrentAllocatedSharedPartialWorker.descendants fuel g s r e p h m c n budget inherited value before).state
    ∃ next final, Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits (forecast budget (.descendants fuel inherited value before) seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (forecast budget (.descendants fuel inherited value before) seed).1) after.checked.native.machine.heap := by
  have returned := outcome_return formulas solver (first := .descendants fuel inherited value before) seed
    initial frame fits known ⟨inheritedReady, available⟩ room
    gBound sBound rBound eBound pBound hBound mBound cBound nBound
  simpa only [Returned, SourceCurrentSharedOuterActiveAncestry.run, erased_state, caller] using returned

/-- Every adequately bounded children outcome retains its exact caller Post and initial resources. -/
theorem children (fuel : Nat)
    {g s r e p h m c n budget : Nat} {combined : EqValue} {values : List Node} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values)
    (room : Room bits (forecast budget (.children fuel combined values before) seed).2)
    (gBound : phaseNeed budget (.children fuel combined values before) seed ≤ g)
    (sBound : phaseNeed budget (.children fuel combined values before) seed ≤ s)
    (rBound : phaseNeed budget (.children fuel combined values before) seed ≤ r)
    (eBound : phaseNeed budget (.children fuel combined values before) seed ≤ e)
    (pBound : phaseNeed budget (.children fuel combined values before) seed ≤ p)
    (hBound : phaseNeed budget (.children fuel combined values before) seed ≤ h)
    (mBound : phaseNeed budget (.children fuel combined values before) seed ≤ m)
    (cBound : phaseNeed budget (.children fuel combined values before) seed ≤ c)
    (nBound : phaseNeed budget (.children fuel combined values before) seed ≤ n) :
    let after := (SourceCurrentAllocatedSharedPartialWorker.children fuel g s r e p h m c n budget combined values before).state
    ∃ next final, Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits (forecast budget (.children fuel combined values before) seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (forecast budget (.children fuel combined values before) seed).1) after.checked.native.machine.heap := by
  have returned := outcome_return formulas solver (first := .children fuel combined values before) seed
    initial frame fits known ⟨inheritedReady, available⟩ room
    gBound sBound rBound eBound pBound hBound mBound cBound nBound
  simpa only [Returned, SourceCurrentSharedOuterActiveAncestry.run, erased_state, caller] using returned

/-- Every adequately bounded walk outcome retains its exact caller Post and initial resources. -/
theorem walk (fuel : Nat)
    {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values : List Node} {before : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values)
    (room : Room bits (forecast budget (.walk fuel combined index values before) seed).2)
    (gBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ g)
    (sBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ s)
    (rBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ r)
    (eBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ e)
    (pBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ p)
    (hBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ h)
    (mBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ m)
    (cBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ c)
    (nBound : phaseNeed budget (.walk fuel combined index values before) seed ≤ n) :
    let after := (SourceCurrentAllocatedSharedPartialWorker.walk fuel g s r e p h m c n budget combined index values before).state
    ∃ next final, Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits (forecast budget (.walk fuel combined index values before) seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (forecast budget (.walk fuel combined index values before) seed).1) after.checked.native.machine.heap := by
  have returned := outcome_return formulas solver (first := .walk fuel combined index values before) seed
    initial frame fits known ⟨inheritedReady, available⟩ room
    gBound sBound rBound eBound pBound hBound mBound cBound nBound
  simpa only [Returned, SourceCurrentSharedOuterActiveAncestry.run, erased_state, caller] using returned

end MicroCFTA.SourceCurrentSharedOuterInitialOutcomePost
