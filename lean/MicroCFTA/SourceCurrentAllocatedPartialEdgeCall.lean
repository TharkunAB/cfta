import MicroCFTA.SourceCurrentAllocatedPartialMemoSound
import MicroCFTA.SourceCurrentAllocatedPartialReads

/-!
# Current reduced-edge calls with actual warm result cells

An evaluated cell runs the current checked parent reduction and publishes
its derived result law. A completed hit reuses that law through the actual
physical key. Neither endpoint assumes a future body result or resets a
warm table. Busy observations and outer recursive completion stay explicit.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialEdgeCall
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialMemoSound (Sound EdgeLaw)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Edge" => EdgeValue Symbol Guard
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GlobalsValid" => EndpointMemoGateTrace.Valid
local notation "Resident" => InternedEdgeResidency.EdgeResident
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- A range plan sees only the owner's actual current field load. -/
def Ranges (budget : Nat) (request : EdgeRequest) (before : Caller width) : Prop :=
  ∀ loaded : Allocated,
    SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints = .ok (some loaded) →
    SourceCurrentAllocatedParentEdge.Ranges budget request.value.entry.key.constraint loaded request.inherited
      request.value.children before.checked before.fourth before.merge

/-- Only a reached evaluated owner demands a parent range plan. -/
def CallRanges (budget : Nat) (request : EdgeRequest) (before : Caller width) : Prop :=
  ∀ handle original running,
    beginEdge request before = (handle, .evaluate original, running) → Ranges budget original running

/-- A reduced-edge call retains all caller and current checked invariants. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (request : EdgeRequest) (before : Caller width) (result : Edge) (after : Caller width) (final : Memos) : Prop where
  ready : Ready after.checked
  admitted : At formulas solver inventory after.checked
  sound : Sound formulas solver after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked)
  resident : Resident after.checked.native.machine.heap result
  stored : SourceCurrentMemoMergeEffects.Stored after.checked.native.machine.heap after.merge
  covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient after.merge
  retained : Extends before.merge after.merge
  globals : GlobalsValid after.checked.native.machine.heap final
  correct : SourceCurrentEmptinessMemo.Correct formulas solver after.checked.native.machine.heap after.fourth
  fourthRetained : SourceCurrentEmptinessMemo.Extends before.fourth after.fourth
  nodes : after.nodeResults = before.nodeResults
  language : EdgeLaw formulas solver request result

/-- The current parent derives its body result without a supplied result-language law. -/
theorem body_finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
    (sound : Sound formulas solver before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap before.fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient before.merge)
    (ranges : Ranges budget request before) (memos : Memos) (valid : GlobalsValid before.checked.native.machine.heap memos) :
    ∃ result after next final,
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result after,
        SourceCurrentAllocatedPartialReads.EdgeBodyReads formulas solver actual memos final ∧
        after.edgeResults = before.edgeResults ∧
        Receipt formulas solver next request before result after final := by
  obtain ⟨cached, loaded, found⟩ := ready.good.fields request.value.entry.key request.value resident
  have available := ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
  obtain ⟨result, checked, fourth, merge, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedParentEdge.finite formulas solver inventory budget request.value.entry.key.symbol
      request.value.entry.key.constraint loaded request.inherited request.value.children before.checked before.fourth before.merge
      ready admitted cached found inherited available correct stored covered (ranges loaded found) memos valid
  have law : EdgeLaw formulas solver request result := by
    intro ambient term
    have input := InternedGuardedLanguage.edgeMeaning_all (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term
    change InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term ↔
      SourceCurrentAllocatedParentEdge.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient
        request.value.entry.key.symbol request.value.entry.key.constraint request.value.children term at input
    exact ⟨fun accepted => input.mpr ((receipt.language ambient term).1 accepted),
      fun satisfied => ((receipt.language ambient term).2 satisfied).trans input.symm⟩
  refine ⟨result, advance before checked fourth merge, next, final,
    .parent (fun _ => found) actual, .parent (field := fun _ => found) reads, rfl,
    receipt.ready, receipt.admitted, sound.advance formulas solver checked fourth merge receipt.effects,
    receipt.effects, receipt.resident, receipt.stored, receipt.covered, receipt.retained,
    receipt.globals, receipt.correct, receipt.fourthRetained, rfl, law⟩

/-- A reached evaluation runs its actual owner body and finishes that same live cell. -/
theorem evaluated (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
    (sound : Sound formulas solver before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap before.fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient before.merge)
    (handle : Nat) (original : EdgeRequest) (running : Caller width)
    (started : beginEdge request before = (handle, .evaluate original, running))
    (ranges : Ranges budget original running) (memos : Memos) (valid : GlobalsValid before.checked.native.machine.heap memos) :
    ∃ result after next final,
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after,
        SourceCurrentAllocatedPartialReads.EdgeCallReads formulas solver actual memos final ∧
        after.edgeResults.cells handle = some ⟨original, .returned result⟩ ∧
        Receipt formulas solver next request before result after final := by
  obtain ⟨runningSound, cell, owner, key⟩ :=
    SourceCurrentAllocatedPartialMemoSound.beginEdge_evaluate_sound formulas solver request before sound inherited resident
      handle original running started
  have components := beginEdge_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checkedSame, mergeSame, fourthSame, nodesSame⟩ := components
  have runningReady : Ready running.checked := by simpa only [checkedSame] using ready
  obtain ⟨result, middle, next, final, body, reads, tables, receipt⟩ :=
    body_finite formulas solver inventory budget original running runningReady
      (by simpa only [checkedSame] using admitted) runningSound owner.inherited owner.input
      (by simpa only [checkedSame, fourthSame] using correct)
      (by simpa only [checkedSame, mergeSame] using stored)
      (by simpa only [checkedSame, mergeSame] using covered) ranges memos
      (by simpa only [checkedSame] using valid)
  have current : middle.edgeResults.cells handle = some ⟨original, .evaluating⟩ := by
    rw [tables]
    exact cell
  have completed := SourceCurrentAllocatedPartialMemoSound.finishEdge_sound formulas solver handle original result middle
    receipt.sound current receipt.resident receipt.language
  have law := SourceCurrentAllocatedPartialMemoSound.EdgeLaw.of_key formulas solver
    running.checked.operations.constraints running.checked.native.machine.heap original request result
    runningReady.good.operations.constraints runningReady.semantic.ready.semantic.1.normal.facts.coherent
    owner.inherited (by simpa only [checkedSame] using inherited)
    owner.input (by simpa only [checkedSame] using resident) key receipt.language
  refine ⟨result, finishEdge handle result middle, next, final, .evaluate started body,
    .evaluate (started := started) reads, finishEdge_returned handle original result middle current,
    receipt.ready, receipt.admitted, completed, ?_, receipt.resident, receipt.stored,
    receipt.covered, ?_, receipt.globals, receipt.correct, ?_, ?_, law⟩
  · simpa only [finishEdge, checkedSame] using receipt.effects
  · simpa only [finishEdge, mergeSame] using receipt.retained
  · simpa only [finishEdge, fourthSame] using receipt.fourthRetained
  · exact receipt.nodes.trans nodesSame

/-- A completed warm hit needs no parent range plan and returns the identical caller state. -/
theorem ready_hit (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
    (sound : Sound formulas solver before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap before.fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient before.merge)
    (handle : Nat) (result : Edge) (after : Caller width)
    (started : beginEdge request before = (handle, .ready result, after))
    (memos : Memos) (valid : GlobalsValid before.checked.native.machine.heap memos) :
    after = before ∧ ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after,
      SourceCurrentAllocatedPartialReads.EdgeCallReads formulas solver actual memos memos ∧
      Receipt formulas solver inventory request before result after memos := by
  obtain ⟨same, available, law⟩ := SourceCurrentAllocatedPartialMemoSound.beginEdge_ready_sound formulas solver request before sound
    ready.good.operations.constraints ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident handle result after started
  subst after
  exact ⟨rfl, .hit started, .hit (started := started), ready, admitted, sound,
    SourceCurrentConjunctionRowsAllocation.Effects.refl _
      (SourceCurrentAllocatedConjunctionMemo.ready before.checked ready.good ready.semantic ready.costs),
    available, stored, covered, extends_refl _, valid, correct, (fun _ _ found => found), rfl, law⟩

/-- A missing key constructs its own evaluated prefix without a successful-body premise. -/
theorem fresh (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
    (sound : Sound formulas solver before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap before.fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient before.merge)
    (missing : before.edgeResults.table request.key = none)
    (ranges : Ranges budget request (beginEdge request before).2.2)
    (memos : Memos) (valid : GlobalsValid before.checked.native.machine.heap memos) :
    ∃ result after next final,
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after,
        SourceCurrentAllocatedPartialReads.EdgeCallReads formulas solver actual memos final ∧
        after.edgeResults.cells before.edgeResults.next = some ⟨request, .returned result⟩ ∧
        Receipt formulas solver next request before result after final := by
  have started := (SourceCurrentAllocatedPartialMemoSound.beginEdge_fresh request before missing).1
  apply evaluated formulas solver inventory budget request before ready admitted sound inherited resident correct stored covered
    before.edgeResults.next request (beginEdge request before).2.2
    (by simp only [started]) ranges memos valid

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem not_absent (request : EdgeRequest) (before : Caller width)
    (valid : SourceCurrentAllocatedPartialState.Valid before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited) :
    (beginEdge request before).2.1 ≠ .absent := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have next := FlatMemoThunk.lookup_valid request.key request before.edgeResults
    (EdgeLinked before.checked.operations.constraints) (fun _ => True) valid.edges ⟨inherited.1, rfl⟩ trivial
  obtain ⟨cell, found, _⟩ := next.linked request.key published.1 (FlatMemoThunk.lookup_stored _ _ _)
  change published.2.cells published.1 = some cell at found
  change (FlatMemoThunk.demand published.1 published.2).1 ≠ .absent
  cases phase : cell.status <;> simp only [FlatMemoThunk.demand, found, phase] <;> simp

/-- A valid reduced-edge call either observes a busy cell or constructs an actual completed call. -/
theorem finite_or_busy (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
    (sound : Sound formulas solver before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap before.fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient before.merge)
    (ranges : CallRanges budget request before) (memos : Memos) (valid : GlobalsValid before.checked.native.machine.heap memos) :
    (∃ handle running, beginEdge request before = (handle, .busy, running)) ∨
      ∃ result after next final,
        ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeCall budget request before result after,
          SourceCurrentAllocatedPartialReads.EdgeCallReads formulas solver actual memos final ∧
          Receipt formulas solver next request before result after final := by
  generalize started : beginEdge request before = observed
  obtain ⟨handle, observation, running⟩ := observed
  cases observation with
  | ready result =>
      obtain ⟨_, actual, reads, receipt⟩ := ready_hit formulas solver inventory budget request before ready admitted sound
        inherited resident correct stored covered handle result running started memos valid
      exact Or.inr ⟨result, running, inventory, memos, actual, reads, receipt⟩
  | evaluate original =>
      obtain ⟨result, after, next, final, actual, reads, _, receipt⟩ :=
        evaluated formulas solver inventory budget request before ready admitted sound inherited resident correct stored covered
          handle original running started (ranges handle original running started) memos valid
      exact Or.inr ⟨result, after, next, final, actual, reads, receipt⟩
  | busy => exact Or.inl ⟨handle, running, rfl⟩
  | absent =>
      have impossible := not_absent request before sound.valid inherited
      exact False.elim (impossible (by rw [started]))

end MicroCFTA.SourceCurrentAllocatedPartialEdgeCall
