import MicroCFTA.SourceCurrentAllocatedPartialEdgeCall

namespace MicroCFTA.PartialEdgeCallIndependentProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialEdgeCall
open SourceCurrentAllocatedPartialMemoSound (Sound EdgeLaw)
open SourceCurrentAllocatedPartialGraph (EdgeCall)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Edge" => EdgeValue Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GlobalsValid" => EndpointMemoGateTrace.Valid
local notation "Resident" => InternedEdgeResidency.EdgeResident
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

#print axioms body_finite
#print axioms evaluated
#print axioms ready_hit
#print axioms fresh
#print axioms finite_or_busy
#check @body_finite
#check @evaluated
#check @ready_hit
#check @fresh
#check @finite_or_busy
#check @Ranges
#check @CallRanges
#check @Receipt

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem demand_table (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle memo).2.table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.demand, found]
  | some cell => cases phase : cell.status <;> simp [FlatMemoThunk.demand, found, phase, FlatMemoThunk.setStatus]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem begin_published (request : EdgeRequest) (before : Caller width) :
    (beginEdge request before).2.2.edgeResults.table request.key = some (beginEdge request before).1 := by
  change (FlatMemoThunk.demand _ _).2.table _ = _
  rw [demand_table]
  exact FlatMemoThunk.lookup_stored _ _ _

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem finish_table (handle : Nat) (result : Edge) (before : Caller width) :
    (finishEdge handle result before).edgeResults.table = before.edgeResults.table := by
  cases found : before.edgeResults.cells handle with
  | none => simp only [finishEdge, FlatMemoThunk.finish, found]
  | some cell =>
      cases cell with
      | mk request status => cases status <;> simp [finishEdge, FlatMemoThunk.finish, found, FlatMemoThunk.setStatus]

/-- The actual parent body leaves its outer caller table intact; finish preserves its published keys. -/
theorem call_table {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeCall budget request before result after) :
    after.edgeResults.table = (beginEdge request before).2.2.edgeResults.table := by
  cases actual with
  | hit started => rw [started]
  | evaluate started body =>
      rw [started]
      dsimp only
      rw [finish_table]
      cases body
      rfl

section Inputs
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller width)
variable (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
variable (sound : Sound formulas solver before)
variable (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
variable (resident : Resident before.checked.native.machine.heap request.value)
variable (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap before.fourth)
variable (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
variable (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient before.merge)
variable (memos : Memos) (valid : GlobalsValid before.checked.native.machine.heap memos)
include ready admitted sound inherited resident correct stored covered valid

/-- A reached evaluation derives its returned cell, then the identical request completes as a whole-state warm hit. -/
theorem evaluated_repeat (handle : Nat) (owner : EdgeRequest) (running : Caller width)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (ranges : Ranges budget owner running) :
    ∃ (result : Edge) (after : Caller width) (next : Inventory) (final : Memos),
      after.edgeResults.cells handle = some ⟨owner, .returned result⟩ ∧
      after.edgeResults.table request.key = some handle ∧
      beginEdge request after = (handle, .ready result, after) ∧
      ∃ actual : EdgeCall budget request after result after,
        SourceCurrentAllocatedPartialReads.EdgeCallReads formulas solver actual final final ∧
        Receipt formulas solver next request after result after final := by
  obtain ⟨result, after, next, final, actual, _, returned, receipt⟩ :=
    evaluated formulas solver inventory budget request before ready admitted sound inherited resident correct stored covered
      handle owner running started ranges memos valid
  have published := begin_published request before
  rw [started] at published
  have retained : after.edgeResults.table request.key = some handle := by
    rw [call_table actual]
    simpa only [started] using published
  have again := beginEdge_ready request owner after handle result retained returned
  have laterInherited := inherited.grows receipt.effects.grows.constraint_growth
  have laterResident := InternedEdgeResidency.edge_grows _ _ receipt.effects.keeps.growth _ resident
  obtain ⟨_, warm, reads, repeated⟩ := ready_hit formulas solver next budget request after receipt.ready receipt.admitted
    receipt.sound laterInherited laterResident receipt.correct receipt.stored receipt.covered handle result after again final receipt.globals
  exact ⟨result, after, next, final, returned, retained, again, warm, reads, repeated⟩

-- Every evaluated alias stores the actual owner's result cell, not a candidate replacement request.
example (handle : Nat) (owner : EdgeRequest) (running : Caller width)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (ranges : Ranges budget owner running) :
    ∃ (result : Edge) (after : Caller width) (next : Inventory) (final : Memos),
      after.edgeResults.cells handle = some ⟨owner, .returned result⟩ ∧
      EdgeLaw formulas solver request result ∧ Sound formulas solver after ∧
      At formulas solver next after.checked ∧ GlobalsValid after.checked.native.machine.heap final := by
  obtain ⟨result, after, next, final, _, _, returned, receipt⟩ :=
    evaluated formulas solver inventory budget request before ready admitted sound inherited resident correct stored covered
      handle owner running started ranges memos valid
  exact ⟨result, after, next, final, returned, receipt.language, receipt.sound, receipt.admitted, receipt.globals⟩

-- A warm ready hit has no range-plan input and returns the exact old caller state.
example (handle : Nat) (result : Edge) (after : Caller width)
    (started : beginEdge request before = (handle, .ready result, after)) :
    after = before ∧ EdgeLaw formulas solver request result := by
  obtain ⟨same, _, _, receipt⟩ := ready_hit formulas solver inventory budget request before ready admitted sound inherited resident
    correct stored covered handle result after started memos valid
  exact ⟨same, receipt.language⟩

-- A missing key constructs its actual owner and completed cell without a body-success assumption.
example (missing : before.edgeResults.table request.key = none)
    (ranges : Ranges budget request (beginEdge request before).2.2) :
    ∃ (result : Edge) (after : Caller width) (next : Inventory) (final : Memos),
      after.edgeResults.cells before.edgeResults.next = some ⟨request, .returned result⟩ ∧
      Resident after.checked.native.machine.heap result ∧
      Receipt formulas solver next request before result after final := by
  obtain ⟨result, after, next, final, _, _, returned, receipt⟩ :=
    fresh formulas solver inventory budget request before ready admitted sound inherited resident correct stored covered
      missing ranges memos valid
  exact ⟨result, after, next, final, returned, receipt.resident, receipt⟩

-- An actual busy observation selects the Or-left boundary; no range plan or successful body is invented.
example (handle : Nat) (running : Caller width)
    (busy : beginEdge request before = (handle, .busy, running)) :
    ∃ actualHandle actualRunning, beginEdge request before = (actualHandle, .busy, actualRunning) := by
  have ranges : CallRanges budget request before := by
    intro other original current evaluated
    rw [busy] at evaluated
    cases evaluated
  rcases finite_or_busy formulas solver inventory budget request before ready admitted sound inherited resident correct stored covered
      ranges memos valid with observed | ⟨result, after, next, final, actual, _, _⟩
  · exact observed
  · exact False.elim (actual.not_busy busy)

-- Completion retains all original outer-node cells and the current merge/fourth families.
example (ranges : CallRanges budget request before) :
    (∃ handle running, beginEdge request before = (handle, .busy, running)) ∨
      ∃ (result : Edge) (after : Caller width) (next : Inventory) (final : Memos),
        after.nodeResults = before.nodeResults ∧ Extends before.merge after.merge ∧
        SourceCurrentEmptinessMemo.Extends before.fourth after.fourth ∧
        Receipt formulas solver next request before result after final := by
  rcases finite_or_busy formulas solver inventory budget request before ready admitted sound inherited resident correct stored covered
      ranges memos valid with busy | ⟨result, after, next, final, _, _, receipt⟩
  · exact Or.inl busy
  · exact Or.inr ⟨result, after, next, final, receipt.nodes, receipt.retained, receipt.fourthRetained, receipt⟩
end Inputs

-- Literal empty caller families derive their own Sound and missing-key facts before the actual fresh call.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (checked : Checked width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (ready : Ready checked) (admitted : At formulas solver inventory checked)
    (inherited : SourceEqualityConstraintAllocation.Ready checked.operations.constraints request.inherited)
    (resident : Resident checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver checked.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient merge)
    (ranges : Ranges budget request (beginEdge request (initial checked merge fourth)).2.2)
    (memos : Memos) (valid : GlobalsValid checked.native.machine.heap memos) :
    ∃ (result : Edge) (after : Caller width) (next : Inventory) (final : Memos),
      after.edgeResults.cells 0 = some ⟨request, .returned result⟩ ∧
      Receipt formulas solver next request (initial checked merge fourth) result after final := by
  obtain ⟨result, after, next, final, _, _, returned, receipt⟩ := fresh formulas solver inventory budget request
    (initial checked merge fourth) ready admitted
    (SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver checked merge fourth)
    inherited resident correct stored covered rfl ranges memos valid
  exact ⟨result, after, next, final, returned, receipt⟩

#print axioms evaluated_repeat
#print axioms call_table
#check @evaluated_repeat
#check @call_table
end MicroCFTA.PartialEdgeCallIndependentProbe
