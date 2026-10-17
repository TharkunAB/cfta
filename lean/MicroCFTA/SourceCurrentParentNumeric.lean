import MicroCFTA.SourceCurrentParentForecast
import MicroCFTA.SourceCurrentLocalNumeric
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual

/-!
# Initial numeric completion of the allocated parent edge

Raw rejection constructs its sentinel before field or child work.
A live return runs the actual local reduction and then the checked edge
constructor. Both stages retain the same caller and returned inventory.
Initial profiles determine all nine worker fuels. No future graph, range,
or successful worker is an input.
-/
namespace MicroCFTA.SourceCurrentParentNumeric
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning edgeMeaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "fuel" => SourceCurrentParentForecast.fuel
namespace Graph
export SourceCurrentAllocatedParentEdge (Edge Receipt RawMeaning)
export SourceCurrentAllocatedParentEdgeActual (Reads)
end Graph
variable {width bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Only the initial live branch demands the stored field and original children. -/
def LiveInputs (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller width) : Prop :=
  contradictory original = false →
    SourceEqualityGuardReadback.Cached original.equalities ∧
    SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded) ∧
    SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited ∧
    Values before.checked.native.machine.heap values

/-- One actual parent return retains strict reads, language, caller history, and numeric replay. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (profile : Profile) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated)
    (inherited : EqValue) (values : List (Value Symbol Guard)) (before : Caller width) (memos : Memos)
    (result : EdgeValue Symbol Guard) (after : Checked width) (savedFourth : Fourth) (saved : Memo) (final : Memos) : Prop where
  /-- The live field was loaded from the original initial operations. -/
  field : contradictory original = false →
    SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded)
  /-- The source graph retains raw rejection or the exact local and constructor order. -/
  actual : Graph.Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
    result after savedFourth saved
  /-- Global memo reads belong to that same actual graph. -/
  reads : Graph.Reads formulas solver actual memos final
  /-- The complete old receipt retains physical stores and guarded language. -/
  semantic : Graph.Receipt formulas solver inventory symbol original loaded inherited values before.checked result after
    before.fourth savedFourth before.merge saved final
  /-- The full Frame shares the caller Post inventory. -/
  frame : Frame formulas solver inventory after
  /-- The initial local schedule and original child count bound construction. -/
  fits : Fits (SourceCurrentParentForecast.finalProfile budget values.length original loaded inherited before.checked profile) after
  /-- Both outer tables and the complete caller retain their current laws. -/
  post : Post formulas solver inventory before (advance before after savedFourth saved) final
  /-- All nine independently larger fuels retain the same full parent return. -/
  run : ∀ g s r e p h m c n,
    fuel budget values.length original loaded inherited before.checked profile ≤ g →
    fuel budget values.length original loaded inherited before.checked profile ≤ s →
    fuel budget values.length original loaded inherited before.checked profile ≤ r →
    fuel budget values.length original loaded inherited before.checked profile ≤ e →
    fuel budget values.length original loaded inherited before.checked profile ≤ p →
    fuel budget values.length original loaded inherited before.checked profile ≤ h →
    fuel budget values.length original loaded inherited before.checked profile ≤ m →
    fuel budget values.length original loaded inherited before.checked profile ≤ c →
    fuel budget values.length original loaded inherited before.checked profile ≤ n →
    SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited values
      before.checked before.fourth before.merge = .done result after savedFourth saved

/-- Raw rejection needs no field, inherited readiness, available children, or Room. -/
theorem rejected (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked) (test : contradictory original = true) :
    Receipt formulas solver inventory profile budget symbol original loaded inherited values before memos
      (SourceCurrentAllocatedMkEdge.reject symbol before.checked).1 (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2
      before.fourth before.merge memos := by
  obtain ⟨_actual, _reads, semantic⟩ := SourceCurrentAllocatedParentEdge.rejected formulas solver inventory budget symbol
    original loaded inherited values before.checked before.fourth before.merge initial.ready initial.admitted test
    initial.correct initial.stored initial.covered memos initial.globals
  have constructor := SourceCurrentMkEdgeNumeric.reject formulas solver inventory symbol before.checked frame profile fits
  have post : Post formulas solver inventory before
      (advance before (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2 before.fourth before.merge) memos :=
    ⟨⟨semantic.ready, semantic.admitted,
      initial.sound.advance formulas solver _ before.fourth before.merge semantic.effects,
      semantic.stored, semantic.covered, semantic.correct, semantic.globals,
      SourceCurrentAllocatedProbeParent.reject_heap symbol before.checked initial.probes⟩,
      semantic.effects, semantic.retained, semantic.fourthRetained⟩
  refine ⟨?_, .rejected test, .rejected (test := test), semantic, constructor.2.1, ?_, post, ?_⟩
  · intro impossible
    rw [test] at impossible
    cases impossible
  · simpa only [SourceCurrentParentForecast.finalProfile, test, ite_true] using constructor.2.2.1
  · intro g s r e p h m c n _hg _hs _hr _he _hp _hh _hm _hc _hn
    exact SourceCurrentAllocatedParentWorker.edge_rejected g s r e p h m c n budget symbol original inherited values
      before.checked before.fourth before.merge test

/-- Initial live facts construct the literal local and parent workers at computed fuels. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked) (live : LiveInputs original loaded inherited values before)
    (reserved : SourceCurrentParentForecast.Reserved bits budget values.length original loaded inherited before.checked profile) :
    ∃ result after savedFourth saved next final,
      Receipt formulas solver next profile budget symbol original loaded inherited values before memos result after savedFourth saved final := by
  cases test : contradictory original with
  | true =>
      exact ⟨_, _, before.fourth, before.merge, inventory, memos,
        rejected formulas solver inventory budget symbol original loaded inherited values before memos initial frame profile fits test⟩
  | false =>
      obtain ⟨cached, found, inheritedReady, available⟩ := live test
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.checked.operations.constraints
        initial.ready.good.operations.constraints cached loaded found
      have localRoom : SourceCurrentLocalForecast.Reserved bits budget values.length loaded inherited before.checked profile := by
        simpa only [SourceCurrentParentForecast.Reserved, test, Bool.false_eq_true, ite_false] using reserved
      obtain ⟨children, middle, savedFourth, saved, next, final, lowerReceipt⟩ := SourceCurrentLocalNumeric.complete formulas solver inventory
        budget original loaded inherited values before memos initial frame profile fits cached found inheritedReady available localRoom
      have lower := lowerReceipt.semantic
      have storedReady := loadedReady.1.grows lower.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations original from ⟨cached, loaded, found⟩).grows
          lower.effects.grows
      obtain ⟨result, after, constructor, finalFrame, numeric, _nodes, _edges⟩ := SourceCurrentMkEdgeNumeric.complete
        formulas solver next symbol loaded children middle lowerReceipt.frame
        (SourceCurrentLocalForecast.finalProfile budget values.length loaded inherited before.checked profile) lowerReceipt.fits
        storedReady field lower.available
      let actual : Graph.Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
          result after savedFourth saved := .live test lowerReceipt.actual constructor.actual
      have reads : Graph.Reads formulas solver actual memos final := .live (test := test) (built := constructor.actual) lowerReceipt.reads
      have semantic : Graph.Receipt formulas solver next symbol original loaded inherited values before.checked result after
          before.fourth savedFourth before.merge saved final := by
        refine ⟨constructor.ready, constructor.admitted, lower.effects.trans constructor.effects, constructor.resident,
          lower.stored.grows constructor.effects.keeps, lower.covered, lower.retained,
          SourceQueryUnfoldMemo.valid_grows _ _ lower.ready.semantic constructor.effects.keeps final lower.globals,
          SourceCurrentEmptinessMemo.grows formulas solver constructor.effects.keeps savedFourth lower.correct,
          lower.fourthRetained, Or.inr ⟨children, middle, lower.length, constructor⟩, ?_⟩
        intro ambient term
        have edgeLaw := constructor.language storedReady ambient term
        rw [loadedReady.2] at edgeLaw
        have narrows : edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
            Graph.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term := by
          intro accepted
          obtain ⟨terms, shape, forest, guard⟩ := edgeLaw.mp accepted
          exact ⟨terms, shape, (lower.language ambient symbol terms).1 forest, guard⟩
        refine ⟨narrows, fun inheritedSat => ⟨narrows, ?_⟩⟩
        rintro ⟨terms, shape, forest, guard⟩
        apply edgeLaw.mpr
        refine ⟨terms, shape, ?_, guard⟩
        have guards : SourceEqualityPCSGuard.holds formulas solver original (.node symbol terms) = true := by
          simpa only [shape] using guard
        have inheritedSat : SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload := by
          simpa only [shape] using inheritedSat
        exact ((lower.language ambient symbol terms).2 guards inheritedSat).mpr forest
      have probes : InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap := by
        have produced := SourceCurrentAllocatedProbeParent.mkEdge_heap symbol loaded children middle lowerReceipt.post.context.probes
        rw [constructor.actual] at produced
        exact produced
      have post : Post formulas solver next before (advance before after savedFourth saved) final :=
        ⟨⟨semantic.ready, semantic.admitted,
          initial.sound.advance formulas solver after savedFourth saved semantic.effects,
          semantic.stored, semantic.covered, semantic.correct, semantic.globals, probes⟩,
          semantic.effects, semantic.retained, semantic.fourthRetained⟩
      refine ⟨result, after, savedFourth, saved, next, final, (fun _ => found), actual, reads, semantic, finalFrame, ?_, post, ?_⟩
      · simpa only [SourceCurrentParentForecast.finalProfile, test, Bool.false_eq_true, ite_false, lower.length] using numeric
      · intro g s r e p h m c n hg hs hr he hp hh hm hc hn
        have done := lowerReceipt.run g s r e p h m c n
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hg)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hs)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hr)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using he)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hp)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hh)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hm)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hc)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hn)
        simp only [SourceCurrentAllocatedParentWorker.edge, test, Bool.false_eq_true, ite_false, found,
          SourceCurrentAllocatedParentWorker.reduceChildren, done, SourceCurrentAllocatedParentWorker.Outcome.bind,
          SourceCurrentAllocatedParentWorker.build, constructor.actual]

/-- Resident live inputs derive their own initial field and children; raw rejection skips these facts. -/
theorem resident_complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory) (budget : Nat) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (resident : contradictory request.value.entry.key.constraint = false → Resident before.checked.native.machine.heap request.value)
    (inheritedReady : contradictory request.value.entry.key.constraint = false →
      SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (reserved : SourceCurrentParentForecast.residentReserved bits budget request before.checked profile) :
    ∃ loaded result after savedFourth saved next final,
      Receipt formulas solver next profile budget request.value.entry.key.symbol request.value.entry.key.constraint loaded
        request.inherited request.value.children before memos result after savedFourth saved final ∧
      Fits (SourceCurrentParentForecast.residentProfile budget request before.checked profile) after ∧
      ∀ g s r e p h m c n,
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ g →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ s →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ r →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ e →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ p →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ h →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ m →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ c →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ n →
        SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
          request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge =
          .done result after savedFourth saved := by
  cases test : contradictory request.value.entry.key.constraint with
  | true =>
      let loaded : Allocated := ⟨.contradiction, request.value.entry.key.constraint.guard⟩
      have receipt := rejected formulas solver inventory budget request.value.entry.key.symbol request.value.entry.key.constraint
        loaded request.inherited request.value.children before memos initial frame profile fits test
      refine ⟨loaded, _, _, before.fourth, before.merge, inventory, memos, receipt, ?_, ?_⟩
      · simpa only [SourceCurrentParentForecast.residentProfile, SourceCurrentParentForecast.finalProfile, test, ite_true] using receipt.fits
      · intro g s r e p h m c n _hg _hs _hr _he _hp _hh _hm _hc _hn
        apply receipt.run g s r e p h m c n <;>
          simp only [SourceCurrentParentForecast.fuel, test, ite_true, Nat.zero_le]
  | false =>
      obtain ⟨cached, loaded, found⟩ := initial.ready.good.fields request.value.entry.key request.value (resident test)
      have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value (resident test)
      have live : LiveInputs request.value.entry.key.constraint loaded request.inherited request.value.children before :=
        fun _ => ⟨cached, found, inheritedReady test, available⟩
      have reserve : SourceCurrentParentForecast.Reserved bits budget request.value.children.length request.value.entry.key.constraint
          loaded request.inherited before.checked profile := by
        simpa only [SourceCurrentParentForecast.residentReserved, test, Bool.false_eq_true, ite_false, found] using reserved
      obtain ⟨result, after, savedFourth, saved, next, final, receipt⟩ := complete formulas solver inventory budget
        request.value.entry.key.symbol request.value.entry.key.constraint loaded request.inherited request.value.children
        before memos initial frame profile fits live reserve
      refine ⟨loaded, result, after, savedFourth, saved, next, final, receipt, ?_, ?_⟩
      · simpa only [SourceCurrentParentForecast.residentProfile, test, Bool.false_eq_true, ite_false, found] using receipt.fits
      · intro g s r e p h m c n hg hs hr he hp hh hm hc hn
        exact receipt.run g s r e p h m c n
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hg)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hs)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hr)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using he)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hp)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hh)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hm)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hc)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hn)

end MicroCFTA.SourceCurrentParentNumeric
