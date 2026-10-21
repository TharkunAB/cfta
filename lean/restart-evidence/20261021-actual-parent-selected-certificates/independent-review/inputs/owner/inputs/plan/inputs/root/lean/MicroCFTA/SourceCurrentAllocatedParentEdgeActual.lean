import MicroCFTA.SourceCurrentAllocatedLocalReductionActual
import MicroCFTA.SourceCurrentAllocatedParentEdge

/-!
# Receipts for the supplied actual parent-edge return

The actual raw rejection has no child or local-range premise. A live
return uses the supplied local reads and literal checked constructor.
The returned receipt describes that same edge and full checked state.
-/
namespace MicroCFTA.SourceCurrentAllocatedParentEdgeActual
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning edgeMeaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedParentEdge (Edge Receipt RawMeaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Only the reached live local graph demands global memo reads. -/
inductive Reads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {symbol : Symbol} → {original : Guard} → {loaded : Allocated} → {inherited : EqValue} →
    {values : List (Value Symbol Guard)} → {before after : Checked width} → {result : EdgeValue Symbol Guard} →
    {fourth savedFourth : Fourth} → {memo saved : Memo} →
    Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved → Memos → Memos → Prop where
  | rejected {budget symbol original loaded inherited values before fourth memo test memos} :
      Reads formulas solver (Edge.rejected (budget := budget) (symbol := symbol) (original := original)
        (loaded := loaded) (inherited := inherited) (values := values) (before := before)
        (fourth := fourth) (memo := memo) test) memos memos
  | live {budget symbol original loaded inherited values before fourth memo children middle savedFourth saved result after test}
      {reduction : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
        children middle savedFourth saved}
      {built : SourceCurrentAllocatedMkEdge.build symbol loaded children middle = (.ok result, after)} {memos final}
      (reads : SourceCurrentAllocatedLocalReductionActual.Reads formulas solver reduction memos final) :
      Reads formulas solver (Edge.live (original := original) (symbol := symbol) test reduction built) memos final


/-- Source-refined reads retain the literal parent trace and every returned table. -/
theorem Reads.erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo}
    {actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    {memos final : Memos} (reads : Reads formulas solver actual memos final) :
    SourceCurrentAllocatedParentEdge.Reads formulas solver actual memos final := by
  cases reads with
  | rejected => exact .rejected (test := by assumption)
  | live actual => exact .live (test := by assumption) (built := by assumption) actual.erase

/-- Initial invariants and reached live inputs derive the receipt for the supplied actual edge. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next symbol original loaded inherited values before result after fourth savedFourth memo saved final := by
  cases reads with
  | rejected =>
      rename_i test
      obtain ⟨_, _, receipt⟩ := SourceCurrentAllocatedParentEdge.rejected formulas solver inventory budget symbol original
        loaded inherited values before fourth memo ready admitted test correct stored covered memos valid
      exact ⟨inventory, receipt⟩
  | live reads =>
      rename_i children middle test built reduction
      obtain ⟨cached, found, inheritedReady, available, ranges⟩ := live test
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original
        reads ready admitted cached found inheritedReady available correct stored covered ranges valid
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original from ⟨cached, loaded, found⟩).grows
          receipt.effects.grows
      obtain ⟨chosen, returned, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next symbol loaded children middle
        receipt.ready receipt.admitted storedReady field receipt.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      have sameValue := Except.ok.inj same.1
      cases sameValue
      cases same.2
      refine ⟨next, constructor.ready, constructor.admitted, receipt.effects.trans constructor.effects, constructor.resident,
        receipt.stored.grows constructor.effects.keeps, receipt.covered, receipt.retained,
        SourceQueryUnfoldMemo.valid_grows _ _ receipt.ready.semantic constructor.effects.keeps final receipt.globals,
        SourceCurrentEmptinessMemo.grows formulas solver constructor.effects.keeps savedFourth receipt.correct,
        receipt.fourthRetained, Or.inr ⟨children, middle, receipt.length, constructor⟩, ?_⟩
      intro ambient term
      have edgeLaw := constructor.language storedReady ambient term
      rw [loadedReady.2] at edgeLaw
      have narrows : edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
          RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term := by
        intro accepted
        obtain ⟨terms, shape, forest, guard⟩ := edgeLaw.mp accepted
        exact ⟨terms, shape, (receipt.language ambient symbol terms).1 forest, guard⟩
      refine ⟨narrows, fun inheritedSat => ⟨narrows, ?_⟩⟩
      rintro ⟨terms, shape, forest, guard⟩
      apply edgeLaw.mpr
      refine ⟨terms, shape, ?_, guard⟩
      have guards : SourceEqualityPCSGuard.holds formulas solver original (.node symbol terms) = true := by
        simpa only [shape] using guard
      have inheritedSat : SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload := by
        simpa only [shape] using inheritedSat
      exact ((receipt.language ambient symbol terms).2 guards inheritedSat).mpr forest

/-- Finite reached plans construct strict source reads and the same actual parent receipt. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedParentEdge.Ranges budget original loaded inherited values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after savedFourth saved next final,
      ∃ actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next symbol original loaded inherited values before result after fourth savedFourth memo saved final := by
  have liveInputs : contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth :=
    fun test => ⟨cached, found, inheritedReady, available,
      SourceCurrentAllocatedLocalReductionActual.ranges_of_finite (ranges test)⟩
  cases test : contradictory original with
  | true =>
      let actual : Edge budget symbol original loaded inherited values before fourth memo
          (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2
          fourth memo := .rejected test
      have read : Reads formulas solver actual memos memos := .rejected (test := test)
      obtain ⟨next, receipt⟩ := verified formulas solver inventory read ready admitted liveInputs correct stored covered valid
      exact ⟨_, _, _, _, next, memos, actual, read, receipt⟩
  | false =>
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨children, middle, savedFourth, saved, next, final, reduction, localRead, receipt⟩ :=
        SourceCurrentAllocatedLocalReductionActual.finite formulas solver inventory budget original loaded inherited values before
          fourth memo ready admitted cached found inheritedReady available correct stored covered (ranges test) memos valid
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original from ⟨cached, loaded, found⟩).grows
          receipt.effects.grows
      obtain ⟨result, after, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next symbol loaded children middle
        receipt.ready receipt.admitted storedReady field receipt.available
      let actual := Edge.live (original := original) (symbol := symbol) test reduction constructor.actual
      have read : Reads formulas solver actual memos final :=
        .live (test := test) (built := constructor.actual) localRead
      obtain ⟨finalInventory, receipt⟩ := verified formulas solver inventory read ready admitted liveInputs correct stored covered valid
      exact ⟨result, after, savedFourth, saved, finalInventory, final, actual, read, receipt⟩

end MicroCFTA.SourceCurrentAllocatedParentEdgeActual
