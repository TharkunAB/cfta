import MicroCFTA.SourceCurrentAllocatedLocalReduction
import MicroCFTA.SourceCurrentAllocatedMkEdge

/-!
# Checked local reduction followed by the actual parent constructor

Raw contradiction selects the sentinel before any local child reduction.
The live branch runs the current local reduction and then the checked edge
constructor at its literal returned state. Equality operations can grow in
both constructors. Native tables and all completed memo families remain in
the same serial execution. Outer inherited-child recursion and runtime
forcing remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedParentEdge
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning edgeMeaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
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

/-- Raw rejection skips the local child graph; live construction uses its actual return. -/
inductive Edge (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated)
    (inherited : EqValue) (values : List (Value Symbol Guard)) (before : Checked width)
    (fourth : Fourth) (memo : Memo) : EdgeValue Symbol Guard → Checked width → Fourth → Memo → Prop where
  | rejected (test : contradictory original = true) :
      Edge budget symbol original loaded inherited values before fourth memo
        (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo
  | live {children middle savedFourth saved result after}
      (test : contradictory original = false)
      (reduction : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
        children middle savedFourth saved)
      (built : SourceCurrentAllocatedMkEdge.build symbol loaded children middle = (.ok result, after)) :
      Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved

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
      (reads : SourceCurrentAllocatedLocalReduction.Reads formulas solver reduction memos final) :
      Reads formulas solver (Edge.live (original := original) (symbol := symbol) test reduction built) memos final

/-- Local range plans apply only after the raw constructor contradiction test passes. -/
def Ranges (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) : Prop :=
  contradictory original = false → SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo

/-- Interpret the original raw edge without replacing its stored field by its accessor. -/
def RawMeaning (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (original : Guard) (values : List (Value Symbol Guard)) (term : Term Symbol) : Prop :=
  ∃ terms, term = .node symbol terms ∧ All₂ (meaning holds ambient) values terms ∧ holds original term = true

/-- The actual parent return retains physical and completed-cache invariants. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (result : EdgeValue Symbol Guard)
    (after : Checked width) (fourth savedFourth : Fourth) (memo saved : Memo) (final : Memos) : Prop where
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  resident : InternedEdgeResidency.EdgeResident after.native.machine.heap result
  stored : SourceCurrentMemoMergeEffects.Stored after.native.machine.heap saved
  covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved
  retained : Extends memo saved
  globals : Valid after.native.machine.heap final
  correct : SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap savedFourth
  fourthRetained : SourceCurrentEmptinessMemo.Extends fourth savedFourth
  construction : SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol before result after ∨
    ∃ children middle, children.length = values.length ∧
      SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol loaded children middle result after
  language : ∀ ambient term,
    (edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
      RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term) ∧
    (SourceEqualityPrecheck.Sat term inherited.payload →
      (edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term))

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem raw_rejected (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (symbol : Symbol) (original : Guard)
    (values : List (Value Symbol Guard)) (test : contradictory original = true)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    ¬ RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term := by
  rintro ⟨_, _, _, accepted⟩
  obtain ⟨sat, guard⟩ := (SourceEqualityPCSGuard.holds_exact formulas solver original term).mp accepted
  cases original with
  | mk equalities termGuard =>
      cases equalities with
      | none => exact sat
      | some records =>
          cases termGuard <;> solve
            | cases test
            | simp [SourceBooleanEntry.evaluateGuard, SourceBooleanEntry.evaluateGuardWithSame,
                SourceBooleanEntry.evaluate, SourceBooleanEntry.scoped_eq, SourceGuards.evaluateWith,
                SourceGuards.polarize] at guard

/-- Raw contradiction constructs its return without any local range or child-availability premise. -/
theorem rejected (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (test : contradictory original = true)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ actual : Edge budget symbol original loaded inherited values before fourth memo
        (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo,
      Reads formulas solver actual memos memos ∧ Receipt formulas solver inventory symbol original loaded inherited values before
        (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth fourth memo memo memos := by
  have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory symbol before ready admitted
  refine ⟨.rejected test, .rejected (test := test), constructor.ready, constructor.admitted, constructor.effects, constructor.resident,
    stored.grows constructor.effects.keeps, covered, extends_refl _,
    SourceQueryUnfoldMemo.valid_grows _ _ ready.semantic constructor.effects.keeps memos valid,
    SourceCurrentEmptinessMemo.grows formulas solver constructor.effects.keeps fourth correct,
    (fun _ _ found => found), Or.inl constructor, ?_⟩
  intro ambient term
  have empty := constructor.empty (SourceEqualityPCSGuard.holds formulas solver) ambient term
  have originalEmpty := raw_rejected formulas solver symbol original values test ambient term
  exact ⟨fun accepted => False.elim (empty accepted), fun _ => ⟨fun accepted => False.elim (empty accepted),
    fun accepted => False.elim (originalEmpty accepted)⟩⟩

/-- Initial warm invariants construct the exact raw-test, local-reduction, and edge-constructor order. -/
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
    (ranges : Ranges budget original loaded inherited values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after savedFourth saved next final,
      ∃ actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next symbol original loaded inherited values before result after fourth savedFourth memo saved final := by
  cases test : contradictory original with
  | true =>
      obtain ⟨actual, reads, receipt⟩ := rejected formulas solver inventory budget symbol original loaded inherited values
        before fourth memo ready admitted test correct stored covered memos valid
      exact ⟨_, _, fourth, memo, inventory, memos, actual, reads, receipt⟩
  | false =>
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨children, middle, savedFourth, saved, next, final, reduction, reads, receipt⟩ :=
        SourceCurrentAllocatedLocalReduction.finite formulas solver inventory budget original loaded inherited values before
          fourth memo ready admitted cached found inheritedReady available correct stored covered (ranges test) memos valid
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original from ⟨cached, loaded, found⟩).grows
          receipt.effects.grows
      obtain ⟨result, after, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next symbol loaded children middle
        receipt.ready receipt.admitted storedReady field receipt.available
      refine ⟨result, after, savedFourth, saved, next, final, .live test reduction constructor.actual,
        .live (test := test) (built := constructor.actual) reads,
        constructor.ready, constructor.admitted, receipt.effects.trans constructor.effects, constructor.resident,
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

end MicroCFTA.SourceCurrentAllocatedParentEdge
