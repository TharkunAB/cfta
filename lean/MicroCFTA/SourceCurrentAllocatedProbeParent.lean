import MicroCFTA.SourceCurrentAllocatedProbeReduction

/-!
# Filtered probes through finite local reduction and parent construction

The construction retains the literal returned checked state at each stage.
It derives probe preservation from the reached Scan, required worker, class
pass, and edge constructor. Initial probe validity remains explicit.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeParent
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
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
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem erased_narrows (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (values : List (Value Symbol Guard)) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) (EqualityLeafProjectionRuntimeEmpty.erase values) terms →
      All₂ (meaning holds ambient) values terms := by
  cases values with
  | nil => exact id
  | cons value values =>
      intro accepted
      cases accepted with
      | cons impossible _ => simp only [meaning] at impossible

/-- The actual local reduction preserves filtered probes on every finite branch. -/
theorem local_finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (probes : ProbeHeap before.native.machine.heap) :
    ∃ results after savedFourth saved next final,
      ∃ actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo results after savedFourth saved,
        SourceCurrentAllocatedLocalReduction.Reads formulas solver actual memos final ∧
        SourceCurrentAllocatedLocalReduction.Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final ∧
        ProbeHeap after.native.machine.heap := by
  obtain ⟨own, branch, checked⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before ready admitted original cached loaded found inherited inheritedReady
  cases branch with
  | unchanged =>
      refine ⟨values, prefixState before loaded inherited, fourth, memo, inventory, memos,
        .unchanged checked.actual, .unchanged (actual := checked.actual), ?_, probes⟩
      refine ⟨⟨inventory, own, .unchanged, checked⟩, checked.ready, checked.admitted, checked.effects, available, available,
        rfl, stored, covered, extends_refl _, valid, correct, (fun _ _ same => same), ?_⟩
      intro ambient symbol terms
      exact ⟨id, fun _ _ => Iff.rfl⟩
  | emptyChildren =>
      refine ⟨EqualityLeafProjectionRuntimeEmpty.erase values, prefixState before loaded inherited,
        fourth, memo, inventory, memos, .emptyChildren checked.actual, .emptyChildren (actual := checked.actual), ?_, probes⟩
      refine ⟨⟨inventory, own, .emptyChildren, checked⟩, checked.ready, checked.admitted, checked.effects, available,
        (SourceEqualityEmptyPropagation.erased_scope before.native.machine.heap values).1,
        List.length_map _, stored, covered, extends_refl _, valid, correct, (fun _ _ same => same), ?_⟩
      intro ambient symbol terms
      have narrows := erased_narrows (SourceEqualityPCSGuard.holds formulas solver) ambient values terms
      exact ⟨narrows, fun guard inheritedSat => False.elim (checked.empty_guard rfl _ guard inheritedSat)⟩
  | classes records =>
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      obtain ⟨outcome, results, after, savedFourth, saved, next, final, continuation, reads, receipt, finalProbes⟩ :=
        SourceCurrentAllocatedProbeReduction.finite formulas solver inventory budget records values
          (prefixState before loaded inherited) fourth memo checked.ready checked.admitted available
          recordsProper fields correct stored covered (ranges records checked.actual) memos valid probes
      refine ⟨results, after, savedFourth, saved, next, final, .classes checked.actual continuation,
        .classes (actual := checked.actual) reads, ?_, finalProbes⟩
      refine ⟨?_, receipt.ready, receipt.admitted, checked.effects.trans receipt.effects, receipt.originals,
        receipt.available, receipt.length, receipt.stored, receipt.covered, receipt.retained,
        receipt.globals, receipt.correct, receipt.fourthRetained, ?_⟩
      · exact ⟨inventory, own, .classes records, checked⟩
      · intro ambient symbol terms
        have language := receipt.language ambient symbol terms
        refine ⟨language.1, fun guard _ => language.2 ?_⟩
        have satisfied := (checked.classes_exact records rfl (.node symbol terms)).mpr
          (SourceEqualityPCSGuard.own_sat formulas solver original (.node symbol terms) guard)
        intro record member
        exact satisfied record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- Edge requests retain all node records on successful and failed constructor paths. -/
theorem mkEdge_heap (symbol : Symbol) (loaded : Allocated) (children : List (Value Symbol Guard))
    (before : Checked width) (probes : ProbeHeap before.native.machine.heap) :
    ProbeHeap (SourceCurrentAllocatedMkEdge.build symbol loaded children before).2.native.machine.heap := by
  change ProbeHeap (SourceEqualityMkEdgeAllocation.build symbol loaded.stored loaded.guard children
    before.operations before.native.machine.heap).2.2
  unfold SourceEqualityMkEdgeAllocation.build
  dsimp only
  cases result : (SourceEqualityMkEdgeAllocation.check loaded.stored loaded.guard children.length before.operations).1 with
  | error message => exact probes
  | ok keep =>
      cases keep <;> simp only [SourceEqualityMkEdgeAllocation.work, Bool.false_eq_true,
        ↓reduceIte] <;> exact probes

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- The contradiction sentinel retains all node records without forcing children. -/
theorem reject_heap (symbol : Symbol) (before : Checked width)
    (probes : ProbeHeap before.native.machine.heap) :
    ProbeHeap (SourceCurrentAllocatedMkEdge.reject symbol before).2.native.machine.heap := by
  exact probes

/-- Initial warm invariants derive the actual parent return and its filtered probes. -/
theorem parent_finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (probes : ProbeHeap before.native.machine.heap) :
    ∃ result after savedFourth saved next final,
      ∃ actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved,
        SourceCurrentAllocatedParentEdge.Reads formulas solver actual memos final ∧
        SourceCurrentAllocatedParentEdge.Receipt formulas solver next symbol original loaded inherited values before result after fourth savedFourth memo saved final ∧
        ProbeHeap after.native.machine.heap := by
  cases test : contradictory original with
  | true =>
      obtain ⟨actual, reads, receipt⟩ := SourceCurrentAllocatedParentEdge.rejected formulas solver inventory budget symbol original loaded inherited values
        before fourth memo ready admitted test correct stored covered memos valid
      exact ⟨_, _, fourth, memo, inventory, memos, actual, reads, receipt, reject_heap symbol before probes⟩
  | false =>
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨children, middle, savedFourth, saved, next, final, reduction, reads, receipt, middleProbes⟩ :=
        local_finite formulas solver inventory budget original loaded inherited values before
          fourth memo ready admitted cached found inheritedReady available correct stored covered (ranges test) memos valid probes
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original from ⟨cached, loaded, found⟩).grows
          receipt.effects.grows
      obtain ⟨result, after, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next symbol loaded children middle
        receipt.ready receipt.admitted storedReady field receipt.available
      have finalProbes := mkEdge_heap symbol loaded children middle middleProbes
      rw [constructor.actual] at finalProbes
      refine ⟨result, after, savedFourth, saved, next, final, .live test reduction constructor.actual,
        .live (test := test) (built := constructor.actual) reads, ?_, finalProbes⟩
      refine ⟨constructor.ready, constructor.admitted, receipt.effects.trans constructor.effects, constructor.resident,
        receipt.stored.grows constructor.effects.keeps, receipt.covered, receipt.retained,
        SourceQueryUnfoldMemo.valid_grows _ _ receipt.ready.semantic constructor.effects.keeps final receipt.globals,
        SourceCurrentEmptinessMemo.grows formulas solver constructor.effects.keeps savedFourth receipt.correct,
        receipt.fourthRetained, Or.inr ⟨children, middle, receipt.length, constructor⟩, ?_⟩
      intro ambient term
      have edgeLaw := constructor.language storedReady ambient term
      rw [loadedReady.2] at edgeLaw
      have narrows : edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
          SourceCurrentAllocatedParentEdge.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term := by
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

end MicroCFTA.SourceCurrentAllocatedProbeParent
