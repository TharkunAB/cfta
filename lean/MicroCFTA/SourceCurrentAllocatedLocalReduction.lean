import MicroCFTA.SourceCurrentAllocatedPrecheck
import MicroCFTA.SourceCurrentConjunctionScanClassPass

/-!
# Complete warm local child reduction

The actual allocated precheck selects unchanged children, empty children,
or the current Scan and its class continuation. Each continuation starts
at the literal precheck return. The full original guard and inherited
equalities imply exact forest language preservation. The graph describes
completed serial execution. It does not establish host demand order.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalReduction
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
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
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- The actual precheck selects exactly one local continuation. -/
inductive Reduction (budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    List (Value Symbol Guard) → Checked width → Fourth → Memo → Prop where
  | unchanged (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged) :
      Reduction budget loaded inherited values before fourth memo values (prefixState before loaded inherited) fourth memo
  | emptyChildren (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .emptyChildren) :
      Reduction budget loaded inherited values before fourth memo (EqualityLeafProjectionRuntimeEmpty.erase values)
        (prefixState before loaded inherited) fourth memo
  | classes {records outcome results after savedFourth saved}
      (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records))
      (continuation : SourceCurrentConjunctionScanClassPass.Reduction budget records values
        (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved) :
      Reduction budget loaded inherited values before fourth memo results after savedFourth saved

/-- Early returns make no global query; live returns retain the actual stage reads. -/
inductive Reads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {loaded : Allocated} → {inherited : EqValue} →
    {values results : List (Value Symbol Guard)} → {before after : Checked width} →
    {fourth savedFourth : Fourth} → {memo saved : Memo} →
    Reduction budget loaded inherited values before fourth memo results after savedFourth saved → Memos → Memos → Prop where
  | unchanged {budget loaded inherited values before fourth memo actual memos} :
      Reads formulas solver (Reduction.unchanged (budget := budget) (loaded := loaded) (inherited := inherited)
        (values := values) (before := before) (fourth := fourth) (memo := memo) actual) memos memos
  | emptyChildren {budget loaded inherited values before fourth memo actual memos} :
      Reads formulas solver (Reduction.emptyChildren (budget := budget) (loaded := loaded) (inherited := inherited)
        (values := values) (before := before) (fourth := fourth) (memo := memo) actual) memos memos
  | classes {budget loaded inherited values before fourth memo records outcome results after savedFourth saved actual}
      {continuation : SourceCurrentConjunctionScanClassPass.Reduction budget records values
        (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved} {memos final}
      (reads : SourceCurrentConjunctionScanClassPass.Reads formulas solver continuation memos final) :
      Reads formulas solver (Reduction.classes actual continuation) memos final

/-- Only a live actual precheck return requires Scan and class range plans. -/
def Ranges (budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) : Prop :=
  ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
    SourceCurrentConjunctionScanClassPass.Ranges budget records values (prefixState before loaded inherited) fourth memo

/-- Every local branch retains physical state and exact guarded forest membership. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values results : List (Value Symbol Guard)) (before after : Checked width)
    (fourth savedFourth : Fourth) (memo saved : Memo) (final : Memos) : Prop where
  precheck : ∃ initialInventory own branch,
    SourceCurrentAllocatedPrecheck.Receipt formulas solver initialInventory original loaded inherited before own branch
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  originals : Values after.native.machine.heap values
  available : Values after.native.machine.heap results
  length : results.length = values.length
  stored : SourceCurrentMemoMergeEffects.Stored after.native.machine.heap saved
  covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved
  retained : Extends memo saved
  globals : Valid after.native.machine.heap final
  correct : SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap savedFourth
  fourthRetained : SourceCurrentEmptinessMemo.Extends fourth savedFourth
  language : ∀ ambient symbol terms,
    (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
    (SourceEqualityPCSGuard.holds formulas solver original (.node symbol terms) = true →
      SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload →
      (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms))

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

/-- Initial warm invariants construct the precheck and every reached local stage. -/
theorem finite
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
    (ranges : Ranges budget loaded inherited values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after savedFourth saved next final,
      ∃ actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final := by
  obtain ⟨own, branch, checked⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before ready admitted original cached loaded found inherited inheritedReady
  cases branch with
  | unchanged =>
      refine ⟨values, prefixState before loaded inherited, fourth, memo, inventory, memos,
        .unchanged checked.actual, .unchanged (actual := checked.actual),
        ⟨inventory, own, .unchanged, checked⟩, checked.ready, checked.admitted, checked.effects, available, available,
        rfl, stored, covered, extends_refl _, valid, correct, (fun _ _ same => same), ?_⟩
      intro ambient symbol terms
      exact ⟨id, fun _ _ => Iff.rfl⟩
  | emptyChildren =>
      refine ⟨EqualityLeafProjectionRuntimeEmpty.erase values, prefixState before loaded inherited,
        fourth, memo, inventory, memos, .emptyChildren checked.actual, .emptyChildren (actual := checked.actual),
        ⟨inventory, own, .emptyChildren, checked⟩, checked.ready, checked.admitted, checked.effects, available,
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
      obtain ⟨outcome, results, after, savedFourth, saved, next, final, continuation, reads, receipt⟩ :=
        SourceCurrentConjunctionScanClassPass.finite formulas solver inventory budget records values
          (prefixState before loaded inherited) fourth memo checked.ready checked.admitted available
          recordsProper fields correct stored covered (ranges records checked.actual) memos valid
      refine ⟨results, after, savedFourth, saved, next, final, .classes checked.actual continuation,
        .classes (actual := checked.actual) reads,
        ?_, receipt.ready, receipt.admitted, checked.effects.trans receipt.effects, receipt.originals,
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

end MicroCFTA.SourceCurrentAllocatedLocalReduction
