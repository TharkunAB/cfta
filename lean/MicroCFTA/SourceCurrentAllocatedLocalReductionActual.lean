import MicroCFTA.SourceCurrentConjunctionScanClassPassActual
import MicroCFTA.SourceCurrentAllocatedLocalReduction

/-!
# Receipts for the supplied allocated local reduction

The actual precheck selects the same branch as its derived allocation
receipt. A live branch uses the supplied Scan and class continuation.
The theorem retains its exact children, checked state, and memo tables.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalReductionActual
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
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
      (reads : SourceCurrentConjunctionScanClassPassActual.Reads formulas solver continuation memos final) :
      Reads formulas solver (Reduction.classes actual continuation) memos final


/-- Source-refined reads retain the actual historical precheck and continuation. -/
theorem Reads.erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    {actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved}
    {memos final : Memos} (reads : Reads formulas solver actual memos final) :
    SourceCurrentAllocatedLocalReduction.Reads formulas solver actual memos final := by
  cases reads with
  | unchanged => exact .unchanged (actual := by assumption)
  | emptyChildren => exact .emptyChildren (actual := by assumption)
  | classes actual => exact .classes (actual := by assumption) actual.erase

/-- Only actual live precheck returns require the reached Scan range checks. -/
def Ranges (budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) : Prop :=
  ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
    SourceCurrentConjunctionClassScanCompletion.Ranges budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map SourceEqualityClassOrder.Record.paths) (prefixState before loaded inherited) fourth

/-- Existing finite plans supply the smaller actual-verification plan. -/
theorem ranges_of_finite
    {budget : Nat} {loaded : Allocated} {inherited : EqValue} {values : List (Value Symbol Guard)}
    {before : Checked width} {fourth : Fourth} {memo : Memo}
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo) :
    Ranges budget loaded inherited values before fourth := fun records actual => (ranges records actual).scan

omit [DecidableEq (Value Symbol Guard)] in
/-- The actual completed prefix derives its own branch receipt from the current stored field. -/
theorem prefix_verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    {branch : SourceEqualityPrecheck.Branch}
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok branch) :
    ∃ own, SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own branch := by
  obtain ⟨own, chosen, receipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before ready admitted original cached loaded found inherited inheritedReady
  have same := Except.ok.inj (receipt.actual.symm.trans actual)
  cases same
  exact ⟨own, receipt⟩

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

/-- Actual local reads derive physical and language receipts without a final invariant premise. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges budget loaded inherited values before fourth)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final := by
  cases reads with
  | unchanged =>
      rename_i actual
      obtain ⟨own, checked⟩ := prefix_verified formulas solver inventory before original loaded inherited
        ready admitted cached found inheritedReady actual
      refine ⟨inventory, ⟨inventory, own, .unchanged, checked⟩, checked.ready, checked.admitted, checked.effects,
        available, available, rfl, stored, covered, extends_refl _, valid, correct, (fun _ _ same => same), ?_⟩
      intro ambient symbol terms
      exact ⟨id, fun _ _ => Iff.rfl⟩
  | emptyChildren =>
      rename_i actual
      obtain ⟨own, checked⟩ := prefix_verified formulas solver inventory before original loaded inherited
        ready admitted cached found inheritedReady actual
      refine ⟨inventory, ⟨inventory, own, .emptyChildren, checked⟩, checked.ready, checked.admitted, checked.effects,
        available, (SourceEqualityEmptyPropagation.erased_scope before.native.machine.heap values).1,
        List.length_map _, stored, covered, extends_refl _, valid, correct, (fun _ _ same => same), ?_⟩
      intro ambient symbol terms
      have narrows := erased_narrows (SourceEqualityPCSGuard.holds formulas solver) ambient values terms
      exact ⟨narrows, fun guard inheritedSat => False.elim (checked.empty_guard rfl _ guard inheritedSat)⟩
  | classes reads =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := prefix_verified formulas solver inventory before original loaded inherited
        ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      obtain ⟨next, receipt⟩ := SourceCurrentConjunctionScanClassPassActual.verified formulas solver inventory
        reads checked.ready checked.admitted available recordsProper fields correct stored covered
          (ranges records checked.actual) valid
      refine ⟨next, ⟨inventory, own, .classes records, checked⟩, receipt.ready, receipt.admitted,
        checked.effects.trans receipt.effects, receipt.originals, receipt.available, receipt.length,
        receipt.stored, receipt.covered, receipt.retained, receipt.globals, receipt.correct,
        receipt.fourthRetained, ?_⟩
      intro ambient symbol terms
      have language := receipt.language ambient symbol terms
      refine ⟨language.1, fun guard _ => language.2 ?_⟩
      have satisfied := (checked.classes_exact records rfl (.node symbol terms)).mpr
        (SourceEqualityPCSGuard.own_sat formulas solver original (.node symbol terms) guard)
      intro record member
      exact satisfied record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)

/-- Initial stored-field invariants and finite plans construct a strict actual local schedule. -/
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
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after savedFourth saved next final,
      ∃ actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final := by
  have checks := ranges_of_finite ranges
  obtain ⟨own, branch, checked⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before ready admitted original cached loaded found inherited inheritedReady
  cases branch with
  | unchanged =>
      let actual : Reduction budget loaded inherited values before fourth memo values
          (prefixState before loaded inherited) fourth memo := .unchanged checked.actual
      have read : Reads formulas solver actual memos memos := .unchanged (actual := checked.actual)
      obtain ⟨next, receipt⟩ := verified formulas solver inventory original read ready admitted cached found
        inheritedReady available correct stored covered checks valid
      exact ⟨_, _, _, _, next, memos, actual, read, receipt⟩
  | emptyChildren =>
      let actual : Reduction budget loaded inherited values before fourth memo
          (EqualityLeafProjectionRuntimeEmpty.erase values) (prefixState before loaded inherited) fourth memo :=
        .emptyChildren checked.actual
      have read : Reads formulas solver actual memos memos := .emptyChildren (actual := checked.actual)
      obtain ⟨next, receipt⟩ := verified formulas solver inventory original read ready admitted cached found
        inheritedReady available correct stored covered checks valid
      exact ⟨_, _, _, _, next, memos, actual, read, receipt⟩
  | classes records =>
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      obtain ⟨outcome, results, after, savedFourth, saved, next, final, continuation, stageRead, _⟩ :=
        SourceCurrentConjunctionScanClassPassActual.finite formulas solver inventory budget records values
          (prefixState before loaded inherited) fourth memo checked.ready checked.admitted available
          recordsProper fields correct stored covered (ranges records checked.actual) memos valid
      let actual := Reduction.classes checked.actual continuation
      have read : Reads formulas solver actual memos final := .classes (actual := checked.actual) stageRead
      obtain ⟨finalInventory, receipt⟩ := verified formulas solver inventory original read ready admitted cached found
        inheritedReady available correct stored covered checks valid
      exact ⟨results, after, savedFourth, saved, finalInventory, final, actual, read, receipt⟩

end MicroCFTA.SourceCurrentAllocatedLocalReductionActual
