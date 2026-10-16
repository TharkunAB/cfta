import MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryState

/-!
# Warm checked entry through the actual allocated precheck

The accessor and precheck use the current equality-operation state. Their
returned state retains the complete native machine and its memo tables.
Every branch has its original payload meaning. Live records retain their
source order and normalized trie facts. No input forest must be closed.
-/
namespace MicroCFTA.SourceCurrentAllocatedPrecheck
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityRequiredCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
variable {width : Nat}

/-- The actual equality prefix advances operations at the same constructor heap. -/
noncomputable def state (before : Checked width) (loaded : Allocated) (inherited : EqValue) : Checked width :=
  SourceCurrentAllocatedQueryMemo.advancePhysical before
    ⟨before.native.machine.heap, (runPrefix loaded.stored loaded.guard inherited before.operations).2⟩

/-- Updating only the equality operations retains the full native state. -/
theorem state_native (before : Checked width) (loaded : Allocated) (inherited : EqValue) :
    (state before loaded inherited).native = before.native := rfl

/-- The returned operations are the literal accessor and precheck result. -/
theorem state_operations (before : Checked width) (loaded : Allocated) (inherited : EqValue) :
    (state before loaded inherited).operations =
      (runPrefix loaded.stored loaded.guard inherited before.operations).2 := rfl

/-- A completed prefix retains the same native cells and actual allocation effects. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (own : EqValue) (branch : SourceEqualityPrecheck.Branch) : Prop where
  cached : SourceEqualityGuardReadback.Cached original.equalities
  load : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded)
  readback : SourceEqualityConjoinAllocation.readback loaded = original
  storedReady : EqReady before.operations.constraints loaded.stored
  constructor : SourceEqualityPhysicalPayload.read original.equalities = .ok loaded.stored.payload
  ownRead : SourceEqualityPhysicalPayload.own original = .ok own.payload
  ownClasses : SourceEqualityInheritedPayload.classes own.payload = SourceCompactGuards.sourceEqualities original
  actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok branch
  exact : SourceEqualityPrecheck.precheck own.payload inherited.payload = .ok branch
  entry : SourceEqualityPhysicalClassEntry.entry original inherited.payload = .ok branch
  operations : SourceEqualityConstraintMemoAllocation.Valid (state before loaded inherited).operations
  grows : SourceEqualityConstraintMemoAllocation.Grows before.operations (state before loaded inherited).operations
  effects : Effects (physical before) (physical (state before loaded inherited))
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine (state before loaded inherited).native.machine
  ready : Ready (state before loaded inherited)
  admitted : At formulas solver inventory (state before loaded inherited)

/-- A successful current load derives the complete warm precheck receipt. -/
theorem loaded_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (original : Guard) (cached : SourceEqualityGuardReadback.Cached original.equalities) (loaded : Allocated)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inherited : EqValue) (inheritedReady : EqReady before.operations.constraints inherited) :
    ∃ own branch, Receipt formulas solver inventory original loaded inherited before own branch := by
  have field := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
    ready.good.operations.constraints cached loaded found
  have built := SourceEqualityConstraintFieldLookup.load_constructor_receipt original before.operations.constraints cached loaded found
  obtain ⟨own, branch, ownRead, actual, exact, valid, grows⟩ :=
    SourceEqualityPartialPrecheckAllocation.run_correct loaded.stored loaded.guard inherited before.operations
      ready.good.operations field.1 inheritedReady original.equalities cached built
  have guard : loaded.guard = original.guard := congrArg SourceSymbolicIndex.Constraint.guard field.2
  have ownRead : SourceEqualityPhysicalPayload.own original = .ok own.payload := by
    simpa only [guard] using ownRead
  have ownClasses := (SourceEqualityPhysicalClassEntry.own_verified original cached own.payload ownRead).2
  have entry := (SourceEqualityPhysicalClassEntry.entry_of_own original inherited.payload own.payload ownRead).trans exact
  have nextReady : Ready (state before loaded inherited) :=
    SourceCurrentConjunctionAllocatedClassEntry.operations_ready before _ ready valid grows
  have effects : Effects (physical before) (physical (state before loaded inherited)) :=
    ⟨pure_keeps _ ready.semantic.ready,
      ⟨ready.semantic, ready.costs, valid, ready.good.fields.grows grows⟩, grows⟩
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before
    ⟨before.native.machine.heap, (runPrefix loaded.stored loaded.guard inherited before.operations).2⟩ effects
  exact ⟨own, branch, cached, found, field.2, field.1, built, ownRead, ownClasses,
    actual, exact, entry, valid, grows, effects, extension, nextReady, admitted.advance _ extension⟩

/-- Available fields derive their actual load and warm prefix without a supplied branch. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (original : Guard) (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations original)
    (inherited : EqValue) (inheritedReady : EqReady before.operations.constraints inherited) :
    ∃ loaded own branch, Receipt formulas solver inventory original loaded inherited before own branch := by
  obtain ⟨cached, loaded, found⟩ := field
  obtain ⟨own, branch, receipt⟩ := loaded_complete formulas solver inventory before ready admitted original cached loaded found inherited inheritedReady
  exact ⟨loaded, own, branch, receipt⟩

/-- A resident original edge supplies the current stored-field load itself. -/
theorem resident_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident before.native.machine.heap edge)
    (inherited : EqValue) (inheritedReady : EqReady before.operations.constraints inherited) :
    ∃ loaded own branch, Receipt formulas solver inventory edge.entry.key.constraint loaded inherited before own branch :=
  complete formulas solver inventory before ready admitted edge.entry.key.constraint
    (ready.good.fields edge.entry.key edge resident) inherited inheritedReady

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {original : Guard} {loaded : Allocated} {inherited own : EqValue}
variable {before : Checked width} {branch : SourceEqualityPrecheck.Branch}

/-- The actual own payload has exactly the independent source equality meaning. -/
theorem Receipt.own_exact (receipt : Receipt formulas solver inventory original loaded inherited before own branch)
    (term : Term Symbol) :
    SourceEqualityPrecheck.Sat term own.payload ↔
      SourceEqualityGuardReadback.Sat term (SourceCompactGuards.sourceEqualities original) := by
  rw [← receipt.ownClasses]
  exact (SourceEqualityInheritedPayload.classes_sat own.payload term).symm

/-- Complete guard acceptance implies the actual own payload, including residual guards. -/
theorem Receipt.own_accepted (receipt : Receipt formulas solver inventory original loaded inherited before own branch)
    (term : Term Symbol) (accepted : SourceEqualityPCSGuard.holds formulas solver original term = true) :
    SourceEqualityPrecheck.Sat term own.payload :=
  (receipt.own_exact term).mpr (SourceEqualityPCSGuard.own_sat formulas solver original term accepted)

/-- The normalized precheck combination denotes own and inherited obligations exactly. -/
theorem Receipt.combined_exact (receipt : Receipt formulas solver inventory original loaded inherited before own branch)
    (term : Term Symbol) :
    RunSat term (SourceEqualityPrecheck.combine own.payload inherited.payload) ↔
      SourceEqualityGuardReadback.Sat term (SourceCompactGuards.sourceEqualities original) ∧
        SourceEqualityPrecheck.Sat term inherited.payload :=
  (SourceEqualityPrecheck.combine_exact own.payload inherited.payload term).trans
    (and_congr (receipt.own_exact term) Iff.rfl)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem empty_payload (payload : SourceEqualityPrecheck.Constraint)
    (empty : SourceEqualityPrecheck.isEmpty payload = true) : payload = some [] := by
  cases payload with
  | none => cases empty
  | some records => cases records <;> simp_all [SourceEqualityPrecheck.isEmpty]

/-- The unchanged branch has two literal empty payloads; a residual guard remains separate. -/
theorem Receipt.unchanged (receipt : Receipt formulas solver inventory original loaded inherited before own branch)
    (same : branch = .unchanged) :
    own.payload = some [] ∧ inherited.payload = some [] ∧ SourceCompactGuards.sourceEqualities original = some [] := by
  have actual := receipt.exact
  rw [same] at actual
  unfold SourceEqualityPrecheck.precheck at actual
  split at actual
  · rename_i empty
    obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp empty
    have first := empty_payload own.payload first
    exact ⟨first, empty_payload inherited.payload second, by rw [← receipt.ownClasses, first]; rfl⟩
  · split at actual
    · cases actual
    · cases payload : own.payload with
      | none => simp [payload, SourceEqualityPrecheck.unsafeOrdered, Except.map] at actual
      | some records => simp [payload, SourceEqualityPrecheck.unsafeOrdered, Except.map] at actual

/-- Actual precheck rejection excludes every term satisfying both equality payloads. -/
theorem Receipt.empty_excludes (receipt : Receipt formulas solver inventory original loaded inherited before own branch)
    (same : branch = .emptyChildren) (term : Term Symbol) :
    ¬ (SourceEqualityGuardReadback.Sat term (SourceCompactGuards.sourceEqualities original) ∧
      SourceEqualityPrecheck.Sat term inherited.payload) := by
  intro satisfied
  exact SourceEqualityOnePassPrecheck.contradiction_rejects (receipt.exact.trans (congrArg Except.ok same)) term
    ⟨(receipt.own_exact term).mpr satisfied.1, satisfied.2⟩

/-- Precheck rejection also excludes complete original guards under inherited satisfaction. -/
theorem Receipt.empty_guard (receipt : Receipt formulas solver inventory original loaded inherited before own branch)
    (same : branch = .emptyChildren) (term : Term Symbol)
    (accepted : SourceEqualityPCSGuard.holds formulas solver original term = true) :
    ¬ SourceEqualityPrecheck.Sat term inherited.payload := by
  intro inheritedSat
  exact receipt.empty_excludes same term ⟨SourceEqualityPCSGuard.own_sat formulas solver original term accepted, inheritedSat⟩

/-- A live branch derives the literal original records, order, and every normalized trie fact. -/
theorem Receipt.classes (receipt : Receipt formulas solver inventory original loaded inherited before own branch)
    (output : List Record) (same : branch = .classes output) :
    (∀ paths ∈ output.map Record.paths, ∀ path ∈ paths, path ≠ []) ∧
      ∃ records, SourceEqualityPhysicalPayload.own original = .ok (some records) ∧
        SourceCompactGuards.sourceEqualities original = some (records.map Record.paths) ∧
        output = ordered records ∧
        ∀ record ∈ output, Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths := by
  have live := receipt.entry.trans (congrArg Except.ok same)
  obtain ⟨records, ownRead, classes, _, order, valid⟩ :=
    SourceEqualityPhysicalClassEntry.live_records original receipt.cached inherited.payload output live
  exact ⟨SourceEqualityPhysicalClassEntry.live_proper original receipt.cached inherited.payload output live,
    records, ownRead, classes, order, valid⟩

/-- Original equality satisfaction agrees with all returned live classes in their source order. -/
theorem Receipt.classes_exact (receipt : Receipt formulas solver inventory original loaded inherited before own branch)
    (output : List Record) (same : branch = .classes output) (term : Term Symbol) :
    Satisfies term (output.map Record.paths) ↔
      SourceEqualityGuardReadback.Sat term (SourceCompactGuards.sourceEqualities original) := by
  obtain ⟨_, records, _, classes, order, _⟩ := receipt.classes output same
  rw [classes, order]
  change Satisfies term ((ordered records).map Record.paths) ↔ Satisfies term (records.map Record.paths)
  have members (paths : Class) := ((ordered_perm records).map Record.paths).mem_iff (a := paths)
  exact ⟨fun satisfied paths member => satisfied paths ((members paths).mpr member),
    fun satisfied paths member => satisfied paths ((members paths).mp member)⟩

end MicroCFTA.SourceCurrentAllocatedPrecheck
