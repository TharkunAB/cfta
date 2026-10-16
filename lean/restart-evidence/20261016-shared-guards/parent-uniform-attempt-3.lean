import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardOwn
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentResources

/-!
# Uniform parent row and arity envelopes

The initial own guard vector bounds the actual class list.
One common class transformer bounds each tail-first pass step.
The resulting row envelope depends only on the initial profile and vector.
The parent arity envelope includes the Empty sentinel.
These numeric comparisons do not construct an outer execution or capacity Plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers
open SourceEqualityClassOrder (Record)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryGuardOwn (classBudget pathDepth)
local notation "TargetRows" => SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.targetRows
local notation "PassRows" => SourceCurrentAllocatedFiniteOrdinaryPassResources.outputRows
local notation "PassArity" => SourceCurrentAllocatedFiniteOrdinaryPassResources.outputArity
local notation "ClassRows" => SourceCurrentAllocatedFiniteOrdinaryClassResources.outputRows

/-- One class permits the fixed path-count limit at its captured forest. -/
def classRows (paths rows count depth height : Nat) : Nat :=
  max (TargetRows rows count depth height paths) rows * max (TargetRows rows count depth height paths) rows

/-- Each class processes the profile returned by its literal tail. -/
def passRows (paths count depth height : Nat) : Nat → Nat → Nat
  | 0, rows => rows
  | classes + 1, rows => classRows paths (passRows paths count depth height classes rows) count depth height

/-- The initial raw guard vector bounds both class count and each class path count. -/
def parentRows (limits : Limits) (rows count height : Nat) : Nat :=
  passRows (classBudget limits) count (pathDepth limits) height (classBudget limits) rows

private theorem max_mono {a b c d : Nat} (first : a ≤ c) (second : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans first (Nat.le_max_left _ _), Nat.le_trans second (Nat.le_max_right _ _)⟩

/-- Every common class envelope retains its captured input rows. -/
theorem classRows_ge (paths rows count depth height : Nat) : rows ≤ classRows paths rows count depth height :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_mul_self _)

/-- Widening captured rows retains the common class envelope. -/
theorem classRows_mono (paths count depth height : Nat) {first last : Nat} (enough : first ≤ last) :
    classRows paths first count depth height ≤ classRows paths last count depth height := by
  have target := SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.targetRows_parameters_mono paths
    enough (Nat.le_refl count) (Nat.le_refl depth) (Nat.le_refl height)
  exact Nat.mul_le_mul (max_mono target enough) (max_mono target enough)

/-- Every literal class fits the common initial path-count envelope. -/
theorem class_rows (record : Record) (paths rows count depth height : Nat)
    (bounded : record.paths.length ≤ paths) :
    ClassRows record rows count depth height ≤ classRows paths rows count depth height := by
  have target : SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth height ≤
      TargetRows rows count depth height paths := by
    unfold SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
    cases tailCount : record.paths.length - 1 with
    | zero => simp only [SourceCurrentAllocatedFiniteOrdinaryTargetResources.outputRows]; exact Nat.zero_le _
    | succ remaining =>
        change TargetRows rows count depth height remaining ≤ _
        exact SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.targetRows_mono rows count depth height (by omega)
  exact Nat.mul_le_mul (max_mono target (Nat.le_refl rows)) (max_mono target (Nat.le_refl rows))

/-- Every uniform pass retains its initial row envelope. -/
theorem passRows_ge (paths count depth height classes rows : Nat) : rows ≤ passRows paths count depth height classes rows := by
  induction classes with
  | zero => exact Nat.le_refl _
  | succ classes ih => exact Nat.le_trans ih (classRows_ge _ _ _ _ _)

/-- Widening the initial rows retains every uniform pass envelope. -/
theorem passRows_rows_mono (paths count depth height classes : Nat) {first last : Nat} (enough : first ≤ last) :
    passRows paths count depth height classes first ≤ passRows paths count depth height classes last := by
  induction classes with
  | zero => exact enough
  | succ classes ih => exact classRows_mono paths count depth height ih

/-- More classes retain every earlier uniform pass envelope. -/
theorem passRows_count_mono (paths count depth height rows : Nat) {first last : Nat} (enough : first ≤ last) :
    passRows paths count depth height first rows ≤ passRows paths count depth height last rows := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (classRows_ge _ _ _ _ _)

private theorem pass_rows_exact (records : List Record) (paths rows count depth height : Nat)
    (bounded : ∀ record ∈ records, record.paths.length ≤ paths) :
    PassRows records rows count depth height ≤ passRows paths count depth height records.length rows := by
  induction records with
  | nil => exact Nat.le_refl _
  | cons record rest ih =>
      have tail := ih (fun value member => bounded value (List.mem_cons_of_mem record member))
      exact Nat.le_trans (class_rows record paths _ count depth height (bounded record List.mem_cons_self))
        (classRows_mono paths count depth height tail)

/-- Actual tail-first pass rows fit initial count and per-class path limits. -/
theorem pass_rows (records : List Record) (paths classes rows count depth height : Nat)
    (bounded : ∀ record ∈ records, record.paths.length ≤ paths) (length : records.length ≤ classes) :
    PassRows records rows count depth height ≤ passRows paths count depth height classes rows :=
  Nat.le_trans (pass_rows_exact records paths rows count depth height bounded)
    (passRows_count_mono paths count depth height rows length)

/-- Every class-pass arity is bounded by the original arity and the sentinel. -/
theorem pass_arity (records : List Record) (arity : Nat) : PassArity records arity ≤ max arity 1 := by
  induction records with
  | nil => exact Nat.le_max_left _ _
  | cons record rest ih =>
      change max (max (max (PassArity rest arity) 1) (PassArity rest arity)) 1 ≤ max arity 1
      exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨ih, Nat.le_max_right _ _⟩, ih⟩, Nat.le_max_right _ _⟩

variable [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
variable [DecidableEq (InternedConstructorTemplates.EdgeKey (SourceObservations.Label FullSyntax.Formula)
  (SourceSymbolicIndex.Constraint FullSyntax.Formula))]

/-- An actual allocated precheck derives a uniform row bound with no inherited-size premise. -/
theorem receipt_rows
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : SourceSymbolicIndex.Constraint FullSyntax.Formula}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : SourceEqualityConstraintAllocation.Value}
    {before : SourceEqualityNativeDemand.State width} {records : List Record}
    (actual : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own (.classes records))
    (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limits original)
    (rows count height : Nat) :
    PassRows records rows count (pathDepth limits) height ≤ parentRows limits rows count height := by
  have bounds := SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt actual limits profile
  exact pass_rows records (classBudget limits) (classBudget limits) rows count (pathDepth limits) height
    bounds.2.2.1 bounds.2.1

/-- The same precheck receipt bounds the actual local row selector in every branch. -/
theorem local_rows
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : SourceSymbolicIndex.Constraint FullSyntax.Formula}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : SourceEqualityConstraintAllocation.Value}
    {before : SourceEqualityNativeDemand.State width} {branch : SourceEqualityPrecheck.Branch}
    (actual : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own branch)
    (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limits original)
    (rows count height : Nat) :
    SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputRows loaded inherited before.operations
      rows count (pathDepth limits) height ≤ parentRows limits rows count height := by
  cases branch with
  | unchanged | emptyChildren =>
      simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputRows, actual.actual] using
        passRows_ge (classBudget limits) count (pathDepth limits) height (classBudget limits) rows
  | classes records =>
      simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputRows, actual.actual] using
        receipt_rows actual limits profile rows count height

/-- Raw rejection and the same allocated live prefix share the initial-only parent row envelope. -/
theorem parent_rows
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : SourceSymbolicIndex.Constraint FullSyntax.Formula}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : SourceEqualityConstraintAllocation.Value}
    {before : SourceEqualityNativeDemand.State width} {branch : SourceEqualityPrecheck.Branch}
    (actual : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own branch)
    (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limits original)
    (rows count height : Nat) :
    SourceCurrentAllocatedFiniteOrdinaryParentResources.outputRows original loaded inherited before.operations
      rows count (pathDepth limits) height ≤ parentRows limits rows count height := by
  unfold SourceCurrentAllocatedFiniteOrdinaryParentResources.outputRows
  split
  · exact passRows_ge (classBudget limits) count (pathDepth limits) height (classBudget limits) rows
  · exact local_rows actual limits profile rows count height

/-- Every actual local arity selector retains the original arity and sentinel ceiling. -/
theorem local_arity (loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (inherited : SourceEqualityConstraintAllocation.Value) (operations : SourceEqualityConstraintMemoAllocation.State)
    (arity : Nat) :
    SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputArity loaded inherited operations arity ≤ max arity 1 := by
  unfold SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputArity
  cases prefix : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited operations).1 with
  | error message => exact Nat.le_max_left _ _
  | ok branch =>
      cases branch with
      | unchanged | emptyChildren => exact Nat.le_max_left _ _
      | classes records => exact pass_arity records arity

/-- A parent with at most the original arity children needs only the sentinel ceiling. -/
theorem parent_arity (original : SourceSymbolicIndex.Constraint FullSyntax.Formula)
    (loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (inherited : SourceEqualityConstraintAllocation.Value) (operations : SourceEqualityConstraintMemoAllocation.State)
    (arity count : Nat) (bounded : count ≤ arity) :
    SourceCurrentAllocatedFiniteOrdinaryParentResources.outputArity original loaded inherited operations arity count ≤ max arity 1 := by
  unfold SourceCurrentAllocatedFiniteOrdinaryParentResources.outputArity
  split
  · exact Nat.le_refl _
  · exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨local_arity loaded inherited operations arity,
      Nat.le_trans bounded (Nat.le_max_left _ _)⟩, Nat.le_max_right _ _⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers
