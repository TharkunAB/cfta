import MicroCFTA.SourceCurrentAllocatedMergePhysical
import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceCurrentAllocatedNativeInventoryState
import MicroCFTA.SourceCurrentMemoMergeLanguage
import MicroCFTA.SourceCurrentMemoMergeQueryMemos

/-!
# Allocated merge calls in the current checked state

The actual merge graph advances the constructor heap and equality operations.
Both native tables and the domain cache remain in the same checked state.
Generated results enter the input inventory when a later query requests them.
The completed selection primitive and its runtime demand adapter remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedMerge
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical advance_extension)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (Covers CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat}

/-- The source comparison accepts only the literal unconstrained raw field. -/
noncomputable def literalClear (constraint : Guard) : Bool := by
  classical
  exact decide (constraint = top)

/-- The independent PCS interpretation accepts Top without a storage premise. -/
theorem top_true (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (term : Term Symbol) :
    SourceEqualityPCSGuard.holds formulas solver top term = true := by
  rw [SourceEqualityPCSGuard.public_eq formulas solver top
    (SourceEqualityGuardReadback.active SourceEqualityConstraintConstructors.top_cached)]
  exact SourceEqualityConstraintConstructors.top_true formulas solver term

/-- A literal source clear test derives independent constraint truth. -/
theorem literalClear_true (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (constraint : Guard)
    (cleared : literalClear constraint = true) (term : Term Symbol) :
    SourceEqualityPCSGuard.holds formulas solver constraint term = true := by
  classical
  have same : constraint = top := of_decide_eq_true cleared
  subst constraint
  exact top_true formulas solver term

/-- A normalized clear guard need not be the literal source Top field. -/
theorem normalized_clear_boundary :
    SourceMemoGate.plain (⟨some [], .and []⟩ : Guard) = true ∧
      literalClear (⟨some [], .and []⟩ : Guard) = false := by
  constructor
  · rfl
  · simp [literalClear, SourceEqualityConstraintConstructors.top]

/-- A completed merge retains the full checked state and actual allocation graph. -/
inductive Merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) :
    Value Symbol Guard → Checked width → Memo → Value Symbol Guard → Checked width → Memo → Prop where
  | done (actual : SourceCurrentAllocatedMergeGraph.Call clear input (physical before) memo output after saved) :
      Merge clear input before memo output (advancePhysical before after) saved

/-- One actual call supplies physical, inventory, language, and global table receipts. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (clear : Guard → Bool) (input : Value Symbol Guard)
    (before : Checked width) (memo : Memo) (output : Value Symbol Guard) (after : Checked width)
    (saved : Memo) (memos final : Memos) : Prop where
  actual : Merge clear input before memo output after saved
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  stored : Stored after.native.machine.heap saved
  available : Available after.native.machine.heap output
  closed : input.free = [] → output.free = []
  nodes : after.native.nodes = before.native.nodes
  edges : after.native.edges = before.native.edges
  domains : after.native.machine.domains = before.native.machine.domains
  retained : Extends memo saved
  covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved
  included : ∀ ambient, Covers (SourceEqualityPCSGuard.holds formulas solver) ambient input output
  reads : SourceCurrentMemoMergeQueryMemos.CallReads clear top input before.native.machine.heap memo
    output after.native.machine.heap saved memos final
  globals : SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap after.native.machine.heap memos final

/-- Initial checked invariants derive every returned receipt from the same actual merge. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (clear : Guard → Bool)
    (clearTrue : ∀ constraint, clear constraint = true → ∀ term,
      SourceEqualityPCSGuard.holds formulas solver constraint term = true)
    {input output : Value Symbol Guard} {before after : Checked width} {memo saved : Memo}
    (actual : Merge clear input before memo output after saved) (ready : Ready before)
    (admitted : At formulas solver inventory before) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (available : Available before.native.machine.heap input) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final, Receipt formulas solver inventory clear input before memo output after saved memos final := by
  cases actual with
  | done call =>
      have initial : SourceCurrentConjunctionRowsAllocation.Ready (physical before) :=
        ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩
      obtain ⟨effects, finalStored, returned, closed⟩ := call.verified initial stored available
      have old := call.graph
      obtain ⟨final, reads, globals, _, _, _⟩ := SourceCurrentMemoMergeQueryMemos.call_memos
        old ready.semantic ready.costs stored available memos valid
      have languages := fun ambient => SourceCurrentMemoMergeLanguage.call_language clear top
        (SourceEqualityPCSGuard.holds formulas solver) ambient clearTrue (top_true formulas solver)
        old ready.semantic ready.costs stored (covered ambient) available
      have extension := advance_extension before _ effects
      exact ⟨final, ⟨.done call,
        SourceCurrentConjunctionClassScan.advance_ready before _ ready effects,
        admitted.advance _ extension, effects, extension, finalStored, returned, closed,
        rfl, rfl, rfl, old.extends, fun ambient => (languages ambient).2.2.1,
        fun ambient => (languages ambient).2.2.2.2, reads, globals⟩⟩

/-- Initial warm tables construct the allocated merge and its full checked return. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (clear : Guard → Bool)
    (clearTrue : ∀ constraint, clear constraint = true → ∀ term,
      SourceEqualityPCSGuard.holds formulas solver constraint term = true)
    (input : Value Symbol Guard) (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (available : Available before.native.machine.heap input) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ output after saved final, Receipt formulas solver inventory clear input before memo output after saved memos final := by
  have initial : SourceCurrentConjunctionRowsAllocation.Ready (physical before) :=
    ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩
  obtain ⟨output, after, saved, call, _⟩ :=
    SourceCurrentAllocatedMergePhysical.call_complete clear input (physical before) memo initial stored available
  obtain ⟨final, receipt⟩ := verified formulas solver inventory clear clearTrue (.done call)
    ready admitted stored covered available memos valid
  exact ⟨output, advancePhysical before after, saved, final, receipt⟩

/-- The literal source clear predicate needs no supplied semantic callback law. -/
theorem source_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (input : Value Symbol Guard) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (available : Available before.native.machine.heap input) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ output after saved final, Receipt formulas solver inventory literalClear input before memo output after saved memos final :=
  finite formulas solver inventory literalClear (literalClear_true formulas solver) input before memo ready admitted
    stored covered available memos valid

end MicroCFTA.SourceCurrentAllocatedMerge
