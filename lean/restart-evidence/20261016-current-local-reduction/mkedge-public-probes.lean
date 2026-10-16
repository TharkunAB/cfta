import MicroCFTA.SourceCurrentAllocatedMkEdge

namespace MicroCFTA.MkEdgePublicProbe
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedMkEdge
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

#print axioms build
#print axioms reject
#print axioms finite
#print axioms build_contradictory
#print axioms reject_correct
#print axioms RejectReceipt.empty
#print axioms Receipt.language
#check @finite
#check @build_contradictory
#check @reject_correct
#check @Receipt.language

-- Raw contradiction returns the sentinel without any available-child premise.
example (symbol : Symbol) (children : List (Value Symbol Guard)) (before : Checked width) :
    build symbol (⟨.contradiction, .top⟩ : Allocated) children before =
      (.ok (reject symbol before).1, (reject symbol before).2) :=
  build_contradictory symbol _ children before rfl

-- Bottom also skips the accessor for an arbitrary stored physical value.
example (symbol : Symbol) (stored : SourceEqualityConstraintAllocation.Value)
    (children : List (Value Symbol Guard)) (before : Checked width) :
    build symbol (⟨stored, .bottom⟩ : Allocated) children before =
      (.ok (reject symbol before).1, (reject symbol before).2) := by
  apply build_contradictory
  simp [SourceEqualityConjoinAllocation.readback, SourceEqualityAccessorAllocation.constraint,
    SourceEqualityMkEdgeAllocation.contradictory]

-- Sentinel construction allocates Top even when the initial operation cache is cold.
example : (SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty).constraints.next = 1 := by
  rfl

-- The sentinel's Top field is derived from that allocation, not supplied initially.
example : SourceCurrentConjunctionEquality.FieldAvailable
    (SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty) top :=
  (SourceCurrentConjunctionFieldAllocation.empty_field _ SourceEqualityConstraintMemoAllocation.empty_valid).2.2

-- A valid checked rejection keeps every native table and the same admitted inventory.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (before : Checked width) (ready : Ready before)
    (admitted : At formulas solver inventory before) :
    At formulas solver inventory (reject symbol before).2 ∧
      (reject symbol before).2.native.nodes = before.native.nodes ∧
      (reject symbol before).2.native.edges = before.native.edges ∧
      (reject symbol before).2.native.machine.domains = before.native.machine.domains := by
  have receipt := reject_correct formulas solver inventory symbol before ready admitted
  exact ⟨receipt.admitted, receipt.nodes, receipt.edges, receipt.domains⟩

-- Every sentinel receipt excludes all edge terms, independently of guard semantics.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (before : Checked width) (ready : Ready before)
    (admitted : At formulas solver inventory before)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    ¬ InternedGuardedLanguage.edgeMeaning holds ambient (reject symbol before).1 term :=
  (reject_correct formulas solver inventory symbol before ready admitted).empty holds ambient term

-- Even a live field rejected by the arity test returns the literal sentinel children.
example {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {symbol : Symbol} {constraint : Allocated} {children : List (Value Symbol Guard)}
    {before after : Checked width} {result : EdgeValue Symbol Guard}
    (receipt : Receipt formulas solver inventory symbol constraint children before result after)
    (rejected : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback constraint)
      children.length = false) : result.children = [.empty] := by
  simpa only [rejected, Bool.false_eq_true, ↓reduceIte] using receipt.children

-- The total language law uses the raw stored field, not the full equality accessor as a replacement guard.
example {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {symbol : Symbol} {constraint : Allocated} {children : List (Value Symbol Guard)}
    {before after : Checked width} {result : EdgeValue Symbol Guard}
    (receipt : Receipt formulas solver inventory symbol constraint children before result after)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints constraint.stored)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
      ∃ terms, term = .node symbol terms ∧
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) children terms ∧
        SourceEqualityPCSGuard.holds formulas solver (SourceEqualityConjoinAllocation.readback constraint) term = true :=
  receipt.language storedReady ambient term

end MicroCFTA.MkEdgePublicProbe
