import MicroCFTA.SourceCurrentAllocatedParentEdge

namespace MicroCFTA.ParentEdgePublicProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning edgeMeaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedParentEdge
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

#print axioms rejected
#print axioms finite
#print axioms RawMeaning
#check @rejected
#check @finite
#check @Receipt.language
#check @Receipt.construction

-- The actual raw-reject graph has no local completion, range, or child-availability premise.
example (budget : Nat) (symbol : Symbol) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Edge budget symbol (⟨none, .top⟩ : Guard) loaded inherited values before fourth memo
      (SourceCurrentAllocatedMkEdge.reject symbol before).1
      (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo :=
  .rejected rfl

-- Empty child forests have their ordinary raw edge language. Empty erasure is not a rejection test.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (symbol : Symbol)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol
      SourceEqualityConstraintConstructors.top [] (.node symbol []) :=
  ⟨[], rfl, .nil, SourceCurrentAllocatedMerge.top_true formulas solver (.node symbol [])⟩

-- Rejection supplies an actual memo read receipt and preserves all warm memo entries.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (test : SourceEqualityMkEdgeAllocation.contradictory original = true)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ actual : Edge budget symbol original loaded inherited values before fourth memo
        (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo,
      Reads formulas solver actual memos memos ∧
        At formulas solver inventory (SourceCurrentAllocatedMkEdge.reject symbol before).2 ∧
        SourceCurrentEmptinessMemo.Correct formulas solver
          (SourceCurrentAllocatedMkEdge.reject symbol before).2.native.machine.heap fourth := by
  obtain ⟨actual, reads, receipt⟩ := rejected formulas solver inventory budget symbol original loaded inherited values
    before fourth memo ready admitted test correct stored covered memos valid
  exact ⟨actual, reads, receipt.admitted, receipt.correct⟩

-- A live constructor retains the actual local child arity, with a separate sentinel alternative.
example {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {final : Memos}
    (receipt : Receipt formulas solver inventory symbol original loaded inherited values before result after
      fourth savedFourth memo saved final) :
    result.children = [.empty] ∨ ∃ children, children.length = values.length ∧ result.children = children := by
  rcases receipt.construction with reject | ⟨children, middle, arity, built⟩
  · exact Or.inl reject.children
  · cases kept : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
    | false => exact Or.inl (by simpa only [kept, Bool.false_eq_true, ↓reduceIte] using built.children)
    | true => exact Or.inr ⟨children, arity, by simpa only [kept, ↓reduceIte] using built.children⟩

-- The parent result narrows the original raw edge language without an inherited-satisfaction premise.
example {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {final : Memos}
    (receipt : Receipt formulas solver inventory symbol original loaded inherited values before result after
      fourth savedFourth memo saved final) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term) :
    RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term :=
  (receipt.language ambient term).1 accepted

-- Exact original edge membership is conditional on the actual inherited payload.
example {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {final : Memos}
    (receipt : Receipt formulas solver inventory symbol original loaded inherited values before result after
      fourth savedFourth memo saved final) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (sat : SourceEqualityPrecheck.Sat term inherited.payload) :
    edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
      RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term :=
  (receipt.language ambient term).2 sat

-- Rejected construction retains the native tables while its equality cache can grow.
example (symbol : Symbol) (before : Checked width) :
    (SourceCurrentAllocatedMkEdge.reject symbol before).2.native.nodes = before.native.nodes ∧
      (SourceCurrentAllocatedMkEdge.reject symbol before).2.native.edges = before.native.edges ∧
      (SourceCurrentAllocatedMkEdge.reject symbol before).2.native.machine.domains = before.native.machine.domains ∧
      (SourceCurrentAllocatedMkEdge.reject symbol before).2.operations = SourceEqualityMkEdgeAllocation.emptyField before.operations :=
  ⟨rfl, rfl, rfl, rfl⟩

end MicroCFTA.ParentEdgePublicProbe
