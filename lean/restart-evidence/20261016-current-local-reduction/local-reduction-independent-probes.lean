import MicroCFTA.SourceCurrentAllocatedLocalReduction

#print axioms MicroCFTA.SourceCurrentAllocatedLocalReduction.finite
#check @MicroCFTA.SourceCurrentAllocatedLocalReduction.Reduction
#check @MicroCFTA.SourceCurrentAllocatedLocalReduction.Reads
#check @MicroCFTA.SourceCurrentAllocatedLocalReduction.Ranges
#check @MicroCFTA.SourceCurrentAllocatedLocalReduction.Receipt
#check @MicroCFTA.SourceCurrentAllocatedLocalReduction.finite

namespace MicroCFTA.SourceCurrentAllocatedLocalReductionProbes
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction
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
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- The unchanged branch retains the entire native state and the literal returned operation state.
theorem unchanged_state
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (loaded : Allocated) (inherited : EqValue) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) (memos : Memos)
    (checked : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged) :
    ∃ actual : Reduction budget loaded inherited values before fourth memo values (prefixState before loaded inherited) fourth memo,
      Reads formulas solver actual memos memos ∧
      (prefixState before loaded inherited).native = before.native ∧
      (prefixState before loaded inherited).operations = (runPrefix loaded.stored loaded.guard inherited before.operations).2 :=
  ⟨.unchanged checked, .unchanged (actual := checked), rfl, rfl⟩

-- Erasing zero child slots retains the empty forest's accepted empty term list.
theorem zero_child_erasure
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (loaded : Allocated) (inherited : EqValue) (before : Checked width)
    (fourth : Fourth) (memo : Memo) (memos : Memos)
    (checked : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .emptyChildren)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ actual : Reduction budget loaded inherited [] before fourth memo [] (prefixState before loaded inherited) fourth memo,
      Reads formulas solver actual memos memos ∧ All₂ (meaning holds ambient) ([] : List (Value Symbol Guard)) [] :=
  ⟨.emptyChildren checked, .emptyChildren (actual := checked), .nil⟩

-- A resident physical edge derives the same-cache load and all child availability itself.
theorem resident_local
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (edge : EdgeValue Symbol Guard) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap edge)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : ∀ loaded, SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.operations.constraints = .ok (some loaded) →
      Ranges budget loaded inherited edge.children before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ loaded results after savedFourth saved next final,
      ∃ actual : Reduction budget loaded inherited edge.children before fourth memo results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next edge.entry.key.constraint loaded inherited edge.children results before after fourth savedFourth memo saved final ∧
        ∀ ambient symbol terms,
          SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint (.node symbol terms) = true →
          SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload →
          (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
            All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) edge.children terms) := by
  obtain ⟨cached, loaded, found⟩ := ready.good.fields edge.entry.key edge resident
  have available : Values before.native.machine.heap edge.children :=
    ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  obtain ⟨results, after, savedFourth, saved, next, final, actual, reads, receipt⟩ := finite
    formulas solver inventory budget edge.entry.key.constraint loaded inherited edge.children before fourth memo ready admitted
    cached found inheritedReady available correct stored covered (ranges loaded found) memos valid
  exact ⟨loaded, results, after, savedFourth, saved, next, final, actual, reads, receipt,
    fun ambient symbol terms => (receipt.language ambient symbol terms).2⟩

end MicroCFTA.SourceCurrentAllocatedLocalReductionProbes

#print axioms MicroCFTA.SourceCurrentAllocatedLocalReductionProbes.unchanged_state
#print axioms MicroCFTA.SourceCurrentAllocatedLocalReductionProbes.zero_child_erasure
#print axioms MicroCFTA.SourceCurrentAllocatedLocalReductionProbes.resident_local
#check @MicroCFTA.SourceCurrentAllocatedLocalReductionProbes.unchanged_state
#check @MicroCFTA.SourceCurrentAllocatedLocalReductionProbes.zero_child_erasure
#check @MicroCFTA.SourceCurrentAllocatedLocalReductionProbes.resident_local
