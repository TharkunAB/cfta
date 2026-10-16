import MicroCFTA.SourceCurrentAllocatedNativeInventoryState
import MicroCFTA.SourceCurrentAllocatedSeededOperandLanguage

/-!
# Common subtree preservation through the actual checked seeded fold

Each projection retains the same native tables. Each native request extends
the concrete inventory at its actual entry heap and derives final admission.
The induction follows head projection, tail fold, then the native request.
Only selected paths need closed support. Other original siblings can be open.
Reached word ranges and the initial warm invariants remain explicit.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded FoldRanges SeededRanges)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

/-- Every common selected subtree remains in the result's physical language. -/
def Includes (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (result : Value Symbol Guard) : Prop :=
  ∀ ambient symbol terms part,
    All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
    (∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) →
    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part

/-- Actual final physical state and the concrete inventory used by its warm cells. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Checked width) (result : Value Symbol Guard) (after : Checked width) : Prop where
  good : Good after
  effects : Effects (physical before) (physical after)
  extension : Extension before.native.machine after.native.machine
  scopes : Scoped after.native
  idle : Idle after.native
  available : Available after.native.machine.heap result
  closed : result.free = []
  admitted : At formulas solver inventory after

/-- The whole source fold constructs its own next inventory and common subtree law. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : FoldRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ paths, path ≠ []) :
    ∃ result after next, Fold values paths before result after ∧
      Receipt formulas solver next before result after ∧ Includes formulas solver values paths result := by
  induction paths generalizing before inventory with
  | nil => cases ranges
  | cons path paths ih =>
      cases paths with
      | nil =>
          obtain ⟨result, after, actual, afterGood, effects, extension, afterScopes, afterIdle, resident, closed⟩ :=
            SourceCurrentAllocatedSeededQuery.operand_complete unconstrained anchor anchorSemantic anchorReady
              path values before good ready scopes idle available growth (supported path (by simp))
          have afterAdmission : At formulas solver inventory after := by
            cases actual with
            | force heap projection => exact admitted.advance ⟨heap, before.operations⟩ extension
          refine ⟨result, after, inventory, .one actual,
            ⟨afterGood, effects, extension, afterScopes, afterIdle, resident, closed, afterAdmission⟩, ?_⟩
          intro ambient symbol terms part accepted selected
          exact SourceCurrentAllocatedSeededOperandLanguage.Operand.included
            unconstrained anchor anchorSemantic anchorReady actual ready available growth
            (supported path (by simp)) (nonroot path (by simp))
            (SourceEqualityPCSGuard.holds formulas solver) ambient symbol terms part accepted (selected path (by simp))
      | cons next paths =>
          cases ranges with
          | cons rest native =>
              obtain ⟨value, middle, first, middleGood, firstEffects, firstExtension, middleScopes,
                middleIdle, valueAvailable, valueClosed⟩ := SourceCurrentAllocatedSeededQuery.operand_complete
                  unconstrained anchor anchorSemantic anchorReady path values before good ready scopes idle
                  available growth (supported path (by simp))
              have middleAdmission : At formulas solver inventory middle := by
                cases first with
                | force heap projection => exact admitted.advance ⟨heap, before.operations⟩ firstExtension
              obtain ⟨tail, later, tailInventory, remaining, tailReceipt, tailIncluded⟩ :=
                ih inventory middle (rest value middle first) middleGood firstEffects.ready middleScopes middleIdle
                  middleAdmission (fun value member => firstEffects.keeps.available value (available value member))
                  (grows_trans growth firstEffects.keeps.growth)
                  (fun path member => supported path (List.mem_cons_of_mem _ member))
                  (fun path member => nonroot path (List.mem_cons_of_mem _ member))
              have valueLater := tailReceipt.effects.keeps.available value valueAvailable
              obtain ⟨finalInventory, fuel, result, after, sourceEq, rootsEq, query, finalAdmission⟩ :=
                SourceCurrentAllocatedNativeInventoryState.query_complete tailInventory formulas solver later
                  tailReceipt.good tailReceipt.admitted tailReceipt.scopes tailReceipt.effects.ready.semantic
                  tailReceipt.idle value tail valueLater tailReceipt.available valueClosed tailReceipt.closed
                  (native value middle tail later first remaining)
              have checked := SourceCurrentAllocatedNativeTraceEffects.effects query.trace tailReceipt.good
                tailReceipt.effects.ready.semantic tailReceipt.effects.ready.costs (fun _ => trivial)
              refine ⟨result, after, finalInventory, .cons first remaining query.trace,
                ⟨checked.1, firstEffects.trans (tailReceipt.effects.trans checked.2.1),
                  firstExtension.trans (tailReceipt.extension.trans checked.2.2), query.scopedCache,
                  query.idle, query.result, query.closed, finalAdmission⟩, ?_⟩
              intro ambient symbol terms part accepted selected
              have own := SourceCurrentAllocatedSeededOperandLanguage.Operand.included
                unconstrained anchor anchorSemantic anchorReady first ready available growth
                (supported path (by simp)) (nonroot path (by simp))
                (SourceEqualityPCSGuard.holds formulas solver) ambient symbol terms part accepted (selected path (by simp))
              have tail := tailIncluded ambient symbol terms part accepted
                (fun path member => selected path (List.mem_cons_of_mem _ member))
              exact (query.meaning ambient part).mpr ⟨own, tail⟩

/-- The exact first-seed rotation retains admission and every nonempty common subtree. -/
theorem seeded_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ paths, path ≠ []) :
    ∃ result after next, Seeded values paths before result after ∧
      Receipt formulas solver next before result after ∧ (paths ≠ [] → Includes formulas solver values paths result) := by
  cases paths with
  | nil =>
      exact ⟨.empty, before, inventory, .nil before,
        ⟨good, .refl _ ready, .refl _, scopes, idle, empty_available _, rfl, admitted⟩,
        fun nonempty => False.elim (nonempty rfl)⟩
  | cons seed rest =>
      have rotated : ∀ path, path ∈ rest ++ [seed] → path ∈ seed :: rest := by
        intro path member
        simpa [List.mem_append, List.mem_cons, or_comm] using member
      obtain ⟨result, after, next, actual, receipt, included⟩ := fold_complete formulas solver inventory
        unconstrained anchor anchorSemantic anchorReady values (rest ++ [seed]) before ranges good ready scopes idle
        admitted available growth (fun path member => supported path (rotated path member))
        (fun path member => nonroot path (rotated path member))
      refine ⟨result, after, next, .nonempty actual, receipt, ?_⟩
      intro _ ambient symbol terms part accepted selected
      exact included ambient symbol terms part accepted (fun path member => selected path (rotated path member))

/-- An actual checked seeded result receives the same derived state and language receipt. -/
theorem Seeded.receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Seeded values paths before result after)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ paths, path ≠ []) :
    ∃ next, Receipt formulas solver next before result after ∧
      (paths ≠ [] → Includes formulas solver values paths result) := by
  obtain ⟨chosen, reached, next, completed, receipt, included⟩ := seeded_complete formulas solver inventory
    unconstrained anchor anchorSemantic anchorReady values paths before ranges good ready scopes idle
    admitted available growth supported nonroot
  obtain ⟨rfl, rfl⟩ := actual.unique completed
  exact ⟨next, receipt, included⟩

/-- A false secondary gate derives the complete query with its actual anchor and warm tables. -/
theorem false_class_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool)
    (paths : EqualityNormalize.Class) (values : List (Value Symbol Guard))
    {before : Checked width} {anchor : State Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (good : Good before) (ready : Ready (physical before)) (scopes : Scoped before.native) (idle : Idle before.native)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SeededRanges values (paths.map (List.map Int.ofNat))
      (advancePhysical before ⟨anchor, before.operations⟩)) :
    ∃ query after next, Seeded values (paths.map (List.map Int.ofNat))
        (advancePhysical before ⟨anchor, before.operations⟩) query after ∧
      Receipt formulas solver next before query after ∧
      (paths ≠ [] → Includes formulas solver values (paths.map (List.map Int.ofNat)) query) := by
  obtain ⟨anchorSemantic, anchorReady, _, anchorValues, supported⟩ :=
    SourceCurrentSecondaryProjectionScoped.class_support unconstrained gate ready.semantic
      (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
  have first := SourceCurrentAllocatedGateFields.secondary_class unconstrained gate ready available
  have anchorGood := SourceCurrentAllocatedConjunctionMemo.advance_good before _ good first.1
  have anchorScopes := SourceCurrentAllocatedConjunctionMemo.advance_scoped before ⟨anchor, before.operations⟩ scopes
  have anchorIdle := SourceCurrentAllocatedConjunctionMemo.advance_idle before ⟨anchor, before.operations⟩ idle
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before _ first.1
  have advanced : Effects (physical before)
      (physical (advancePhysical before ⟨anchor, before.operations⟩)) := first.1
  obtain ⟨query, after, next, actual, receipt, included⟩ := seeded_complete formulas solver inventory
    unconstrained anchor anchorSemantic anchorReady values (paths.map (List.map Int.ofNat))
    (advancePhysical before ⟨anchor, before.operations⟩) ranges anchorGood advanced.ready anchorScopes anchorIdle
    (admitted.advance ⟨anchor, before.operations⟩ extension) anchorValues (grows_refl anchor)
    (by
      intro path member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact supported original present)
    (by
      intro path member empty
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact proper original present (List.map_eq_nil_iff.mp empty))
  refine ⟨query, after, next, actual,
    ⟨receipt.good, advanced.trans receipt.effects, extension.trans receipt.extension,
      receipt.scopes, receipt.idle, receipt.available, receipt.closed, receipt.admitted⟩, ?_⟩
  intro nonempty
  exact included (fun empty => nonempty (List.map_eq_nil_iff.mp empty))

/-- The actual false-class query receives the constructed state and language law by uniqueness. -/
theorem false_class_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool)
    (paths : EqualityNormalize.Class) (values : List (Value Symbol Guard))
    {before after : Checked width} {anchor : State Symbol Guard} {query : Value Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (actual : Seeded values (paths.map (List.map Int.ofNat))
      (advancePhysical before ⟨anchor, before.operations⟩) query after)
    (good : Good before) (ready : Ready (physical before)) (scopes : Scoped before.native) (idle : Idle before.native)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SeededRanges values (paths.map (List.map Int.ofNat))
      (advancePhysical before ⟨anchor, before.operations⟩)) :
    ∃ next, Receipt formulas solver next before query after ∧
      (paths ≠ [] → Includes formulas solver values (paths.map (List.map Int.ofNat)) query) := by
  obtain ⟨chosen, reached, next, completed, receipt, included⟩ := false_class_complete formulas solver inventory
    unconstrained paths values gate good ready scopes idle admitted available proper ranges
  obtain ⟨rfl, rfl⟩ := actual.unique completed
  exact ⟨next, receipt, included⟩

end MicroCFTA.SourceCurrentAllocatedSeededLanguage
