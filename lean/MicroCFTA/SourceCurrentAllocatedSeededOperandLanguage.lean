import MicroCFTA.SourceCurrentAllocatedSeededQuery

/-!
# Physical effects and language of checked seeded operands

Each actual operand retains its literal returned checked state. Anchored
path support derives its physical effects and closed result. A proper
path retains each selected subtree of an accepted original child forest.
Unrelated original children can remain open. These results concern the
completed projection graph. They do not establish GHC demand order.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededOperandLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedSeededQuery
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
variable {width : Nat}

/-- Anchored support derives physical effects at the actual operand's exact returned state. -/
theorem Operand.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : SourceCurrentAllocatedSeededQuery.Operand path values before result after)
    (good : Good before) (ready : Ready (physical before)) (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : PathSupport unconstrained anchor path values) :
    Good after ∧ Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨chosen, reached, completed, effects⟩ := operand_complete unconstrained anchor anchorSemantic anchorReady
    path values before good ready scopes idle available growth supported
  obtain ⟨rfl, rfl⟩ := actual.unique completed
  exact effects

/-- The actual proper operand contains each selected subtree of an accepted original forest. -/
theorem Operand.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : SourceCurrentAllocatedSeededQuery.Operand path values before result after)
    (ready : Ready (physical before))
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : PathSupport unconstrained anchor path values) (nonroot : path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    meaning holds ambient result part := by
  rcases supported with ⟨natural, rfl, supported⟩
  cases natural with
  | nil => exact False.elim (nonroot rfl)
  | cons index path =>
      cases actual with
      | force heap projected =>
          exact SourceCurrentSecondaryProjectionLanguage.forest_included unconstrained anchor anchorSemantic anchorReady
            projected ready.semantic available growth supported holds ambient symbol terms part accepted selected

end MicroCFTA.SourceCurrentAllocatedSeededOperandLanguage
