import MicroCFTA.SourceSecondaryGateQueryCosts
import MicroCFTA.SourceSecondaryGateRefusedClassQuery
import MicroCFTA.SourceSecondaryGateHeap

/-!
# Ready actual queries after false secondary class gates

The false gate returns one exact constructor anchor. The seeded query starts
in the original native state advanced to that anchor. Class satisfaction
supplies proper paths. Actual query operations then derive final readiness,
costs, fields, and original input retention. A true decision refutes the
original class without a supplied final invariant.

The graphs retain their actual scoped native and completed exploration
receipts. This module makes no global memo or GHC demand claim.
-/
namespace MicroCFTA.SourceSecondaryGateQueryReady
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEmptinessClassFold
open SourceSecondaryGateScopedProjection
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- A satisfied active class derives every final query invariant from its exact false gate anchor. -/
theorem queried_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (paths : Class) (active : Nontrivial paths)
    (values : List (Value Symbol Guard))
    {beforeNative middle after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {anchor : State Symbol Guard} {query : Value Symbol Guard} {answer : Bool}
    (gate : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths
      beforeNative.machine.heap false anchor)
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat))
      (advanceHeap beforeNative anchor) query middle)
    (decision : SourceEmptinessDecision.Decision query middle answer after)
    (ready : IdleReady top conjoin beforeNative) (available : Values beforeNative.machine.heap values)
    (costs : CostHeap beforeNative.machine.heap) (fields : FieldHeap beforeNative.machine.heap)
    (symbol : Symbol) (terms : List (Term Symbol)) (satisfied : ClassSat (.node symbol terms) paths) :
    IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps beforeNative.machine.heap after.machine.heap ∧ Values after.machine.heap values := by
  have nonroot := EqualityReduction.class_nonroot paths active (.node symbol terms) satisfied
  obtain ⟨anchorSemantic, anchorReady, kept, anchorAvailable, _, certificates⟩ :=
    SourceSecondaryGateProjectionAnchor.class_anchor unconstrained gate ready.semantic
      (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available
  have supported : ∀ path ∈ paths.map (List.map Int.ofNat), PathSupport unconstrained anchor path values := by
    intro path member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact path_support_of_false (certificates original present) (nonroot original present) anchorAvailable
  have anchorFields : FieldHeap anchor :=
    SourceSecondaryGateHeap.class_heap (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
      unconstrained gate ready.semantic available fields
  have queried := SourceSecondaryGateQueryCosts.seeded_decision_ready unconstrained anchor anchorSemantic anchorReady
    seeded decision (ready.advance anchor kept anchorSemantic) anchorAvailable (grows_refl anchor) supported
    anchorReady.2.2.2 anchorFields
  have retained : Keeps beforeNative.machine.heap after.machine.heap := kept.trans queried.2.2.2.1
  exact ⟨queried.1, queried.2.1, queried.2.2.2.2, retained,
    fun value member => retained.available value (available value member)⟩

/-- The exact advanced native query state supplies every premise of actual true-decision refutation. -/
theorem refutes_decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (paths : Class) (active : Nontrivial paths)
    (values : List (Value Symbol Guard))
    {beforeNative middle after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {anchor : State Symbol Guard} {query : Value Symbol Guard}
    (gate : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths
      beforeNative.machine.heap false anchor)
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat))
      (advanceHeap beforeNative anchor) query middle)
    (decision : SourceEmptinessDecision.Decision query middle true after)
    (ready : IdleReady top conjoin beforeNative) (available : Values beforeNative.machine.heap values)
    (costs : CostHeap beforeNative.machine.heap) (fields : FieldHeap beforeNative.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬ClassSat (.node symbol terms) paths := by
  have anchored := SourceSecondaryGateProjectionAnchor.class_anchor unconstrained gate ready.semantic
    (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available
  have anchorFields : FieldHeap anchor :=
    SourceSecondaryGateHeap.class_heap (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
      unconstrained gate ready.semantic available fields
  exact SourceSecondaryGateRefusedClassQuery.refutes_decision unconstrained paths active values gate ready.semantic
    (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available seeded
    (ready.advance anchor anchored.2.2.1 anchored.1) anchored.2.2.2.1 (grows_refl anchor) anchorFields
    decision formulas solver ambient symbol terms accepted

end MicroCFTA.SourceSecondaryGateQueryReady
