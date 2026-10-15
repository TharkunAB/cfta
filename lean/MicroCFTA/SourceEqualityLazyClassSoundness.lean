import MicroCFTA.SourceEqualityLazyClassPrefix
import MicroCFTA.SourcePrimaryGateEffects
import MicroCFTA.SourceSecondaryGateQueryReady

/-!
# Sound early rejection in the current lazy class scan

Actual primary and secondary gates retain native readiness through their
returned constructor heaps. A satisfied queried class derives support at
its actual secondary anchor. A false decision then retains readiness for
the next class. A true decision refutes that original class.

An independently accepted forest that satisfies all active original classes
cannot reach a true decision. This proof derives intermediate readiness.
It does not assume a semantic emptiness oracle or a completed fallback.
Global memo composition, exact GHC demand, and completion remain separate.
-/
namespace MicroCFTA.SourceEqualityLazyClassSoundness
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityLazyClassPrefix
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- An enabled primary class advances the same native state and derives every next-call invariant. -/
theorem primary_advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before : Native width Symbol Guard}
    {answer : Bool} {heap : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap answer heap)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) :
    IdleReady top conjoin (advanceHeap before heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
      Keeps before.machine.heap heap ∧ Values heap values := by
  have checked := SourcePrimaryGateEffects.class_effects
    (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    unconstrained reaches trace ready.semantic costs available fields
  exact ⟨ready.advance heap checked.2.1 checked.1, checked.2.2.1, checked.2.2.2, checked.2.1,
    fun value member => checked.2.1.available value (available value member)⟩

/-- A secondary class advances the same native state for either actual gate answer. -/
theorem secondary_advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before : Native width Symbol Guard}
    {answer : Bool} {heap : State Symbol Guard}
    (trace : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths before.machine.heap answer heap)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) :
    IdleReady top conjoin (advanceHeap before heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
      Keeps before.machine.heap heap ∧ Values heap values := by
  have semantic := SourceSecondaryGateReplay.class_replay unconstrained values paths before.machine.heap answer heap
    trace ready.semantic available
  have weighted := InternedSourceGateReplay.class_replay unconstrained values paths before.machine.heap answer heap
    trace (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available
  have retainedFields := SourceSecondaryGateHeap.class_heap
    (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    unconstrained trace ready.semantic available fields
  exact ⟨ready.advance heap semantic.2.1 semantic.1, weighted.1.2.2.2, retainedFields, semantic.2.1,
    fun value member => semantic.2.1.available value (available value member)⟩

/-- A satisfied accepted candidate excludes early rejection and derives all reached scan invariants. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Native width Symbol Guard}
    (trace : Scan unconstrained reaches values classes before outcome selected after)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) (active : Active classes)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)
    (satisfied : Satisfies (.node symbol terms) classes) :
    outcome = none ∧ IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap values := by
  revert satisfied active fields costs available ready
  induction trace with
  | nil =>
      intro ready available costs fields _ _
      exact ⟨rfl, ready, costs, fields, pure_keeps _ ready.semantic.ready, available⟩
  | selected primary rest ih =>
      intro ready available costs fields active satisfied
      obtain ⟨nextReady, nextCosts, nextFields, first, nextValues⟩ :=
        primary_advance unconstrained reaches primary ready available costs fields
      obtain ⟨none, finalReady, finalCosts, finalFields, later, finalValues⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => active paths (List.mem_cons_of_mem _ member))
          (fun paths member => satisfied paths (List.mem_cons_of_mem _ member))
      exact ⟨none, finalReady, finalCosts, finalFields, first.trans later, finalValues⟩
  | skipped primary secondary rest ih =>
      intro ready available costs fields active satisfied
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        primary_advance unconstrained reaches primary ready available costs fields
      obtain ⟨nextReady, nextCosts, nextFields, second, nextValues⟩ :=
        secondary_advance unconstrained secondary primaryReady primaryValues primaryCosts primaryFields
      obtain ⟨none, finalReady, finalCosts, finalFields, later, finalValues⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => active paths (List.mem_cons_of_mem _ member))
          (fun paths member => satisfied paths (List.mem_cons_of_mem _ member))
      exact ⟨none, finalReady, finalCosts, finalFields, first.trans (second.trans later), finalValues⟩
  | continued primary secondary seeded decision rest ih =>
      intro ready available costs fields active satisfied
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        primary_advance unconstrained reaches primary ready available costs fields
      obtain ⟨nextReady, nextCosts, nextFields, second, nextValues⟩ :=
        SourceSecondaryGateQueryReady.queried_effects unconstrained _ (active _ List.mem_cons_self) values
          secondary seeded decision primaryReady primaryValues primaryCosts primaryFields symbol terms
          (satisfied _ List.mem_cons_self)
      obtain ⟨none, finalReady, finalCosts, finalFields, later, finalValues⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => active paths (List.mem_cons_of_mem _ member))
          (fun paths member => satisfied paths (List.mem_cons_of_mem _ member))
      exact ⟨none, finalReady, finalCosts, finalFields, first.trans (second.trans later), finalValues⟩
  | stopped primary secondary seeded decision =>
      intro ready available costs fields active satisfied
      obtain ⟨primaryReady, primaryCosts, primaryFields, _, primaryValues⟩ :=
        primary_advance unconstrained reaches primary ready available costs fields
      exact False.elim ((SourceSecondaryGateQueryReady.refutes_decision unconstrained _ (active _ List.mem_cons_self)
        values secondary seeded decision primaryReady primaryValues primaryCosts primaryFields
        formulas solver ambient symbol terms accepted) (satisfied _ List.mem_cons_self))

/-- An actual stopped prefix excludes every independently accepted forest satisfying all original classes. -/
theorem stopped_refutes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {paths : Class} {before after : Native width Symbol Guard}
    (trace : Scan unconstrained reaches values classes before (some paths) selected after)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) (active : Active classes)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬Satisfies (.node symbol terms) classes := by
  intro satisfied
  have impossible := (verified trace ready available costs fields active formulas solver ambient symbol terms accepted satisfied).1
  cases impossible

end MicroCFTA.SourceEqualityLazyClassSoundness
