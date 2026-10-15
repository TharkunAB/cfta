import MicroCFTA.EndpointMemoGateClasses
import MicroCFTA.SourceSecondaryGateRefusedClassQuery

/-!
# Reached original classes in the current lazy refused-class scan

The primary gate uses the enabled endpoint policy. A clear primary class
is selected. A blocked primary class runs the secondary gate. A clear
secondary class runs the actual seeded query and decision. A true decision
stops without any receipt for the remaining original classes. Exhaustion
retains selected original records for the separate fallback.

The graph records constructor and scoped native states. Global gate memo
receipts, GHC demand, and the fallback require separate source composition.
-/
namespace MicroCFTA.SourceEqualityLazyClassPrefix
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open SourceEqualityNativeScoped SourceEmptinessClassFold
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Only reached original classes have actual gate and query receipts. -/
inductive Scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard)) :
    Constraints → Native width Symbol Guard → Option Class → Constraints → Native width Symbol Guard → Prop where
  | nil : Scan unconstrained reaches values [] state none [] state
  | selected
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap false heap)
      (rest : Scan unconstrained reaches values classes (advanceHeap before heap) outcome selected after) :
      Scan unconstrained reaches values (paths :: classes) before outcome (paths :: selected) after
  | skipped
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap)
      (secondary : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths heap true anchor)
      (rest : Scan unconstrained reaches values classes (advanceHeap (advanceHeap before heap) anchor) outcome selected after) :
      Scan unconstrained reaches values (paths :: classes) before outcome selected after
  | continued
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap)
      (secondary : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths heap false anchor)
      (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle)
      (decision : SourceEmptinessDecision.Decision query middle false later)
      (rest : Scan unconstrained reaches values classes later outcome selected after) :
      Scan unconstrained reaches values (paths :: classes) before outcome selected after
  | stopped
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap)
      (secondary : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths heap false anchor)
      (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle)
      (decision : SourceEmptinessDecision.Decision query middle true after) :
      Scan unconstrained reaches values (paths :: classes) before (some paths) [] after

/-- A stopped query belongs to the original class list, including its original paths. -/
theorem stopped_member [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {paths : Class} {before after : Native width Symbol Guard}
    (trace : Scan unconstrained reaches values classes before (some paths) selected after) : paths ∈ classes := by
  generalize result : some paths = outcome at trace
  induction trace with
  | nil => cases result
  | selected primary rest ih => exact List.mem_cons_of_mem _ (ih result)
  | skipped primary secondary rest ih => exact List.mem_cons_of_mem _ (ih result)
  | continued primary secondary seeded decision rest ih => exact List.mem_cons_of_mem _ (ih result)
  | stopped primary secondary seeded decision =>
      have same := Option.some.inj result
      subst paths
      exact List.mem_cons_self

/-- Selected records keep their original order and multiplicity in the reached class prefix. -/
theorem selected_sublist [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Native width Symbol Guard}
    (trace : Scan unconstrained reaches values classes before outcome selected after) : selected.Sublist classes := by
  induction trace with
  | nil => exact .refl _
  | selected primary rest ih => exact .cons_cons _ ih
  | skipped primary secondary rest ih => exact .cons _ ih
  | continued primary secondary seeded decision rest ih => exact .cons _ ih
  | stopped => exact List.nil_sublist _

end MicroCFTA.SourceEqualityLazyClassPrefix
