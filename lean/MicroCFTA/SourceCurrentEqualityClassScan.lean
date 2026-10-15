import MicroCFTA.EndpointMemoGateClasses
import MicroCFTA.SourceCurrentSecondaryTrace
import MicroCFTA.SourceCurrentEmptinessMemo

/-!
# Current lazy class scans with completed emptiness memo calls

The primary gate selects an original class or runs the current secondary
gate. A clear secondary class runs the actual seeded query and the separate
completed emptiness memo. A true answer stops before the remaining classes.
Other branches retain the exact returned memo for the next original class.
The graph does not compose the three global gate memo tables or the fallback.
-/
namespace MicroCFTA.SourceCurrentEqualityClassScan
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open SourceEqualityNativeScoped SourceEmptinessClassFold
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Only reached original classes carry actual gate, seeded-query, and fourth-memo receipts. -/
inductive Scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard)) :
    Constraints → Native width Symbol Guard → Memo → Option Class → Constraints →
      Native width Symbol Guard → Memo → Prop where
  | nil : Scan unconstrained reaches values [] state memo none [] state memo
  | selected
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap false heap)
      (rest : Scan unconstrained reaches values classes (advanceHeap before heap) memo outcome selected after saved) :
      Scan unconstrained reaches values (paths :: classes) before memo outcome (paths :: selected) after saved
  | skipped
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap)
      (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap true anchor)
      (rest : Scan unconstrained reaches values classes (advanceHeap (advanceHeap before heap) anchor)
        memo outcome selected after saved) :
      Scan unconstrained reaches values (paths :: classes) before memo outcome selected after saved
  | continued
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap)
      (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor)
      (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle)
      (decision : SourceCurrentEmptinessMemo.Call memo query middle false later savedMemo)
      (rest : Scan unconstrained reaches values classes later savedMemo outcome selected after saved) :
      Scan unconstrained reaches values (paths :: classes) before memo outcome selected after saved
  | stopped
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap true heap)
      (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor)
      (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle)
      (decision : SourceCurrentEmptinessMemo.Call memo query middle true after saved) :
      Scan unconstrained reaches values (paths :: classes) before memo (some paths) [] after saved

/-- Every stopped query retains its exact original class occurrence. -/
theorem stopped_member [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {paths : Class} {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan unconstrained reaches values classes before memo (some paths) selected after saved) : paths ∈ classes := by
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

/-- Selected records retain their original order and multiplicity in the reached prefix. -/
theorem selected_sublist [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan unconstrained reaches values classes before memo outcome selected after saved) : selected.Sublist classes := by
  induction trace with
  | nil => exact .refl _
  | selected primary rest ih => exact .cons_cons _ ih
  | skipped primary secondary rest ih => exact .cons _ ih
  | continued primary secondary seeded decision rest ih => exact .cons _ ih
  | stopped => exact List.nil_sublist _

end MicroCFTA.SourceCurrentEqualityClassScan
