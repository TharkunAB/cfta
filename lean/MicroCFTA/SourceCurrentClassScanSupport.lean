import MicroCFTA.SourceCurrentPrimaryReplay
import MicroCFTA.SourceCurrentClassScanGlobalMemos
import MicroCFTA.SourceCurrentSelectedClassRecords
import MicroCFTA.SourceCurrentRequiredSupport
import MicroCFTA.SourceEqualitySelectedRequired

/-!
# Selected required-path support at the actual scan final heap

Each selected class retains its original primary gate occurrence. Reached
queries derive the intervening heap effects and memo invariants. Every
retained gate then has an exact false certificate at the scan final heap.
The canonical union supplies the required trie domain on the original
children. These certificates add no source gate or memo execution.

This module does not assert support for reconstructed children after the
required-path worker or the later equality edits.
-/
namespace MicroCFTA.SourceCurrentClassScanSupport
open Cache EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceCurrentEqualityClassScan SourceCurrentEqualityClassScanSoundness
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- A selected class keeps the actual earlier gate and its derived input domain. -/
def Origin [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (paths : Class) (final : State Symbol Guard) : Prop :=
  ∃ before middle, EndpointStatefulGateTrace.ClassTrace source reaches values paths before false middle ∧
    SemanticReady before ∧ Values before values ∧ Grows middle final

/-- Retained original gates have effect-free primary certificates at the exact final heap. -/
theorem Origin.replay [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : Class} {final : State Symbol Guard}
    (origin : Origin values paths final) :
    EndpointStatefulGateTrace.ClassTrace source reaches values paths final false final := by
  obtain ⟨before, middle, actual, semantic, available, growth⟩ := origin
  exact (SourceCurrentPrimaryReplay.class_replay source reaches values paths before false middle
    actual semantic available).2.2 final growth

/-- Actual reached scan branches derive each selected gate's original input invariants. -/
theorem selected_origins [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values classes before memo outcome selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∀ paths ∈ selected, Origin values paths after.machine.heap := by
  induction trace generalizing memos with
  | nil => simp
  | selected primary rest ih =>
      obtain ⟨nextReady, nextCosts, nextFields, first, nextValues⟩ :=
        primary_advance source reaches primary ready available costs fields
      obtain ⟨nextMemos, _, firstKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available memos valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver first _ correct
      have tailProper := fun paths member => proper paths (List.mem_cons_of_mem _ member)
      have origins := ih nextReady nextValues nextCosts nextFields tailProper nextCorrect nextMemos firstKept.valid
      obtain ⟨_, _, _, _, _, _, later, _, _, _⟩ := SourceCurrentClassScanGlobalMemos.scan_memos rest
        nextReady nextValues nextCosts nextFields tailProper formulas solver nextCorrect nextMemos firstKept.valid
      intro paths member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, primary, ready.semantic, available, later.growth⟩
      · exact origins paths member
  | skipped primary secondary rest ih =>
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        primary_advance source reaches primary ready available costs fields
      obtain ⟨primaryMemos, _, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available memos valid
      obtain ⟨nextReady, nextCosts, nextFields, second, nextValues⟩ :=
        secondary_advance source secondary primaryReady primaryValues primaryCosts primaryFields
      obtain ⟨nextMemos, _, secondaryKept⟩ := SourceCurrentSecondaryMemos.lift_class _ _ _ _ _ secondary
        (SourceEqualityExposureCosts.gate_ready primaryReady.semantic primaryCosts) primaryValues primaryMemos primaryKept.valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver (first.trans second) _ correct
      exact ih nextReady nextValues nextCosts nextFields
        (fun paths member => proper paths (List.mem_cons_of_mem _ member)) nextCorrect nextMemos secondaryKept.valid
  | continued primary secondary seeded call rest ih =>
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        primary_advance source reaches primary ready available costs fields
      obtain ⟨primaryMemos, _, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available memos valid
      have primaryCorrect := SourceCurrentEmptinessMemo.grows formulas solver first _ correct
      obtain ⟨nextMemos, _, queryValid, nextReady, nextCosts, nextFields, _, nextValues, nextCorrect, _⟩ :=
        SourceCurrentClassQueryGlobalMemos.query_memos _ values (proper _ List.mem_cons_self)
          secondary seeded call primaryReady primaryValues primaryCosts primaryFields
          formulas solver primaryCorrect primaryMemos primaryKept.valid
      exact ih nextReady nextValues nextCosts nextFields
        (fun paths member => proper paths (List.mem_cons_of_mem _ member)) nextCorrect nextMemos queryValid
  | stopped => simp

/-- Every selected class has an actual primary false certificate at one common returned heap. -/
theorem selected_primary [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values classes before memo outcome selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∀ paths ∈ selected,
      EndpointStatefulGateTrace.ClassTrace source reaches values paths after.machine.heap false after.machine.heap :=
  fun paths member => (selected_origins trace ready available costs fields proper formulas solver correct
    memos valid paths member).replay

private theorem class_paths [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : Class} {state : State Symbol Guard}
    (actual : EndpointStatefulGateTrace.ClassTrace source reaches values paths state false state)
    (semantic : SemanticReady state) (available : Values state values) :
    ∀ path ∈ paths, SourceCurrentSecondaryTrace.PathTrace source values path state false state :=
  SourceCurrentSecondaryReplay.false_class_paths source values paths state state
    (SourceCurrentPrimaryProjectionSupport.class_false actual) semantic available state (grows_refl state)

private theorem paths_trace [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : Class} {state : State Symbol Guard}
    (allPaths : ∀ path ∈ paths, SourceCurrentSecondaryTrace.PathTrace source values path state false state) :
    SourceCurrentSecondaryTrace.ClassTrace source values paths state false state := by
  induction paths with
  | nil => exact .nil
  | cons first rest ih =>
      exact .next (allPaths first List.mem_cons_self)
        (ih (fun path member => allPaths path (List.mem_cons_of_mem first member)))

/-- The canonical selected union supplies the exact original-child required-trie domain. -/
theorem selected_domain [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {selected : Constraints} {state : State Symbol Guard}
    (semantic : SemanticReady state) (costs : CostHeap state) (available : Values state values)
    (primary : ∀ paths ∈ selected,
      EndpointStatefulGateTrace.ClassTrace source reaches values paths state false state) :
    SourceCurrentRequiredSupport.ForestSupport source state
      (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) values := by
  have gate : SourceCurrentSecondaryTrace.ClassTrace source values
      (canonicalClass selected.flatten) state false state := by
    apply paths_trace
    intro path member
    obtain ⟨paths, included, present⟩ := List.mem_flatten.mp ((mem_canonicalClass _ _).mp member)
    exact class_paths (primary paths included) semantic available path present
  have anchor := SourceCurrentSecondaryProjectionAnchor.class_anchor source gate semantic
    (SourceEqualityExposureCosts.gate_ready semantic costs) available
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected) with
  | node entries =>
      intro index child found value selectedValue path tip _nonroot
      have whole : SourceCurrentRequiredSupport.Tip
          (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) (index :: path) := by
        rw [compiled]
        exact .child found tip
      have member := whole.build_member (by simp)
      obtain ⟨original, present, same⟩ := List.mem_map.mp member
      have originalEqual : original = index :: path := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map Int.toNat) same
      subst original
      have pathTrace := anchor.2.2.2.2.2 (index :: path) present
      cases pathTrace with
      | child childTrace =>
          exact Or.inr ⟨available value (List.mem_of_getElem? selectedValue),
            SourceCurrentSecondaryReplay.false_selected childTrace selectedValue⟩

/-- Actual scans derive shared final support and all four completed memo invariants. -/
theorem scan_support [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values classes before memo outcome selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, SourceCurrentClassScanGlobalMemos.ScanReads trace memos final ∧ Valid after.machine.heap final ∧
      IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved ∧
      InternedFreshOrdinaryMemoGateTrace.Ready after.machine.heap ∧
      (∀ paths ∈ selected, Origin values paths after.machine.heap) ∧
      (∀ paths ∈ selected,
        EndpointStatefulGateTrace.ClassTrace source reaches values paths after.machine.heap false after.machine.heap) ∧
      SourceCurrentRequiredSupport.ForestSupport source after.machine.heap
        (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) values := by
  obtain ⟨final, reads, finalValid, finalReady, finalCosts, finalFields, kept,
      finalValues, finalCorrect, extension⟩ := SourceCurrentClassScanGlobalMemos.scan_memos trace
    ready available costs fields proper formulas solver correct memos valid
  have origins := selected_origins trace ready available costs fields proper formulas solver correct memos valid
  have primary := fun paths member => (origins paths member).replay
  exact ⟨final, reads, finalValid, finalReady, finalCosts, finalFields, kept, finalValues,
    finalCorrect, extension, SourceEqualityExposureCosts.gate_ready finalReady.semantic finalCosts,
    origins, primary, selected_domain finalReady.semantic finalCosts finalValues primary⟩

/-- Positional original records retain the same primary receipt without changing their fields. -/
theorem retained_primary [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    {trace : Scan source reaches values classes before memo outcome selected after saved}
    {records kept : List SourceEqualityClassOrder.Record}
    (retained : SourceCurrentSelectedClassRecords.Retained trace records kept)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∀ record ∈ kept, Origin values record.paths after.machine.heap ∧
      EndpointStatefulGateTrace.ClassTrace source reaches values record.paths after.machine.heap false after.machine.heap := by
  intro record member
  have selectedMember : record.paths ∈ selected := by
    rw [← retained.fields.2]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  have origin := selected_origins trace ready available costs fields proper formulas solver correct
    memos valid record.paths selectedMember
  exact ⟨origin, origin.replay⟩

end MicroCFTA.SourceCurrentClassScanSupport
