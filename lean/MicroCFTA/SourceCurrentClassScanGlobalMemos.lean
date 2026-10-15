import MicroCFTA.SourceCurrentClassQueryGlobalMemos
import MicroCFTA.SourceCurrentEqualityClassScanSoundness

/-!
# Current class scans with four coherent completed memo families

Each branch retains the reached primary, secondary, and query calls in
source order. A true emptiness answer stops before the class suffix. The
proof derives final validity from the initial tables and proper original
paths. It supplies no acceptance or future-state premise. The source lazy
runtime and pending memo publication remain outside these completed traces.
-/
namespace MicroCFTA.SourceCurrentClassScanGlobalMemos
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceCurrentEqualityClassScan
open SourceCurrentClassQueryGlobalMemos
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

/-- Only reached scan calls carry the three tables returned to the next source operation. -/
inductive ScanReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {classes selected : Constraints} → {outcome : Option Class} →
    {before after : Native width Symbol Guard} → {memo saved : Memo} →
    Scan source reaches values classes before memo outcome selected after saved → Memos → Memos → Prop where
  | nil : ScanReads .nil memos memos
  | selected (first : EndpointMemoGateTrace.ClassReads primary memos middle)
      (tail : ScanReads rest middle final) : ScanReads (.selected primary rest) memos final
  | skipped (first : EndpointMemoGateTrace.ClassReads primary memos middle)
      (second : SourceCurrentSecondaryMemos.ClassReads secondary middle later)
      (tail : ScanReads rest later final) : ScanReads (.skipped primary secondary rest) memos final
  | continued {values : List (Value Symbol Guard)} {paths : Class} {classes selected : Constraints}
      {before middleNative laterNative after : Native width Symbol Guard} {heap anchor : State Symbol Guard}
      {query : Value Symbol Guard} {memo savedMemo saved : Memo} {outcome : Option Class}
      {primary : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace source values paths heap false anchor}
      {seeded : SourceEmptinessClassFold.Seeded top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middleNative}
      {call : SourceCurrentEmptinessMemo.Call memo query middleNative false laterNative savedMemo}
      {rest : Scan source reaches values classes laterNative savedMemo outcome selected after saved}
      {memos middle later final : Memos}
      (first : EndpointMemoGateTrace.ClassReads primary memos middle)
      (second : QueryReads (before := advanceHeap before heap) secondary seeded call middle later)
      (tail : ScanReads rest later final) : ScanReads (.continued primary secondary seeded call rest) memos final
  | stopped {values : List (Value Symbol Guard)} {paths : Class} {classes : Constraints}
      {before middleNative after : Native width Symbol Guard} {heap anchor : State Symbol Guard}
      {query : Value Symbol Guard} {memo saved : Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace source values paths heap false anchor}
      {seeded : SourceEmptinessClassFold.Seeded top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middleNative}
      {call : SourceCurrentEmptinessMemo.Call memo query middleNative true after saved}
      {memos middle final : Memos}
      (first : EndpointMemoGateTrace.ClassReads primary memos middle)
      (second : QueryReads (before := advanceHeap before heap) secondary seeded call middle final) :
      ScanReads (.stopped (classes := classes) primary secondary seeded call) memos final

/-- Every reached scan derives coherent final tables and physical invariants from its initial state. -/
theorem scan_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values classes before memo outcome selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, ScanReads trace memos final ∧ Valid after.machine.heap final ∧
      IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  induction trace generalizing memos with
  | nil =>
      exact ⟨memos, .nil, valid, ready, costs, fields, pure_keeps _ ready.semantic.ready, available,
        correct, fun _ _ found => found⟩
  | selected primary rest ih =>
      obtain ⟨nextReady, nextCosts, nextFields, first, nextValues⟩ :=
        SourceCurrentEqualityClassScanSoundness.primary_advance source reaches primary ready available costs fields
      obtain ⟨nextMemos, firstRead, firstKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available memos valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver first _ correct
      obtain ⟨final, tailRead, finalValid, finalReady, finalCosts, finalFields, later, finalValues, finalCorrect, extension⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => proper paths (List.mem_cons_of_mem _ member)) nextCorrect nextMemos firstKept.valid
      exact ⟨final, .selected firstRead tailRead, finalValid, finalReady, finalCosts, finalFields,
        first.trans later, finalValues, finalCorrect, extension⟩
  | skipped primary secondary rest ih =>
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        SourceCurrentEqualityClassScanSoundness.primary_advance source reaches primary ready available costs fields
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available memos valid
      obtain ⟨nextReady, nextCosts, nextFields, second, nextValues⟩ :=
        SourceCurrentEqualityClassScanSoundness.secondary_advance source secondary primaryReady primaryValues primaryCosts primaryFields
      obtain ⟨nextMemos, secondaryRead, secondaryKept⟩ := SourceCurrentSecondaryMemos.lift_class _ _ _ _ _ secondary
        (SourceEqualityExposureCosts.gate_ready primaryReady.semantic primaryCosts) primaryValues primaryMemos primaryKept.valid
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver (first.trans second) _ correct
      obtain ⟨final, tailRead, finalValid, finalReady, finalCosts, finalFields, later, finalValues, finalCorrect, extension⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => proper paths (List.mem_cons_of_mem _ member)) nextCorrect nextMemos secondaryKept.valid
      exact ⟨final, .skipped primaryRead secondaryRead tailRead, finalValid, finalReady, finalCosts, finalFields,
        first.trans (second.trans later), finalValues, finalCorrect, extension⟩
  | continued primary secondary seeded call rest ih =>
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        SourceCurrentEqualityClassScanSoundness.primary_advance source reaches primary ready available costs fields
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available memos valid
      have primaryCorrect := SourceCurrentEmptinessMemo.grows formulas solver first _ correct
      obtain ⟨nextMemos, queryRead, queryValid, nextReady, nextCosts, nextFields, second, nextValues, nextCorrect, firstExtends⟩ :=
        query_memos _ values (proper _ List.mem_cons_self) secondary seeded call primaryReady primaryValues
          primaryCosts primaryFields formulas solver primaryCorrect primaryMemos primaryKept.valid
      obtain ⟨final, tailRead, finalValid, finalReady, finalCosts, finalFields, later, finalValues, finalCorrect, laterExtends⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => proper paths (List.mem_cons_of_mem _ member)) nextCorrect nextMemos queryValid
      exact ⟨final, .continued (memos := memos) (middle := primaryMemos) (later := nextMemos) (primary := primary) (secondary := secondary) (seeded := seeded) (call := call) (rest := rest) primaryRead queryRead tailRead, finalValid, finalReady, finalCosts, finalFields,
        first.trans (second.trans later), finalValues, finalCorrect,
        fun key entry found => laterExtends key entry (firstExtends key entry found)⟩
  | stopped primary secondary seeded call =>
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        SourceCurrentEqualityClassScanSoundness.primary_advance source reaches primary ready available costs fields
      obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
        (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available memos valid
      have primaryCorrect := SourceCurrentEmptinessMemo.grows formulas solver first _ correct
      obtain ⟨final, queryRead, finalValid, finalReady, finalCosts, finalFields, second, finalValues, finalCorrect, extension⟩ :=
        query_memos _ values (proper _ List.mem_cons_self) secondary seeded call primaryReady primaryValues
          primaryCosts primaryFields formulas solver primaryCorrect primaryMemos primaryKept.valid
      exact ⟨final, .stopped (memos := memos) (middle := primaryMemos) (primary := primary) (secondary := secondary) (seeded := seeded) (call := call) primaryRead queryRead, finalValid, finalReady, finalCosts, finalFields,
        first.trans second, finalValues, finalCorrect, extension⟩

end MicroCFTA.SourceCurrentClassScanGlobalMemos
