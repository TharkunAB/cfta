import MicroCFTA.SourceCurrentEqualityOperationFixed
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.EqualityOperationKernels
open EqualityNormalize SourceEqualityConstraintAllocation
open SourceCurrentEqualityOperationFixed
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid
private def raw : Constraints := [[[0,0],[0,1]],[[0,1],[0,2]]]
private def merged : Constraints := [[[0,0],[0,1],[0,2]]]
private def suffixes : Constraints := [[[0],[1],[2]]]
private def rawRecords : List SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordsOf raw).getD []
private def mergedRecords : List SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordsOf merged).getD []
private def childRecords : List SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordsOf suffixes).getD []
private def own : SourceSymbolicIndex.Constraint FullSyntax.Formula :=
  SourceEqualityConstraintConstructors.top
private def initial : Operations :=
  SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def original : Value := .live 1 rawRecords
private def combined : Value := .live 2 mergedRecords
private def child : Value := .live 3 childRecords
private def before : Operations :=
  {initial with constraints := (intern (some rawRecords) initial.constraints).2}
private def middle : Operations :=
  ⟨(intern (some mergedRecords) before.constraints).2,
    Cache.keepFirst before.combinations (some 1, some 0) ⟨original, .live 0 [], combined⟩,
    before.descents⟩
private def after : Operations :=
  (SourceEqualityConstraintMemoAllocation.descend combined 0 middle).2

private theorem raw_normalized : SourceCompactGuards.normalize raw = some merged := by
  have small : mkEqConstraints 2 raw = .normalized merged := by cbv
  have array := SourceEqualityNormalizationReceipt.array_eq 2 raw
    (by rw [small]; intro impossible; cases impossible)
  unfold SourceCompactGuards.normalize
  rw [array,small]
  rfl

private theorem raw_cached : SourceEqualityGuardReadback.Cached (some raw) := by
  intro classes same
  cases same
  refine ⟨?_, by cbv, ?_⟩
  · intro paths member
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨[0,0], by simp, [0,1], by simp, by decide⟩
    · exact ⟨[0,1], by simp, [0,2], by simp, by decide⟩
  · intro paths member
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cbv

private theorem raw_read :
    SourceEqualityPhysicalPayload.read (some raw) = .ok (some rawRecords) := by cbv

private theorem constructed :
    construct (some raw) initial.constraints = (.ok original, before.constraints) := by
  rw [construct,raw_read]
  cbv

private theorem not_fixed : ¬ FixedPayload original.payload := by
  intro fixed
  have same := fixed rawRecords rfl
  have paths : rawRecords.map SourceEqualityClassOrder.Record.paths = raw := by cbv
  rw [paths,raw_normalized] at same
  have different : merged ≠ raw := by decide
  exact different (Option.some.inj same)

private theorem payload_combined :
    SourceEqualityInheritedPayload.combine (some rawRecords) (some []) = .ok (some mergedRecords) := by
  change SourceEqualityPhysicalPayload.read
    (SourceCompactGuards.combineEqualities
      (some (rawRecords.map SourceEqualityClassOrder.Record.paths)) (some [])) = _
  have paths : rawRecords.map SourceEqualityClassOrder.Record.paths = raw := by cbv
  rw [paths]
  change SourceEqualityPhysicalPayload.read (SourceCompactGuards.normalize (raw ++ [])) = _
  rw [List.append_nil,raw_normalized]
  cbv

private theorem combine_nonempty (identity : Nat) (rows : List SourceEqualityClassOrder.Record)
    (emptyIdentity : Nat) (state : Operations) (nonempty : rows ≠ []) :
    SourceEqualityConstraintMemoAllocation.combine (.live identity rows) (.live emptyIdentity []) state =
      SourceEqualityConstraintMemoAllocation.combineCached (.live identity rows) (.live emptyIdentity []) state := by
  cases rows with
  | nil => exact (nonempty rfl).elim
  | cons first rest => rfl

private theorem combine_actual :
    SourceEqualityConstraintMemoAllocation.combine original (.live 0 []) before = (.ok combined,middle) := by
  unfold original
  rw [combine_nonempty 1 rawRecords 0 before (by cbv; intro impossible; cases impossible)]
  have absent : before.combinations (some 1,some 0) = none := rfl
  simp only [SourceEqualityConstraintMemoAllocation.combineCached,Value.identity,Value.payload,absent]
  rw [payload_combined]
  cbv

private theorem prefix_actual :
    SourceCurrentAllocatedInheritedPrefix.run own original before = (.ok (some combined),middle) := by
  have accessor : SourceCurrentConjunctionEquality.accessor own before =
      (.ok (some (.live 0 [])),before) := by cbv
  unfold original
  rw [SourceCurrentAllocatedInheritedPrefix.run_combine own 1 rawRecords before (.live 0 [])
    (congrArg Prod.fst accessor),accessor]
  change ((SourceEqualityConstraintMemoAllocation.combine original (.live 0 []) before).1.map some,
    (SourceEqualityConstraintMemoAllocation.combine original (.live 0 []) before).2) = _
  rw [combine_actual]
  rfl

private theorem descend_actual :
    SourceEqualityConstraintMemoAllocation.descend combined 0 middle = (child,after) := by cbv

private theorem warm_prefix :
    SourceCurrentAllocatedInheritedPrefix.run own original after = (.ok (some combined),after) := by cbv

private theorem warm_combine :
    SourceEqualityConstraintMemoAllocation.combine original (.live 0 []) after = (.ok combined,after) := by cbv

private theorem warm_descend :
    SourceEqualityConstraintMemoAllocation.descend combined 0 after = (child,after) := by cbv

private theorem initial_operations_proof :
    construct (some raw) initial.constraints = (.ok original,before.constraints) ∧
    Valid before ∧ Ready before.constraints original ∧ Ready before.constraints (.live 0 []) ∧
    ¬ FixedPayload original.payload ∧
    SourceCurrentAllocatedInheritedPrefix.run own original before = (.ok (some combined),middle) ∧
    SourceEqualityConstraintMemoAllocation.combine original (.live 0 []) before = (.ok combined,middle) ∧
    SourceEqualityConstraintMemoAllocation.descend combined 0 middle = (child,after) ∧
    SourceEqualityInheritedPayload.classes combined.payload = some merged ∧
    SourceEqualityInheritedPayload.classes child.payload = some suffixes ∧
    Valid after ∧ Ready after.constraints child ∧ FixedPayload child.payload ∧
    SourceCurrentAllocatedInheritedPrefix.run own original after = (.ok (some combined),after) ∧
    SourceEqualityConstraintMemoAllocation.combine original (.live 0 []) after = (.ok combined,after) ∧
    SourceEqualityConstraintMemoAllocation.descend combined 0 after = (child,after) := by
  obtain ⟨initialValid, _, emptyReady⟩ := SourceEqualityMkEdgeAllocation.emptyField_correct
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  obtain ⟨value,cache,actual,_,ready,steps,_,_⟩ :=
    construct_complete (some raw) raw_cached initial.constraints initialValid.constraints
  have pair := Prod.mk.inj (actual.symm.trans constructed)
  have valueSame : value = original := Except.ok.inj pair.1
  subst value
  have cacheSame : cache = before.constraints := pair.2
  subst cache
  have beforeValid : Valid before := initialValid.steps _ steps
  have beforeEmpty : Ready before.constraints (.live 0 []) :=
    emptyReady.grows (Cache.steps_table_extends steps)
  have initialField := (SourceCurrentConjunctionFieldAllocation.empty_field
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid).2.2
  have growth : SourceEqualityConstraintMemoAllocation.Grows initial before :=
    ⟨steps,Cache.extends_refl _,Cache.extends_refl _⟩
  have beforeField := initialField.grows growth
  obtain ⟨result,done,checked⟩ := prefix_descend own original 0 before
    beforeValid ready beforeField
  have resultSame : result = combined := Option.some.inj (Except.ok.inj
    (done.symm.trans (congrArg Prod.fst prefix_actual)))
  subst result
  have middleSame := congrArg Prod.snd prefix_actual
  rw [middleSame] at checked
  obtain ⟨_,_,_,finalValid,finalReady,_,fixed⟩ := checked
  rw [descend_actual] at finalValid finalReady fixed
  exact ⟨constructed,beforeValid,ready,beforeEmpty,not_fixed,prefix_actual,combine_actual,descend_actual,
    by cbv,by cbv,finalValid,finalReady,fixed,warm_prefix,warm_combine,warm_descend⟩

/-- Actual combination and descent produce a fixed child from Ready overlapping input records that are not initially fixed. Both repeated operations retain the returned state. -/
theorem initial_operations :
    construct (some raw) initial.constraints = (.ok original,before.constraints) ∧
    Valid before ∧ Ready before.constraints original ∧ Ready before.constraints (.live 0 []) ∧
    ¬ FixedPayload original.payload ∧
    SourceCurrentAllocatedInheritedPrefix.run own original before = (.ok (some combined),middle) ∧
    SourceEqualityConstraintMemoAllocation.combine original (.live 0 []) before = (.ok combined,middle) ∧
    SourceEqualityConstraintMemoAllocation.descend combined 0 middle = (child,after) ∧
    SourceEqualityInheritedPayload.classes combined.payload = some merged ∧
    SourceEqualityInheritedPayload.classes child.payload = some suffixes ∧
    Valid after ∧ Ready after.constraints child ∧ FixedPayload child.payload ∧
    SourceCurrentAllocatedInheritedPrefix.run own original after = (.ok (some combined),after) ∧
    SourceEqualityConstraintMemoAllocation.combine original (.live 0 []) after = (.ok combined,after) ∧
    SourceEqualityConstraintMemoAllocation.descend combined 0 after = (child,after) := initial_operations_proof
end MicroCFTA.EqualityOperationKernels
#check @MicroCFTA.EqualityOperationKernels.initial_operations
#print MicroCFTA.EqualityOperationKernels.initial_operations
#print axioms MicroCFTA.EqualityOperationKernels.initial_operations
