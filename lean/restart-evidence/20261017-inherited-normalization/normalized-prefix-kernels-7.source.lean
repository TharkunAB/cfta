import MicroCFTA.SourceCurrentNormalizedInheritedPrefix
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

namespace MicroCFTA.NormalizedPrefixKernels
open SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid
local notation "prefix" => SourceCurrentAllocatedInheritedPrefix.run
private def raw : EqualityNormalize.Constraints := [[[0,0],[0,1]]]
private def records : List SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordsOf raw).getD []
private def own : SourceSymbolicIndex.Constraint FullSyntax.Formula :=
  SourceEqualityConstraintConstructors.top
private def initial : Operations :=
  SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def inherited : Value := .live 1 records
private def start : Operations :=
  { initial with constraints := (intern (some records) initial.constraints).2 }
private noncomputable def cold : Operations := (prefix own inherited start).2

private theorem raw_normalized : SourceCompactGuards.normalize raw = some raw := by
  have small : EqualityNormalize.mkEqConstraints 2 raw = .normalized raw := by cbv
  have array := SourceEqualityNormalizationReceipt.array_eq 2 raw
    (by rw [small]; intro impossible; cases impossible)
  unfold SourceCompactGuards.normalize
  rw [array, small]
  rfl

private theorem raw_read :
    SourceEqualityPhysicalPayload.read (some raw) = .ok (some records) := by cbv

private theorem actual_normalize :
    normalize raw initial.constraints = (.ok inherited, start.constraints) := by
  rw [normalize, raw_normalized, construct, raw_read]
  cbv

private theorem empty_own : SourceCompactGuards.sourceEqualities own = some [] := by
  unfold own SourceEqualityConstraintConstructors.top SourceCompactGuards.sourceEqualities
  rfl

private theorem empty_combination :
    SourceEqualityInheritedPayload.combine (some records) (some []) = .ok (some records) := by
  change SourceEqualityPhysicalPayload.read
    (SourceCompactGuards.combineEqualities (some (records.map SourceEqualityClassOrder.Record.paths)) (some [])) = _
  have paths : records.map SourceEqualityClassOrder.Record.paths = raw := by cbv
  rw [paths, SourceCurrentEqualityNormalizationFixed.combine_empty_right raw raw_normalized]
  exact raw_read

private theorem accessor_start :
    SourceCurrentConjunctionEquality.accessor own start = (.ok (some (.live 0 [])), start) := by
  cbv

private theorem cold_actual : (prefix own inherited start).1 = .ok (some inherited) := by
  unfold inherited
  rw [SourceCurrentAllocatedInheritedPrefix.run_combine own 1 records start (.live 0 [])
    (congrArg Prod.fst accessor_start), accessor_start]
  unfold SourceEqualityConstraintMemoAllocation.combine SourceEqualityConstraintMemoAllocation.combineCached
  change (match SourceEqualityInheritedPayload.combine (some records) (some []) with
    | .error message => ((Except.error message : Except String Value), start)
    | .ok payload =>
      let built := intern payload start.constraints
      (.ok built.1, (⟨built.2,
        Cache.keepFirst start.combinations (some 1, some 0) ⟨inherited, .live 0 [], built.1⟩,
        start.descents⟩ : Operations))).1.map some = _
  rw [empty_combination]
  cbv

private theorem cold_state : cold =
    {start with combinations :=
      (Cache.keepFirst start.combinations (some 1, some 0) ⟨inherited, .live 0 [], inherited⟩)} := by
  unfold cold inherited
  rw [SourceCurrentAllocatedInheritedPrefix.run_combine own 1 records start (.live 0 [])
    (congrArg Prod.fst accessor_start), accessor_start]
  unfold SourceEqualityConstraintMemoAllocation.combine SourceEqualityConstraintMemoAllocation.combineCached
  change (match SourceEqualityInheritedPayload.combine (some records) (some []) with
    | .error message => ((Except.error message : Except String Value), start)
    | .ok payload =>
      let built := intern payload start.constraints
      (.ok built.1, (⟨built.2,
        Cache.keepFirst start.combinations (some 1, some 0) ⟨inherited, .live 0 [], built.1⟩,
        start.descents⟩ : Operations))).2 = _
  rw [empty_combination]
  cbv

private theorem warm_actual : prefix own inherited cold = (.ok (some inherited), cold) := by
  rw [cold_state]
  cbv

private theorem allocated_prefix_proof :
    initial.constraints.next = 1 ∧
    normalize raw initial.constraints = (.ok inherited, start.constraints) ∧
    Valid start ∧ Ready start.constraints inherited ∧
    SourceCurrentConjunctionEquality.FieldAvailable start own ∧
    (prefix own inherited start).1 = .ok (some inherited) ∧
    prefix own inherited cold = (.ok (some inherited), cold) ∧
    SourceCurrentOuterInheritedDescent.pathHeight inherited = 2 ∧
    SourceCurrentOuterInheritedDescent.pathHeight
      (SourceEqualityConstraintMemoAllocation.descend inherited 0 cold).1 < 2 ∧
    (SourceCurrentAllocatedPartialState.NodeRequest.mk
      (SourceEqualityConstraintMemoAllocation.descend inherited 0 cold).1 .empty).key ≠
      (SourceCurrentAllocatedPartialState.NodeRequest.mk inherited .empty).key := by
  obtain ⟨initialValid, _, field⟩ := SourceCurrentConjunctionFieldAllocation.empty_field
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  obtain ⟨value, cache, actual, valid, ready, growth, strict⟩ :=
    SourceCurrentNormalizedInheritedPrefix.normalized own raw initial initialValid field empty_own
  have same := Prod.mk.inj (actual.symm.trans actual_normalize)
  have valueSame : value = inherited := Except.ok.inj same.1
  subst value
  have cacheSame : cache = start.constraints := same.2
  subst cache
  change Valid start at valid
  change Ready start.constraints inherited at ready
  change SourceEqualityConstraintMemoAllocation.Grows initial start at growth
  have startField := field.grows growth
  have fixed : SourceCurrentEqualityNormalizationFixed.Fixed
      (records.map SourceEqualityClassOrder.Record.paths) := by
    have paths : records.map SourceEqualityClassOrder.Record.paths = raw := by cbv
    rw [paths]
    exact SourceCurrentEqualityNormalizationFixed.normalize_idempotent raw raw raw_normalized
  have physical := SourceCurrentNormalizedInheritedPrefix.plain own 1 records start valid ready
    startField empty_own fixed
  have nonempty : records ≠ [] := by cbv; intro impossible; cases impossible
  have height : SourceCurrentOuterInheritedDescent.pathHeight inherited = 2 := by cbv
  have lowered := strict 1 records rfl nonempty 0
  have lowerHeight : SourceCurrentOuterInheritedDescent.pathHeight
      (SourceEqualityConstraintMemoAllocation.descend inherited 0 cold).1 < 2 := by
    have comparison : SourceCurrentOuterInheritedDescent.pathHeight
        (SourceEqualityConstraintMemoAllocation.descend inherited 0 cold).1 <
        SourceCurrentOuterInheritedDescent.pathHeight inherited := lowered.2.1
    exact height ▸ comparison
  exact ⟨by cbv, actual_normalize, valid, ready, startField, cold_actual, warm_actual,
    height, lowerHeight,
    SourceCurrentOuterInheritedDescent.node_key_ne 1 records 0 cold physical.2.1
      physical.2.2.1 nonempty .empty⟩

/-- Initial raw normalization and an allocated empty own field produce a cold prefix, an exact warm state, and a different descended request key. -/
theorem allocated_prefix :
    initial.constraints.next = 1 ∧
    normalize raw initial.constraints = (.ok inherited, start.constraints) ∧
    Valid start ∧ Ready start.constraints inherited ∧
    SourceCurrentConjunctionEquality.FieldAvailable start own ∧
    (prefix own inherited start).1 = .ok (some inherited) ∧
    prefix own inherited cold = (.ok (some inherited), cold) ∧
    SourceCurrentOuterInheritedDescent.pathHeight inherited = 2 ∧
    SourceCurrentOuterInheritedDescent.pathHeight
      (SourceEqualityConstraintMemoAllocation.descend inherited 0 cold).1 < 2 ∧
    (SourceCurrentAllocatedPartialState.NodeRequest.mk
      (SourceEqualityConstraintMemoAllocation.descend inherited 0 cold).1 .empty).key ≠
      (SourceCurrentAllocatedPartialState.NodeRequest.mk inherited .empty).key :=
  allocated_prefix_proof
end MicroCFTA.NormalizedPrefixKernels

#check @MicroCFTA.NormalizedPrefixKernels.allocated_prefix
#print MicroCFTA.NormalizedPrefixKernels.allocated_prefix
#print axioms MicroCFTA.NormalizedPrefixKernels.allocated_prefix
