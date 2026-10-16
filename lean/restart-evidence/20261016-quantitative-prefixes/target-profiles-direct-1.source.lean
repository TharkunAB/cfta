import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputExecution

/-!
# Quantitative profiles of supplied target reads

The proof follows the same operand, recursive tail, and checked native return.
It derives each intermediate profile from the original captured forest.
No constructor headroom or future result profile is an input.
Structural, output, and Merge certificates retain their separate laws.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetProfiles
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open MergedOrdinaryHeight (height childrenHeight)
namespace Numbers
export SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers
  (operandRows targetRows targetRows_base targetRows_step)
end Numbers
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

/-- An actual operand derives its profile from the same projection and actual Merge winner. -/
theorem operand_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧
      NodeShape (Numbers.operandRows rows count depth bound) arity result ∧ height result ≤ bound := by
  have certificates := SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores.receipt receipt
    physicalStored profiles native output ready.idle
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have projectedProfile := SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forest_uniform projection.graph
    ready.semantic available profile count depth bound lengthBound pathBound heightBound
  cases merged.actual with
  | done call =>
      have produced := SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer.call_profile call.graph
        projection.ready.semantic projection.ready.costs (physicalStored.grows projection.effects.keeps)
        profiles projection.available
      have shaped := produced.2.2.2.2 _ _ bound projectedProfile.1 projectedProfile.2
      exact ⟨certificates.1, certificates.2.1, certificates.2.2.1,
        shaped.1, Nat.le_trans shaped.2 projectedProfile.2⟩

/-- The actual rotated fold derives each query profile at the exact returned tail state. -/
theorem fold
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved} (reads : FoldReads formulas solver actual memos final) :
    Ready before → Values before.native.machine.heap values → PhysicalStored before.native.machine.heap memo →
      Profiles memo → NativeStored before.native → OutputStored before.native →
      ∀ rows arity count depth bound, ChildrenShape rows arity values → values.length ≤ count →
      (∀ path ∈ seed :: paths, path.length ≤ depth) → childrenHeight values ≤ bound →
      Ready after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧ Available after.native.machine.heap result ∧
      NodeShape (Numbers.targetRows rows count depth bound paths.length) (max arity 1) result ∧ height result ≤ bound := by
  induction reads with
  | nil receipt =>
      intro ready available physical profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound
      obtain ⟨merged, nativeAfter, outputAfter, shaped, bounded⟩ := operand_receipt receipt ready available
        physical profiles native output rows arity count depth bound profile lengthBound (pathsBound _ List.mem_cons_self) heightBound
      exact ⟨receipt.ready, receipt.effects, receipt.stored, merged, nativeAfter, outputAfter, receipt.available,
        NodeShape.mono _ shaped (Nat.le_refl _) (Nat.le_max_left _ _), bounded⟩
  | cons receipt remaining query ih =>
      intro ready available physical profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound
      obtain ⟨headMerged, headNative, headOutput, headShape, _headHeight⟩ := operand_receipt receipt ready available
        physical profiles native output rows arity count depth bound profile lengthBound (pathsBound _ (by simp)) heightBound
      obtain ⟨tailReady, tailEffects, tailPhysical, tailMerged, tailNative, tailOutput, _tailAvailable, tailShape, tailHeight⟩ :=
        ih receipt.ready receipt.originals receipt.stored headMerged headNative headOutput
          rows arity count depth bound profile lengthBound (tail_all pathsBound) heightBound
      cases query.actual with
      | run trace =>
          have structural := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace tailReady.good tailReady.semantic tailNative
            ⟨rfl, NodeShape.domain _ headShape, NodeShape.domain _ tailShape⟩
          have shaped := SourceCurrentAllocatedFiniteOrdinaryOutputExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace tailReady.good tailReady.semantic tailOutput rfl
            (max (Numbers.operandRows rows count depth bound) _) (max arity 1)
            (NodeShape.mono _ headShape (Nat.le_max_left _ _) (Nat.le_max_left _ _))
            (NodeShape.mono _ tailShape (Nat.le_max_right _ _) (Nat.le_refl _))
          refine ⟨query.ready, receipt.effects.trans (tailEffects.trans query.effects),
            tailPhysical.grows query.effects.keeps, tailMerged, structural.1, shaped.1, query.available, ?_,
            Nat.le_trans structural.2.2.2 tailHeight⟩
          simpa only [List.length_cons, Numbers.targetRows_step, Nat.max_assoc, Nat.max_self] using shaped.2

/-- Supplied whole-target reads retain all three certificate tables and their actual quantitative result. -/
theorem target_reads
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Target values paths before memo result after saved} (reads : TargetReads formulas solver actual memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧
      NodeShape (SourceCurrentAllocatedFiniteOrdinaryTargetResources.outputRows rows count depth bound paths.length)
        (max arity 1) result ∧ height result ≤ bound := by
  cases reads with
  | nil => exact ⟨profiles, native, output, True.intro, Nat.zero_le _⟩
  | cons remaining =>
      obtain ⟨_, _, _, merged, nativeAfter, outputAfter, _, shaped, bounded⟩ := fold remaining ready available
        physicalStored profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound
      exact ⟨merged, nativeAfter, outputAfter, shaped, bounded⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetProfiles
