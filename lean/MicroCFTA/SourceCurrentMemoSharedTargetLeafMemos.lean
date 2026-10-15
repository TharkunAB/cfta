import MicroCFTA.SourceCurrentMemoSharedTargetLeaf

/-!
# Global table receipts for memo-aware shared leaves

The receipt follows the actual target force before the native intersection.
The native part uses its instruction-derived constructor event trace. The
completed merge table remains separate from the three global gate tables.
These receipts describe completed resident inputs, not delayed GHC demands.
-/
namespace MicroCFTA.SourceCurrentMemoSharedTargetLeaf
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedTargetForce
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "GlobalEffect" => SourceCurrentSubsumesQueryMemos.Effect

/-- The force receipt precedes the exact native instruction receipt. -/
inductive Reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {record : SourceEqualityClassOrder.Record} → {values : List (Value Symbol Guard)} →
    {path : EqualityNormalize.Path} → {input result : Value Symbol Guard} →
    {before after : State width Symbol Guard} →
    Leaf emptyGuard conjoin clear top record values path input before result after → Memos → Memos → Prop where
  | apply (forcedRead : SourceCurrentMemoSharedTargetForce.Reads forced memos middle)
      (nativeRead : SourceCurrentMemoDemandTarget.StepReads step middle final) :
      Reads (.apply forced step) memos final

/-- Actual leaves derive coherent final tables in force-then-native order. -/
theorem Leaf.memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = [])
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final, Reads trace memos final ∧ GlobalEffect before.native.machine.heap after.native.machine.heap memos final := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known domains member
      have own := first.2.1.available input available
      obtain ⟨middle, forcedRead, firstEffect⟩ := forced.memos ready known domains member memos valid
      obtain ⟨events, actual, silent, coherent⟩ := SourceNativeGlobalMemos.scoped_memos step first.1.native
        first.2.2.1 own first.2.2.2.1 inputClosed (fun _ _ => true) (fun _ _ _ => rfl) middle firstEffect.valid
      have checked := step.verified first.1.native first.2.2.1 own first.2.2.2.1 inputClosed
        (fun _ _ => true) (fun _ _ _ => rfl)
      have nativeEffect : GlobalEffect _ _ middle middle :=
        ⟨checked.2.1, checked.1.semantic, step.cost_heap first.1.native first.1.costs first.2.2.1 own,
          coherent, extends_refl _, rfl⟩
      exact ⟨middle, .apply (step := step) forcedRead ⟨rfl, events, actual, silent⟩,
        SourceCurrentMemoMergeQueryMemos.effect_trans firstEffect nativeEffect⟩

end MicroCFTA.SourceCurrentMemoSharedTargetLeaf
