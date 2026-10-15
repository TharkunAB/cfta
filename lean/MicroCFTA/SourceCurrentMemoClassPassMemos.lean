import MicroCFTA.SourceCurrentMemoSharedEditQueryMemos
import MicroCFTA.SourceCurrentMemoClassPass

/-!
# Global receipts through memo-aware class passes

Every class captures the forest and completed merge table returned by its
tail. Its target slots start empty. Ordered edit receipts retain the same
three global tables through each reached force and native call. Final empty
propagation retains the exact returned native state and all memo tables.
-/
namespace MicroCFTA.SourceCurrentMemoClassPassMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditEffects SourceCurrentEditDomains
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedEditGraph SourceCurrentMemoClassPass
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentSubsumesQueryMemos (Effect)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Each class receipt retains the actual captured forest and completed merge table. -/
inductive ClassReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {record : SourceEqualityClassOrder.Record} → {values results : List (Value Symbol Guard)} →
    {before after : Native width Symbol Guard} → {memo saved : Memo Symbol Guard} →
    Class emptyGuard conjoin clear top record values before memo results after saved → Memos → Memos → Prop where
  | edit {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
      {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
      {before : Native width Symbol Guard} {memo : Memo Symbol Guard} {shared : SharedState width Symbol Guard}
      {actual : EditList emptyGuard conjoin clear top record values (SourceEqualityClassFoldGraph.edits record)
        values (initial before memo) results shared} {memos saved : Memos}
      (read : SourceCurrentMemoSharedEditQueryMemos.ListReads emptyGuard conjoin clear top record values actual memos saved) :
      ClassReads (.edit actual) memos saved

/-- The actual tail completes before the next class capture. -/
inductive FoldReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {records : List SourceEqualityClassOrder.Record} → {values results : List (Value Symbol Guard)} →
    {before after : Native width Symbol Guard} → {memo saved : Memo Symbol Guard} →
    Fold emptyGuard conjoin clear top records values before memo results after saved → Memos → Memos → Prop where
  | nil : FoldReads .nil memos memos
  | cons (tail : FoldReads actualTail memos middle) (head : ClassReads actualHead middle saved) :
      FoldReads (.cons actualTail actualHead) memos saved

/-- Literal final propagation retains the completed fold's global bundle. -/
inductive PassReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {records : List SourceEqualityClassOrder.Record} → {values results : List (Value Symbol Guard)} →
    {before after : Native width Symbol Guard} → {memo saved : Memo Symbol Guard} →
    Pass emptyGuard conjoin clear top records values before memo results after saved → Memos → Memos → Prop where
  | done (fold : FoldReads actual memos saved) : PassReads (.done actual) memos saved

private theorem compiled_safe (pairs : List (SourceEqualityEdits.Path × Action))
    (disjoint : pairs.Pairwise (fun first second => SourceEqualityEditCompiledPaths.Disjoint first.1 second.1))
    (values : List (Value Symbol Guard))
    (domains : ∀ path action, (path, action) ∈ pairs → ForestClosed path values)
    (entries : List (Int × Edits Action)) (compiled : build pairs = .editBelow entries) : ChildrenSafe entries 0 values := by
  intro query child found value selected path action retained
  have member : (Int.ofNat query :: path, action) ∈ leaves (build pairs) := by
    rw [compiled]
    exact below_member _ _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) _ _ retained
  have original := (SourceEqualityEditCompiledPaths.build_leaves pairs disjoint).mem_iff.mp member
  exact domains (Int.ofNat query :: path) action original value
    (by simpa only [SourceCurrentEditDomains.select_natural] using selected)

/-- Actual class edits derive their global receipts from selected original path domains. -/
theorem class_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Class emptyGuard conjoin clear top record values before memo results after saved)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (stored : Stored before.machine.heap memo) (available : Values before.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, ClassReads actual memos final ∧ Effect before.machine.heap after.machine.heap memos final := by
  have supported := SourceEqualityClassEdits.coherent_supported record coherent
  have disjoint := SourceEqualityClassEdits.edits_disjoint record.paths supported id
  have originalDomains : ∀ path action, (path, action) ∈ SourceEqualityClassEdits.edits record.paths id → ForestClosed path values := by
    intro path action member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact domains original included
  obtain ⟨finalReady, _, _, kept, _⟩ := SourceCurrentMemoClassPass.class_effects
    emptyGuard conjoin clear top actual coherent active ready costs stored available domains
  cases actual with
  | edit actual =>
      have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before memo ready
        (pure_keeps _ ready.semantic.ready) costs stored
      obtain ⟨final, reads, finalValid, finalCosts, retained, query⟩ :=
        SourceCurrentMemoSharedEditQueryMemos.list_memos record values before.machine.heap available domains actual
          (build_populated (SourceEqualityClassEdits.edits record.paths id)) (SourceEqualitySharedClassEdits.compiled_allowed record)
          initialReady available (fun entries compiled => compiled_safe _ disjoint values originalDomains entries compiled) costs memos valid
      exact ⟨final, .edit reads, kept, finalReady.semantic, finalCosts, finalValid, retained, query⟩

/-- Every actual right fold derives ordered global reads at its reached capture states. -/
theorem fold_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Fold emptyGuard conjoin clear top records values before memo results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (stored : Stored before.machine.heap memo) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, FoldReads actual memos final ∧ Effect before.machine.heap after.machine.heap memos final := by
  induction actual generalizing memos with
  | nil => exact ⟨memos, .nil, pure_keeps _ ready.semantic.ready, ready.semantic, costs, valid, extends_refl _, rfl⟩
  | cons tail head ih =>
      have tailCoherent := fun record member => coherent record (List.mem_cons_of_mem _ member)
      have tailActive := fun record member => active record (List.mem_cons_of_mem _ member)
      have tailDomains := fun record member => domains record (List.mem_cons_of_mem _ member)
      obtain ⟨middle, tailReads, tailEffect⟩ := ih tailCoherent tailActive ready costs stored available tailDomains memos valid
      obtain ⟨tailReady, _, tailStored, _, tailAvailable, transported, _⟩ :=
        SourceCurrentMemoClassPass.fold_effects emptyGuard conjoin clear top tail tailCoherent tailActive ready costs stored available tailDomains
      obtain ⟨final, headReads, headEffect⟩ := class_memos head (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
        tailReady tailEffect.costs tailStored tailAvailable
        (fun path member => transported _ (domains _ List.mem_cons_self path member)) middle tailEffect.valid
      exact ⟨final, .cons tailReads headReads, SourceCurrentMemoMergeQueryMemos.effect_trans tailEffect headEffect⟩

/-- A complete actual pass derives coherent final global tables without a future premise. -/
theorem pass_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Pass emptyGuard conjoin clear top records values before memo results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (stored : Stored before.machine.heap memo) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, PassReads actual memos final ∧ Effect before.machine.heap after.machine.heap memos final := by
  cases actual with
  | done fold =>
      obtain ⟨final, reads, effect⟩ := fold_memos fold coherent active ready costs stored available domains memos valid
      exact ⟨final, .done reads, effect⟩

end MicroCFTA.SourceCurrentMemoClassPassMemos
