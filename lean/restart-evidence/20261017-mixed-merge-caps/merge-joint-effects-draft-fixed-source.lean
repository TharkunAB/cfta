import MicroCFTA.SourceCurrentConstrainedCapMergeGuardEffects
import MicroCFTA.SourceCurrentAllocatedMerge
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointRebase

/-!
# Actual Merge effects on joint checked query invariants

The instruction proof derives guard-heap retention through actual comparison
and source constructor work. The full checked adapter keeps the native
memo cells, their captured origins, and the fixed semantic inventory.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMergeJointEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
open SourceCurrentConstrainedCapGuardHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private def Safe : Code Symbol Guard Output → Prop
  | .pure _ => True
  | .work job => ∀ state, InternedShallowHeap.NoNewMu state (run job state).2
  | .select _ | .request _ => True
  | .bind first next => Safe first ∧ ∀ value, Safe (next value)

private theorem map_safe (call : Input → Code Symbol Guard Output) (inputs : List Input)
    (safe : ∀ input ∈ inputs, Safe (call input)) : Safe (SourceCurrentMemoMergeGraph.map call inputs) := by
  induction inputs with
  | nil => trivial
  | cons input inputs ih =>
      exact ⟨safe input List.mem_cons_self,
        fun _ => ⟨ih (fun value member => safe value (List.mem_cons_of_mem _ member)), fun _ => trivial⟩⟩

private theorem edge_safe (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) :
    Safe (.work (makeEdge symbol guard values)) := by
  intro state key entry body depth ordinary present
  exact present

private theorem retained_safe (inputs : List (Value Symbol Guard)) : Safe (retainedColumn inputs) := by
  have branches (values : List (Value Symbol Guard)) : Safe
      (if values.any MergedOrdinaryHeight.recursiveBoundary then Code.work (makeUnion values)
        else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) := by
    split
    · exact fun state => InternedShallowHeap.makeUnion_noNewMu values state
    · exact ⟨fun state => InternedShallowHeap.makeNode_noNewMu _ state, fun _ => trivial⟩
  cases inputs with
  | nil => exact branches []
  | cons first rest =>
      cases rest with
      | nil => trivial
      | cons second rest => exact branches (first :: second :: rest)

private theorem small_safe (edge : EdgeValue Symbol Guard) : Safe (small edge) :=
  ⟨map_safe Code.request edge.children (fun _ _ => trivial), fun children => edge_safe _ _ children⟩

private theorem column_safe (inputs : List (Value Symbol Guard)) : Safe (column inputs) :=
  ⟨trivial, retained_safe⟩

private theorem large_safe (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    Safe (large top first rest) :=
  ⟨map_safe column _ (fun values _ => column_safe values), fun children => edge_safe _ _ children⟩

private theorem group_safe (top : Guard) (edges : List (EdgeValue Symbol Guard)) : Safe (group top edges) := by
  unfold group
  split
  · exact map_safe small edges (fun edge _ => small_safe edge)
  · cases edges with
    | nil => trivial
    | cons first rest => exact ⟨large_safe top first rest, fun _ => trivial⟩

private theorem root_safe (top : Guard) (groups : List (List (EdgeValue Symbol Guard))) : Safe (root top groups) :=
  ⟨map_safe (group top) groups (fun edges _ => group_safe top edges),
    fun rows state => InternedShallowHeap.makeNode_noNewMu rows.flatten state⟩

private theorem body_safe [DecidableEq Symbol] (top : Guard) (input : Value Symbol Guard) : Safe (body top input) := by
  cases input with
  | node entry edges depth free =>
      unfold body
      split
      · exact root_safe top _
      · trivial
  | empty | reference | union | mu => trivial

private theorem run_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {clear : Guard → Bool} {top : Guard}
    {code : Code Symbol Guard Output} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before → Stored before memo →
      Certified Contract clear code before post → Safe code → Heap annotation before →
        Effect before after ∧ Stored after saved ∧ post after output ∧ Heap annotation after := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ => SemanticReady before → CostHeap before →
        Stored before memo → Available before input → Heap annotation before →
          Effect before after ∧ Stored after saved ∧ Contract input before output after ∧ Heap annotation after) with
  | pure value state memo =>
      intro post semantic costs stored checked _ guards
      exact ⟨effect_refl _ semantic costs, stored, checked, guards⟩
  | work job state memo =>
      intro post semantic costs stored checked safe guards
      exact ⟨checked.1, stored.grows checked.1.keeps, checked.2,
        SourceCurrentConstrainedCapGuardHeap.preserve annotation state _ guards (safe state)⟩
  | select fuel done =>
      intro post semantic costs stored checked _ guards
      have actual := SourceCurrentConstrainedCapMergeGuardEffects.select_effect annotation _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨actual.keeps, actual.semantic, actual.costs⟩
      exact ⟨effect, stored.grows effect.keeps, checked.2.2 fuel _ _ done effect, actual.guards guards⟩
  | request actual ih =>
      intro post semantic costs stored checked _ guards
      obtain ⟨effect, retained, returned, afterGuards⟩ := ih semantic costs stored checked.1 guards
      exact ⟨effect, retained, checked.2 _ _ effect returned, afterGuards⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored checked safe guards
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstStored, valid, middleGuards⟩ :=
        ihFirst intermediate semantic costs stored firstChecked safe.1 guards
      obtain ⟨laterEffect, laterStored, returned, afterGuards⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstStored
          (nextChecked _ _ firstEffect valid) (safe.2 _) middleGuards
      exact ⟨firstEffect.trans laterEffect, laterStored, returned, afterGuards⟩
  | hit found =>
      rename_i semantic costs stored available guards
      obtain ⟨_, result, closed⟩ := hit_original semantic available stored found
      exact ⟨effect_refl _ semantic costs, stored, ⟨result, closed⟩, guards⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs stored available guards
      obtain ⟨effect, retained, result, afterGuards⟩ := ih _ semantic costs stored
        (body_certified _ _ input before semantic costs available) (body_safe _ input) guards
      have inputAvailable := effect.keeps.available input available
      have completed := stored_remember retained input candidate inputAvailable result.1 result.2
      obtain ⟨_, winnerAvailable, winnerClosed⟩ := hit_original effect.semantic inputAvailable completed
        (winner_found current input candidate)
      exact ⟨effect, completed, ⟨winnerAvailable, winnerClosed⟩, afterGuards⟩

/-- The actual memo-aware Merge call retains its causal guard heap through every comparison. -/
theorem call_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {clear : Guard → Bool} {top : Guard}
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Stored before memo) (available : Available before input)
    (guards : Heap annotation before) : Heap annotation after :=
  (run_heap annotation (.request actual) (fun after output => Contract input before output after)
    semantic costs stored ⟨available, fun _ _ _ returned => returned⟩ trivial guards).2.2.2

section Checked
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical advance_extension)
open SourceCurrentConstrainedCapKernelJoint (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Joint" => SourceCurrentConstrainedCapCheckedJointCache.Stored
local notation "Origins" => SourceCurrentConstrainedCapCheckedJointOrigins.Stored
variable {width : Nat}

/-- Actual physical advancement retains fixed-source laws once its local producer supplies the guard heap. -/
theorem advance (annotation : Guard → Prop) (source : State Symbol Guard)
    (before : Checked width) (after : Physical) (context : Context annotation source before.native.machine)
    (stored : Joint annotation source before.native) (origins : Origins source before.native)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) after)
    (guards : Heap annotation after.heap) :
    Context annotation source (advancePhysical before after).native.machine ∧
      Joint annotation source (advancePhysical before after).native ∧
      Origins source (advancePhysical before after).native := by
  have extension := advance_extension before after effects
  refine ⟨context.after ⟨effects.ready.semantic.ready.semantic.1.normal.facts, context.valid.2⟩
    effects.ready.semantic.ready.semantic guards extension, ?_, ?_⟩
  · exact SourceCurrentConstrainedCapCheckedJointCache.advance_stored annotation source before.native _ stored
  · exact SourceCurrentConstrainedCapCheckedJointOrigins.advance_stored source before.native _ origins

/-- The SAME actual allocated Merge retains joint laws, origins, and its old semantic inventory. -/
theorem merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : Checked width}
    {memo saved : Memo Symbol Guard}
    (actual : SourceCurrentAllocatedMerge.Merge clear input before memo output after saved)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (physicalStored : Stored before.native.machine.heap memo) (available : Available before.native.machine.heap input)
    (context : Context annotation source before.native.machine)
    (stored : Joint annotation source before.native) (origins : Origins source before.native) :
    Context annotation source after.native.machine ∧ Joint annotation source after.native ∧
      Origins source after.native ∧ SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory after := by
  cases actual with
  | done actual =>
      have initial : SourceCurrentConjunctionRowsAllocation.Ready (physical before) :=
        ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩
      have effects := (actual.verified initial physicalStored available).1
      have guards := call_heap annotation actual.graph ready.semantic ready.costs physicalStored available context.guards
      have retained := advance annotation source before _ context stored origins effects guards
      exact ⟨retained.1, retained.2.1, retained.2.2, admitted.advance _ (advance_extension before _ effects)⟩

end Checked
end MicroCFTA.SourceCurrentConstrainedCapMergeJointEffects
