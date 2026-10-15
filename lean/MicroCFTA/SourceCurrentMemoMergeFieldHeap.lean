import MicroCFTA.SourceCurrentMemoMergeNative
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Physical annotations through completed memo-aware merge calls

Small rows retain their original guards. Large rows emit the checked Top
guard. Selection retains annotations through its actual heap effects.
Recursive requests discharge their annotation obligations by graph induction.
-/
namespace MicroCFTA.SourceCurrentMemoMergeFieldHeap
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
open SourceEqualityAnnotationHeap (Heap SafeWork)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Source instructions emit only checked raw edge annotations. Requests are checked by mutual induction. -/
def SafeCode (annotation : Guard → Prop) : Code Symbol Guard Output → Prop
  | .pure _ => True
  | .work job => SafeWork annotation job
  | .select _ => True
  | .request _ => True
  | .bind first next => SafeCode annotation first ∧ ∀ value, SafeCode annotation (next value)

/-- Ordered code maps retain each original instruction's annotation check. -/
theorem map_safe (annotation : Guard → Prop) (call : Input → Code Symbol Guard Output)
    (inputs : List Input) (safe : ∀ input ∈ inputs, SafeCode annotation (call input)) :
    SafeCode annotation (SourceCurrentMemoMergeGraph.map call inputs) := by
  induction inputs with
  | nil => trivial
  | cons input inputs ih =>
      exact ⟨safe input List.mem_cons_self, fun _ => ⟨ih (fun value member => safe value (List.mem_cons_of_mem _ member)), fun _ => trivial⟩⟩

/-- Retained-column normalization emits no edge guard in either constructor branch. -/
theorem retained_safe (annotation : Guard → Prop) (inputs : List (Value Symbol Guard)) :
    SafeCode annotation (retainedColumn inputs) := by
  have branches (values : List (Value Symbol Guard)) : SafeCode annotation
      (if values.any MergedOrdinaryHeight.recursiveBoundary then Code.work (makeUnion values)
        else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) := by
    split
    · exact SourceEqualityAnnotationHeap.makeUnion annotation values
    · exact ⟨SourceEqualityAnnotationHeap.makeNode annotation _, fun _ => trivial⟩
  cases inputs with
  | nil => exact branches []
  | cons first rest =>
      cases rest with
      | nil => trivial
      | cons second rest => exact branches (first :: second :: rest)

/-- Small rows emit only their original resident full guard. -/
theorem small_safe (annotation : Guard → Prop) (edge : EdgeValue Symbol Guard)
    (valid : annotation edge.entry.key.constraint) : SafeCode annotation (small edge) :=
  ⟨map_safe annotation Code.request edge.children (fun _ _ => trivial),
    fun values => SourceEqualityAnnotationHeap.makeEdge annotation _ _ values valid⟩

/-- Column selection adds no raw guard before retained normalization. -/
theorem column_safe (annotation : Guard → Prop) (inputs : List (Value Symbol Guard)) : SafeCode annotation (column inputs) :=
  ⟨trivial, retained_safe annotation⟩

/-- Large groups emit the checked source Top after their ordered columns. -/
theorem large_safe (annotation : Guard → Prop) (top : Guard) (topValid : annotation top)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) : SafeCode annotation (large top first rest) :=
  ⟨map_safe annotation column _ (fun values _ => column_safe annotation values),
    fun values => SourceEqualityAnnotationHeap.makeEdge annotation _ _ values topValid⟩

/-- Both source threshold branches emit only original or Top guards. -/
theorem group_safe (annotation : Guard → Prop) (top : Guard) (topValid : annotation top)
    (edges : List (EdgeValue Symbol Guard)) (valid : ∀ edge ∈ edges, annotation edge.entry.key.constraint) :
    SafeCode annotation (group top edges) := by
  unfold group
  split
  · exact map_safe annotation small edges (fun edge member => small_safe annotation edge (valid edge member))
  · cases edges with
    | nil => trivial
    | cons first rest => exact ⟨large_safe annotation top topValid first rest, fun _ => trivial⟩

/-- Final node construction adds no annotation after its actual original groups. -/
theorem root_safe (annotation : Guard → Prop) (top : Guard) (topValid : annotation top)
    (groups : List (List (EdgeValue Symbol Guard))) (valid : ∀ group ∈ groups, ∀ edge ∈ group, annotation edge.entry.key.constraint) :
    SafeCode annotation (root top groups) :=
  ⟨map_safe annotation (group top) groups (fun edges member => group_safe annotation top topValid edges (valid edges member)),
    fun rows => SourceEqualityAnnotationHeap.makeNode annotation rows.flatten⟩

/-- Actual input residency and the initial physical heap discharge every source body guard. -/
theorem body_safe [DecidableEq Symbol] (annotation : Guard → Prop) (top : Guard) (topValid : annotation top)
    (input : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before input) (fields : Heap annotation before) : SafeCode annotation (body top input) := by
  cases input with
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
        have grouping := MergedSourceGrouping.groups_correct edges
        apply root_safe annotation top topValid
        intro group member edge included
        have original : edge ∈ edges := grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
        exact fields edge.entry.key edge (resident edge original)
      · simp only [body, closed, ite_false, SafeCode]
  | empty | reference | union | mu => trivial

/-- Actual mutual instruction induction retains annotations without a recursive callback premise. -/
theorem run_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : annotation top)
    {code : Code Symbol Guard Output} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before → Stored before memo →
      Certified Contract clear code before post → SafeCode annotation code → Heap annotation before →
        Effect before after ∧ Stored after saved ∧ post after output ∧ Heap annotation after := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ => SemanticReady before → CostHeap before →
        Stored before memo → Available before input → Heap annotation before →
          Effect before after ∧ Stored after saved ∧ Contract input before output after ∧ Heap annotation after) with
  | pure value state memo =>
      intro post semantic costs stored checked _ fields
      exact ⟨effect_refl _ semantic costs, stored, checked, fields⟩
  | work job state memo =>
      intro post semantic costs stored checked safe fields
      exact ⟨checked.1, stored.grows checked.1.keeps, checked.2, SourceEqualityAnnotationHeap.run annotation job safe state fields⟩
  | select fuel done =>
      intro post semantic costs stored checked _ fields
      have original := SourceCurrentMergedHeapEffects.select_effect annotation _ fuel _ _ semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨effect, stored.grows effect.keeps, checked.2.2 fuel _ _ done effect, original.annotations fields⟩
  | request actual ih =>
      intro post semantic costs stored checked _ fields
      obtain ⟨effect, retained, returned, finalFields⟩ := ih semantic costs stored checked.1 fields
      exact ⟨effect, retained, checked.2 _ _ effect returned, finalFields⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored checked safe fields
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstStored, valid, middleFields⟩ := ihFirst intermediate semantic costs stored firstChecked safe.1 fields
      obtain ⟨laterEffect, laterStored, returned, finalFields⟩ := ihLater post firstEffect.semantic firstEffect.costs firstStored
        (nextChecked _ _ firstEffect valid) (safe.2 _) middleFields
      exact ⟨firstEffect.trans laterEffect, laterStored, returned, finalFields⟩
  | hit found =>
      rename_i semantic costs stored available fields
      obtain ⟨_, result, closed⟩ := hit_original semantic available stored found
      exact ⟨effect_refl _ semantic costs, stored, ⟨result, closed⟩, fields⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs stored available fields
      obtain ⟨effect, retained, result, finalFields⟩ := ih _ semantic costs stored
        (body_certified _ _ input before semantic costs available) (body_safe annotation top topValid input before semantic available fields) fields
      have inputAvailable := effect.keeps.available input available
      have completed := stored_remember retained input candidate inputAvailable result.1 result.2
      obtain ⟨_, winnerAvailable, winnerClosed⟩ := hit_original effect.semantic inputAvailable completed (winner_found current input candidate)
      exact ⟨effect, completed, ⟨winnerAvailable, winnerClosed⟩, finalFields⟩

/-- Completed hits skip all work; misses derive their own actual body annotation checks. -/
theorem call_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : annotation top)
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Stored before memo) (available : Available before input)
    (fields : Heap annotation before) : Heap annotation after :=
  (run_heap annotation topValid (.request actual) (fun after output => Contract input before output after)
    semantic costs stored ⟨available, fun _ _ _ returned => returned⟩ trivial fields).2.2.2

/-- The same completed call retains annotations when embedded in the full native state. -/
theorem native_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (topValid : annotation top) {input output : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : SourceCurrentMemoMergeNative.Merge clear top input before memo output after saved)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo) (available : Available before.machine.heap input)
    (fields : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases actual with
  | done call => exact call_heap annotation topValid call ready.semantic costs stored available fields

end MicroCFTA.SourceCurrentMemoMergeFieldHeap
