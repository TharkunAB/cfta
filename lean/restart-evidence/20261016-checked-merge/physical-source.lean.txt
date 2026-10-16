import MicroCFTA.SourceCurrentAllocatedMergeGraph
import MicroCFTA.SourceCurrentMemoMergeCompletion
import MicroCFTA.SourceCurrentMemoMergeFieldHeap
import MicroCFTA.SourceCurrentConjunctionFieldAllocation

/-!
# Physical effects of allocated completed merge calls

Each large row allocates its empty equality field at its actual constructor
step. Other rows retain their original available fields. Recursive calls
derive these checks by mutual induction. Completion uses the finite
heap-only call and its exact allocated lift. This is a completed sequential
graph. Lazy publication, pending thunks, and runtime forcing stay separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergePhysical
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedMergeGraph
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionEquality (FieldAvailable Fields)
open SourceCurrentMemoMergeEffects (Stored Contract)
open SourceEqualityAnnotationHeap (SafeWork)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "State" => SourceCurrentAllocatedMergeGraph.State
namespace Old
export SourceCurrentMemoMergeGraph (remember winner_found)
export SourceCurrentMemoMergeEffects (Certified body_certified hit_original stored_remember)
end Old

/-- Raw constructor work checks its actual field; a large Top row allocates its own field. -/
def SafeCode (operations : SourceEqualityConstraintMemoAllocation.State) : Code Output → Prop
  | .pure _ => True
  | .work job => SafeWork (FieldAvailable operations) job
  | .topRow _ _ => True
  | .select _ => True
  | .request _ => True
  | .bind first next => SafeCode operations first ∧ ∀ value, SafeCode operations (next value)

private theorem work_grows {before after : SourceEqualityConstraintMemoAllocation.State}
    (growth : SourceEqualityConstraintMemoAllocation.Grows before after)
    (job : Work Symbol Guard Output) (safe : SafeWork (FieldAvailable before) job) :
    SafeWork (FieldAvailable after) job := by
  induction job with
  | pure => trivial
  | edge key identify next ih => exact ⟨safe.1.grows growth, fun value => ih value (safe.2 value)⟩
  | node key identify next ih => exact fun value => ih value (safe value)

/-- Equality-cache growth retains each original constructor field check. -/
theorem SafeCode.grows {before after : SourceEqualityConstraintMemoAllocation.State}
    (growth : SourceEqualityConstraintMemoAllocation.Grows before after)
    (code : Code Output) (safe : SafeCode before code) : SafeCode after code := by
  induction code with
  | pure | topRow | select | request => trivial
  | work job => exact work_grows growth job safe
  | bind first next ihFirst ihNext => exact ⟨ihFirst safe.1, fun value => ihNext value (safe.2 value)⟩

/-- Ordered code traversal retains the checks of its literal child instructions. -/
theorem map_safe (operations : SourceEqualityConstraintMemoAllocation.State)
    (call : Input → Code Output) (inputs : List Input)
    (safe : ∀ input ∈ inputs, SafeCode operations (call input)) :
    SafeCode operations (SourceCurrentAllocatedMergeGraph.map call inputs) := by
  induction inputs with
  | nil => trivial
  | cons input inputs ih =>
      exact ⟨safe input List.mem_cons_self,
        fun _ => ⟨ih (fun value member => safe value (List.mem_cons_of_mem _ member)), fun _ => trivial⟩⟩

private theorem retained_safe (operations : SourceEqualityConstraintMemoAllocation.State)
    (inputs : List (Value Symbol Guard)) : SafeCode operations (retainedColumn inputs) := by
  have branches (values : List (Value Symbol Guard)) : SafeCode operations
      (if values.any MergedOrdinaryHeight.recursiveBoundary then Code.work (makeUnion values)
        else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) := by
    split
    · exact SourceEqualityAnnotationHeap.makeUnion _ values
    · exact ⟨SourceEqualityAnnotationHeap.makeNode _ _, fun _ => trivial⟩
  cases inputs with
  | nil => exact branches []
  | cons first rest =>
      cases rest with
      | nil => trivial
      | cons second rest => exact branches (first :: second :: rest)

private theorem small_safe (operations : SourceEqualityConstraintMemoAllocation.State)
    (edge : EdgeValue Symbol Guard) (valid : FieldAvailable operations edge.entry.key.constraint) :
    SafeCode operations (small edge) :=
  ⟨map_safe operations Code.request edge.children (fun _ _ => trivial),
    fun children => SourceEqualityAnnotationHeap.makeEdge _ _ _ children valid⟩

private theorem column_safe (operations : SourceEqualityConstraintMemoAllocation.State)
    (inputs : List (Value Symbol Guard)) : SafeCode operations (column inputs) :=
  ⟨trivial, retained_safe operations⟩

private theorem large_safe (operations : SourceEqualityConstraintMemoAllocation.State)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    SafeCode operations (large first rest) :=
  ⟨map_safe operations column _ (fun values _ => column_safe operations values), fun _ => trivial⟩

private theorem group_safe (operations : SourceEqualityConstraintMemoAllocation.State)
    (edges : List (EdgeValue Symbol Guard))
    (valid : ∀ edge ∈ edges, FieldAvailable operations edge.entry.key.constraint) :
    SafeCode operations (group edges) := by
  unfold group
  split
  · exact map_safe operations small edges (fun edge member => small_safe operations edge (valid edge member))
  · cases edges with
    | nil => trivial
    | cons first rest => exact ⟨large_safe operations first rest, fun _ => trivial⟩

private theorem root_safe (operations : SourceEqualityConstraintMemoAllocation.State)
    (groups : List (List (EdgeValue Symbol Guard)))
    (valid : ∀ group ∈ groups, ∀ edge ∈ group, FieldAvailable operations edge.entry.key.constraint) :
    SafeCode operations (root groups) :=
  ⟨map_safe operations group groups (fun edges member => group_safe operations edges (valid edges member)),
    fun rows => SourceEqualityAnnotationHeap.makeNode _ rows.flatten⟩

/-- Initial residency derives every original field check without an initial Top assumption. -/
theorem body_safe [DecidableEq Symbol] (input : Value Symbol Guard) (before : State)
    (ready : Ready before) (available : Available before.heap input) :
    SafeCode before.equality (body input) := by
  cases input with
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have resident := InternedEdgeResidency.resident_edges before.heap
          ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
        have grouping := MergedSourceGrouping.groups_correct edges
        apply root_safe before.equality
        intro chosen member edge included
        have original : edge ∈ edges :=
          grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨chosen, member, included⟩)
        exact ready.fields edge.entry.key edge (resident edge original)
      · simp only [body, closed, ite_false, SafeCode]
  | empty | reference | union | mu => trivial

private theorem oldEffect {before after : State} (effects : Effects before after) :
    SourceCurrentMemoMergeEffects.Effect before.heap after.heap :=
  ⟨effects.keeps, effects.ready.semantic, effects.ready.costs⟩

/-- Actual instruction and request induction derives all reached physical field checks. -/
theorem Run.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {code : Code Output}
    {before after : State} {memo saved : Memo} {output : Output}
    (actual : Run clear code before memo output after saved) :
    ∀ (post : InternedConstructorTemplates.State Symbol Guard → Output → Prop),
      Ready before → Stored before.heap memo →
      Old.Certified Contract clear (erase code) before.heap post → SafeCode before.equality code →
      Effects before after ∧ Stored after.heap saved ∧ post after.heap output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ => Ready before → Stored before.heap memo →
        Available before.heap input → Effects before after ∧ Stored after.heap saved ∧ Contract input before.heap output after.heap) with
  | pure value state memo =>
      intro post ready stored checked _
      exact ⟨Effects.refl _ ready, stored, checked⟩
  | work job state memo =>
      intro post ready stored checked safe
      exact ⟨⟨checked.1.keeps, ⟨checked.1.semantic, checked.1.costs, ready.valid,
        SourceEqualityAnnotationHeap.run _ job safe state.heap ready.fields⟩,
        SourceEqualityConstraintMemoAllocation.grows_refl _⟩, stored.grows checked.1.keeps, checked.2⟩
  | topRow symbol children state memo =>
      intro post ready stored checked _
      obtain ⟨valid, growth, field⟩ := SourceCurrentConjunctionFieldAllocation.empty_field state.equality ready.valid
      have fields := ready.fields.grows growth
      have finalFields := SourceEqualityAnnotationHeap.run _ (makeEdge symbol top children)
        (SourceEqualityAnnotationHeap.makeEdge _ symbol top children field) state.heap fields
      exact ⟨⟨checked.1.keeps, ⟨checked.1.semantic, checked.1.costs, valid, finalFields⟩, growth⟩,
        stored.grows checked.1.keeps, checked.2⟩
  | select fuel done =>
      rename_i inputs values heap state current
      intro post ready stored checked _
      have own := SourceCurrentMergedHeapEffects.select_effect (FieldAvailable state.equality) _ fuel _ _
        ready.semantic ready.costs checked.1 _ _ done
      have effect : SourceCurrentMemoMergeEffects.Effect _ _ := ⟨own.keeps, own.semantic, own.costs⟩
      exact ⟨⟨own.keeps, ⟨own.semantic, own.costs, ready.valid, own.annotations ready.fields⟩,
        SourceEqualityConstraintMemoAllocation.grows_refl _⟩, stored.grows own.keeps,
        checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post ready stored checked _
      obtain ⟨effect, retained, returned⟩ := ih ready stored checked.1
      exact ⟨effect, retained, checked.2 _ _ (oldEffect effect) returned⟩
  | bind first later ihFirst ihLater =>
      intro post ready stored checked safe
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstStored, valid⟩ := ihFirst intermediate ready stored firstChecked safe.1
      obtain ⟨laterEffect, laterStored, returned⟩ := ihLater post firstEffect.ready firstStored
        (nextChecked _ _ (oldEffect firstEffect) valid) (SafeCode.grows firstEffect.grows _ (safe.2 _))
      exact ⟨firstEffect.trans laterEffect, laterStored, returned⟩
  | hit found =>
      rename_i ready stored available
      obtain ⟨_, result, closed⟩ := Old.hit_original ready.semantic available stored found
      exact ⟨Effects.refl _ ready, stored, result, closed⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i ready stored available
      obtain ⟨effect, retained, result, closed⟩ := ih _ ready stored
        (by simpa only [erase_body] using Old.body_certified clear top input before.heap ready.semantic ready.costs available)
        (body_safe input before ready available)
      have inputAvailable := effect.keeps.available input available
      have completed := Old.stored_remember retained input candidate inputAvailable result closed
      obtain ⟨_, winnerAvailable, winnerClosed⟩ :=
        Old.hit_original effect.ready.semantic inputAvailable completed (Old.winner_found current input candidate)
      exact ⟨effect, completed, winnerAvailable, winnerClosed⟩

/-- Completed hits and allocated misses retain the actual operation state and result records. -/
theorem _root_.MicroCFTA.SourceCurrentAllocatedMergeGraph.Call.verified
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : State} {memo saved : Memo}
    (actual : Call clear input before memo output after saved)
    (ready : Ready before) (stored : Stored before.heap memo) (available : Available before.heap input) :
    Effects before after ∧ Stored after.heap saved ∧ Available after.heap output ∧
      (input.free = [] → output.free = []) :=
  Run.verified (.request actual) (fun after output => Contract input before.heap output after)
    ready stored ⟨available, fun _ _ _ returned => returned⟩ trivial

/-- Actual allocated instructions retain every earlier completed merge entry. -/
theorem _root_.MicroCFTA.SourceCurrentAllocatedMergeGraph.Run.extends
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {code : Code Output} {before after : State} {memo saved : Memo} {output : Output}
    (actual : Run clear code before memo output after saved) : Extends memo saved :=
  actual.graph.extends

/-- A completed allocated call retains every earlier completed merge entry. -/
theorem _root_.MicroCFTA.SourceCurrentAllocatedMergeGraph.Call.extends
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State} {memo saved : Memo}
    (actual : Call clear input before memo output after saved) : Extends memo saved :=
  actual.graph.extends

/-- Finite heap-only completion lifts to an actual allocated call with derived returned invariants. -/
theorem call_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (input : Value Symbol Guard) (before : State) (memo : Memo)
    (ready : Ready before) (stored : Stored before.heap memo) (available : Available before.heap input) :
    ∃ output after saved, Call clear input before memo output after saved ∧ Effects before after ∧
      Stored after.heap saved ∧ Available after.heap output ∧ (input.free = [] → output.free = []) := by
  obtain ⟨output, heap, saved, actual, _⟩ := SourceCurrentMemoMergeCompletion.call_complete
    clear top input before.heap memo ready.semantic ready.costs stored available
  obtain ⟨operations, lifted⟩ := call_lift actual before.equality
  have checked := lifted.verified ready stored available
  exact ⟨output, ⟨heap, operations⟩, saved, lifted, checked⟩

end MicroCFTA.SourceCurrentAllocatedMergePhysical
