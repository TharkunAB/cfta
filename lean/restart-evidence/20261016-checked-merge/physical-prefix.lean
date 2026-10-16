import MicroCFTA.SourceCurrentMemoMergeGraph
import MicroCFTA.SourceCurrentConjunctionRowsAllocation
import MicroCFTA.SourceEqualityMkEdgeAllocation
import MicroCFTA.SourceCurrentMemoMergeCompletion
import MicroCFTA.SourceCurrentMemoMergeFieldHeap
import MicroCFTA.SourceCurrentConjunctionFieldAllocation

/-!
# Completed merge calls with actual Top-field allocation

Large rows intern the canonical empty equality field before their raw edge
request. Small rows retain their stored field. Completed hits skip the body.
Erasure retains the constructor heap, the result, and the merge memo.
This graph uses the existing column-first completed serial schedule.
It does not establish GHC forcing order or pending memo publication.
The comparison predicate remains an explicit parameter.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergeGraph
open Cache InternedConstructorTemplates
open MergedOrdinaryHeight (recursiveBoundary ordinaryUnion)
namespace Old
export SourceCurrentMemoMergeGraph (Entry Memo remember winner)
end Old
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
abbrev State := SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
abbrev Memo := Old.Memo Symbol Guard
abbrev top : Guard := SourceEqualityConstraintConstructors.top

/-- Instructions distinguish direct Top construction from unchanged raw work. -/
inductive Code : Type → Type 1 where
  | pure (value : Result) : Code Result
  | work (job : Work Symbol Guard Result) : Code Result
  | topRow (symbol : Symbol) (children : List (Value Symbol Guard)) : Code (EdgeValue Symbol Guard)
  | select (inputs : List (Value Symbol Guard)) : Code (List (Value Symbol Guard))
  | request (input : Value Symbol Guard) : Code (Value Symbol Guard)
  | bind (first : Code First) (next : First → Code Result) : Code Result

/-- Ordered maps retain each returned physical state and merge memo. -/
def map (call : Input → Code Output) : List Input → Code (List Output)
  | [] => .pure []
  | first :: rest => .bind (call first) fun value => .bind (map call rest) fun values => .pure (value :: values)

/-- Singleton and recursive-boundary branches retain the original column logic. -/
def retainedColumn (retained : List (Value Symbol Guard)) : Code (Value Symbol Guard) :=
  match retained with
  | [single] => .pure single
  | others => if others.any recursiveBoundary then .work (makeUnion others)
    else .bind (.work (ordinaryUnion others)) Code.request

/-- Small rows retain their original complete field after recursive child calls. -/
def small (edge : EdgeValue Symbol Guard) : Code (EdgeValue Symbol Guard) :=
  .bind (map Code.request edge.children) fun children =>
    .work (makeEdge edge.entry.key.symbol edge.entry.key.constraint children)

/-- Actual selection precedes retained-column normalization. -/
def column (inputs : List (Value Symbol Guard)) : Code (Value Symbol Guard) :=
  .bind (.select inputs) retainedColumn

/-- The completed serial schedule allocates the Top field after its columns. -/
def large (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) : Code (EdgeValue Symbol Guard) :=
  .bind (map column
    (MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length))
    fun children => .topRow first.entry.key.symbol children

/-- The threshold retains at most four rows and merges larger groups. -/
def group (edges : List (EdgeValue Symbol Guard)) : Code (List (EdgeValue Symbol Guard)) :=
  if edges.length ≤ 4 then map small edges
  else match edges with
  | [] => .pure []
  | first :: rest => .bind (large first rest) fun edge => .pure [edge]

/-- Final node construction follows the actual ordered group results. -/
def root (groups : List (List (EdgeValue Symbol Guard))) : Code (Value Symbol Guard) :=
  .bind (map group groups) fun rows => .work (makeNode rows.flatten)

/-- Only closed ordinary inputs enter grouping. -/
def body [DecidableEq Symbol] (input : Value Symbol Guard) : Code (Value Symbol Guard) :=
  match input with
  | .node _ edges _ free => if free = [] then root (MergedSourceGrouping.groups edges) else .pure input
  | _ => .pure input

/-- Erasure removes only the separate equality allocation instruction. -/
def erase : Code Output → SourceCurrentMemoMergeGraph.Code Symbol Guard Output
  | .pure value => .pure value
  | .work job => .work job
  | .topRow symbol children => .work (makeEdge symbol top children)
  | .select inputs => .select inputs
  | .request input => .request input
  | .bind first next => .bind (erase first) (fun value => erase (next value))

theorem erase_map (call : Input → Code Output) (inputs : List Input) :
    erase (map call inputs) = SourceCurrentMemoMergeGraph.map (fun input => erase (call input)) inputs := by
  induction inputs with
  | nil => rfl
  | cons first rest ih => simp only [map, erase, ih, SourceCurrentMemoMergeGraph.map]

theorem erase_retainedColumn (inputs : List (Value Symbol Guard)) :
    erase (retainedColumn inputs) = SourceCurrentMemoMergeGraph.retainedColumn inputs := by
  cases inputs with
  | nil => simp only [retainedColumn, SourceCurrentMemoMergeGraph.retainedColumn]; split <;> rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => simp only [retainedColumn, SourceCurrentMemoMergeGraph.retainedColumn]; split <;> rfl

theorem erase_small (edge : EdgeValue Symbol Guard) : erase (small edge) = SourceCurrentMemoMergeGraph.small edge := by
  simp only [small, erase, erase_map, SourceCurrentMemoMergeGraph.small]

theorem erase_column (inputs : List (Value Symbol Guard)) : erase (column inputs) = SourceCurrentMemoMergeGraph.column inputs := by
  simp only [column, erase, erase_retainedColumn, SourceCurrentMemoMergeGraph.column]

theorem erase_large (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    erase (large first rest) = SourceCurrentMemoMergeGraph.large top first rest := by
  simp only [large, erase, erase_map, erase_column, SourceCurrentMemoMergeGraph.large]

theorem erase_group (edges : List (EdgeValue Symbol Guard)) :
    erase (group edges) = SourceCurrentMemoMergeGraph.group top edges := by
  unfold group SourceCurrentMemoMergeGraph.group
  split
  · simp only [erase_map, erase_small]
  · cases edges with
    | nil => rfl
    | cons first rest => simp only [erase, erase_large]

theorem erase_root (groups : List (List (EdgeValue Symbol Guard))) :
    erase (root groups) = SourceCurrentMemoMergeGraph.root top groups := by
  simp only [root, erase, erase_map, erase_group, SourceCurrentMemoMergeGraph.root]

theorem erase_body [DecidableEq Symbol] (input : Value Symbol Guard) :
    erase (body input) = SourceCurrentMemoMergeGraph.body top input := by
  cases input <;> simp only [body, SourceCurrentMemoMergeGraph.body, erase]
  split <;> simp only [erase_root, erase]

mutual
  /-- Actual instructions retain the complete constructor and equality states. -/
  inductive Run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) :
      {Output : Type} → Code Output → State → Memo → Output → State → Memo → Prop where
    | pure (value : Output) (state : State) (memo : Memo) : Run clear (.pure value) state memo value state memo
    | work (job : Work Symbol Guard Output) (state : State) (memo : Memo) :
        Run clear (.work job) state memo (run job state.heap).1 ⟨(run job state.heap).2, state.equality⟩ memo
    | topRow (symbol : Symbol) (children : List (Value Symbol Guard)) (state : State) (memo : Memo) :
        Run clear (.topRow symbol children) state memo (run (makeEdge symbol top children) state.heap).1
          ⟨(run (makeEdge symbol top children) state.heap).2, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩ memo
    | select (fuel : Nat) (done : SourceMergedSelection.select clear fuel inputs before.heap = .done values heap) :
        Run clear (.select inputs) before memo values ⟨heap, before.equality⟩ memo
    | request (actual : Call clear input before memo output after saved) :
        Run clear (.request input) before memo output after saved
    | bind (first : Run clear code before memo value middle current)
        (later : Run clear (next value) middle current output after saved) :
        Run clear (.bind code next) before memo output after saved

  /-- Completed hits are unchanged. Misses run the allocated body and reread the winner. -/
  inductive Call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) :
      Value Symbol Guard → State → Memo → Value Symbol Guard → State → Memo → Prop where
    | hit (found : memo input.referenceOf = some entry) : Call clear input before memo entry.result before memo
    | miss (absent : memo input.referenceOf = none) (actual : Run clear (body input) before memo candidate after current) :
        Call clear input before memo (Old.winner current input candidate).result after (Old.remember current input candidate)
end

/-- Erasure preserves the exact old heap graph, result, and completed memo. -/
theorem Run.graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {code : Code Output} {before after : State} {memo saved : Memo} {output : Output}
    (actual : Run clear code before memo output after saved) :
    SourceCurrentMemoMergeGraph.Run clear top (erase code) before.heap memo output after.heap saved := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SourceCurrentMemoMergeGraph.Call clear top input before.heap memo output after.heap saved) with
  | pure => exact .pure _ _ _
  | work => exact .work _ _ _
  | topRow => exact .work _ _ _
  | select fuel done => exact .select fuel done
  | request _ ih => exact .request ih
  | bind _ _ first later => exact .bind first later
  | hit found => exact .hit found
  | miss absent _ ih => exact .miss absent (by simpa only [erase_body] using ih)

/-- Every allocated completed call has the same old completed call. -/
theorem Call.graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State} {memo saved : Memo}
    (actual : Call clear input before memo output after saved) :
    SourceCurrentMemoMergeGraph.Call clear top input before.heap memo output after.heap saved := by
  exact SourceCurrentMemoMergeGraph.Run.request_iff.mp (Run.graph (.request actual))


end MicroCFTA.SourceCurrentAllocatedMergeGraph

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
theorem Call.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : State} {memo saved : Memo}
    (actual : Call clear input before memo output after saved)
    (ready : Ready before) (stored : Stored before.heap memo) (available : Available before.heap input) :
    Effects before after ∧ Stored after.heap saved ∧ Available after.heap output ∧
      (input.free = [] → output.free = []) :=
  Run.verified (.request actual) (fun after output => Contract input before.heap output after)
    ready stored ⟨available, fun _ _ _ returned => returned⟩ trivial


end MicroCFTA.SourceCurrentAllocatedMergePhysical
