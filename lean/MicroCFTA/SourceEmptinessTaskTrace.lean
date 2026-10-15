import MicroCFTA.SourceEmptinessTaskRows
import MicroCFTA.SourceEmptinessTaskFields
import MicroCFTA.SourceDelayedEmptinessInventory
import MicroCFTA.SourceEqualityNativeInitial

/-!
# Final resident records and completed task rows from source exploration

The reached worklist uses actual closed-domain forces and source row reads.
Local effects derive final resident records and stable shared task results.
Every new stored row has complete task readout at the final heap. This is
not a proof that arbitrary native calls or whole source exploration finish.
Exposure leaves use complete row reads. Exact Haskell row-spine demand and
evaluation of original child thunks remain separate source transfers.
-/
namespace MicroCFTA.SourceEmptinessTaskTrace
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache
open SourceEmptinessTasks SourceEmptinessTaskRows
open DelayedEmptinessExplore
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "TaskState" => SourceEmptinessTasks.State
local notation "Task" => SourceEmptinessTasks.Task Symbol Guard
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard

/-- The source item uses the untagged identity and the actual cached free list. -/
def encode (value : Value) : ConservativeEmptinessExplore.Item :=
  match SourceEmptinessKeys.key value with
  | none => .empty
  | some identity => .resident identity value.free.isEmpty

/-- Every resident encoded item has the exact stored untagged key. -/
theorem encode_key (value : Value) (identity : Int) (closed : Bool)
    (encoded : encode value = .resident identity closed) : SourceEmptinessKeys.key value = some identity := by
  cases found : SourceEmptinessKeys.key value with
  | none => simp only [encode, found] at encoded; cases encoded
  | some actual =>
      have same := ConservativeEmptinessExplore.Item.resident.inj (by simpa only [encode, found] using encoded)
      exact congrArg some same.1

/-- Closed source values use exactly the certified table encoding. -/
theorem encode_closed (before : InternedConstructorTemplates.State Symbol Guard)
    (value : SourceEmptinessKeys.Closed before) : encode value.val = SourceEmptinessKeys.item value := by
  cases found : SourceEmptinessKeys.key value.val <;>
    simp only [encode, SourceEmptinessKeys.item, found, value.property.2, List.isEmpty_nil] <;> rfl

/-- The actual task scope projects to the original physical constructor heap. -/
def heap (state : TaskState width Symbol Guard) : InternedConstructorTemplates.State Symbol Guard :=
  state.native.machine.heap

/-- The source force and exposure graphs discharge each local inventory law. -/
theorem laws [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    SourceDelayedEmptinessInventory.Laws (heap (width := width)) (SourceEmptinessTasks.Ready emptyGuard conjoin)
      (SourceEmptinessTasks.Force emptyGuard conjoin) Expose encode := by
  refine ⟨fun _ ready => ready.native.semantic.ready, ?_, ?_, ?_⟩
  · intro task before value after ready forced
    have actual := forced.effects ready
    exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.1⟩
  · intro value before rows after ready exposed
    have actual := exposed.effects ready
    exact ⟨actual.1, actual.2.1⟩
  · intro value identity encoded
    exact encode_key value identity true encoded

/-- The delayed trace retains this model's completed-value forces and complete row reads. -/
abbrev Run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :=
  DelayedEmptinessExplore.Trace (Heap := TaskState width Symbol Guard)
    (SourceEmptinessTasks.Force emptyGuard conjoin) Expose encode

/-- A complete task read has a closed resident value in the actual current heap. -/
def Complete (state : TaskState width Symbol Guard) (task : Task) : Prop :=
  ∃ value, SourceEmptinessTasks.read state task = some value ∧ Available (heap state) value ∧ value.free = []

/-- Preserved task results and physical heap growth retain each earlier complete read. -/
theorem Complete.keeps {before after : TaskState width Symbol Guard} {task : Task}
    (complete : Complete before task) (retains : Retains before after) (keeps : Keeps (heap before) (heap after)) :
    Complete after task := by
  obtain ⟨value, found, available, closed⟩ := complete
  exact ⟨value, retains task value found, keeps.available value available, closed⟩

/-- Actual worklist leaves derive final readiness, physical history, and stable shared results. -/
theorem shared_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget seen pending before final after) :
    SourceEmptinessTasks.Ready emptyGuard conjoin before →
      SourceEmptinessTasks.Ready emptyGuard conjoin after ∧ Keeps (heap before) (heap after) ∧ Retains before after := by
  induction trace with
  | done => intro ready; exact ⟨ready, pure_keeps _ ready.native.semantic.ready, .refl _⟩
  | empty forced encoded rest ih =>
      intro ready
      have first := forced.effects ready
      have tail := ih first.1
      exact ⟨tail.1, first.2.1.trans tail.2.1, first.2.2.2.2.1.trans tail.2.2⟩
  | skipped forced encoded skipped rest ih =>
      intro ready
      have first := forced.effects ready
      have tail := ih first.1
      exact ⟨tail.1, first.2.1.trans tail.2.1, first.2.2.2.2.1.trans tail.2.2⟩
  | admit forced encoded fresh exposed rest ih =>
      intro ready
      have first := forced.effects ready
      have rows := exposed.effects first.1
      have tail := ih rows.1
      exact ⟨tail.1, first.2.1.trans (rows.2.1.trans tail.2.1),
        first.2.2.2.2.1.trans (rows.2.2.trans tail.2.2)⟩

/-- Every initially pending task has a closed resident read at the actual final heap. -/
theorem pending_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget seen pending before final after) :
    SourceEmptinessTasks.Ready emptyGuard conjoin before → ∀ task ∈ pending, Complete after task := by
  induction trace with
  | done => intro ready task impossible; cases impossible
  | empty forced encoded rest ih =>
      intro ready task member
      have first := forced.effects ready
      have tail := shared_effects rest first.1
      rcases List.mem_cons.mp member with rfl | member
      · exact Complete.keeps (⟨_, first.2.2.2.2.2, first.2.2.1, first.2.2.2.1⟩ : Complete _ _) tail.2.2 tail.2.1
      · exact ih first.1 task member
  | skipped forced encoded skipped rest ih =>
      intro ready task member
      have first := forced.effects ready
      have tail := shared_effects rest first.1
      rcases List.mem_cons.mp member with rfl | member
      · exact Complete.keeps (⟨_, first.2.2.2.2.2, first.2.2.1, first.2.2.2.1⟩ : Complete _ _) tail.2.2 tail.2.1
      · exact ih first.1 task member
  | admit forced encoded fresh exposed rest ih =>
      intro ready task member
      have first := forced.effects ready
      have rows := exposed.effects first.1
      have tail := shared_effects rest rows.1
      rcases List.mem_cons.mp member with rfl | member
      · exact Complete.keeps (⟨_, first.2.2.2.2.2, first.2.2.1, first.2.2.2.1⟩ : Complete _ _)
          (rows.2.2.trans tail.2.2) (rows.2.1.trans tail.2.1)
      · exact ih rows.1 task (List.mem_append_right _ member)

/-- Every newly stored row has complete task readout in the final shared state. -/
theorem new_rows_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget seen pending before final after) :
    SourceEmptinessTasks.Ready emptyGuard conjoin before →
      ∀ key entry, DelayedEmptinessExplore.lookup key final = some entry →
        DelayedEmptinessExplore.lookup key seen = some entry ∨ ∀ task ∈ entry.rows.flatten, Complete after task := by
  induction trace with
  | done => intro ready key entry found; exact Or.inl found
  | empty forced encoded rest ih =>
      intro ready key entry found
      exact ih (forced.effects ready).1 key entry found
  | skipped forced encoded skipped rest ih =>
      intro ready key entry found
      exact ih (forced.effects ready).1 key entry found
  | @admit task before value forcedHeap identity closed budget seen rows exposedHeap pending final after
      forced encoded fresh exposed rest ih =>
      intro ready key entry found
      have first := forced.effects ready
      have captured := exposed.effects first.1
      rcases ih captured.1 key entry found with old | entered
      · by_cases same : key = identity
        · subst key
          have actual : (⟨identity, value, rows⟩ : Entry Task Value) = entry := by
            simpa only [DelayedEmptinessExplore.lookup, ↓reduceIte, Option.some.injEq] using old
          subst entry
          exact Or.inr (fun child member => pending_complete rest captured.1 child (List.mem_append_left _ member))
        · exact Or.inl (by simpa only [DelayedEmptinessExplore.lookup, same, ↓reduceIte] using old)
      · exact Or.inr entered

/-- Empty-start exploration derives complete reads for all actual stored requirement rows. -/
theorem rows_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget [] pending before final after)
    (ready : SourceEmptinessTasks.Ready emptyGuard conjoin before)
    (key : Int) (entry : Entry Task Value) (found : DelayedEmptinessExplore.lookup key final = some entry) :
    ∀ task ∈ entry.rows.flatten, Complete after task := by
  rcases new_rows_complete trace ready key entry found with impossible | complete
  · cases impossible
  · exact complete

/-- Read a completed requirement; the empty fallback is unused on certified returned rows. -/
def readItem (state : TaskState width Symbol Guard) (task : Task) : ConservativeEmptinessExplore.Item :=
  encode ((SourceEmptinessTasks.read state task).getD .empty)

/-- A certified complete read uses its actual value and does not use the empty fallback. -/
theorem readItem_complete {state : TaskState width Symbol Guard} {task : Task} (complete : Complete state task) :
    ∃ value, SourceEmptinessTasks.read state task = some value ∧ Available (heap state) value ∧ value.free = [] ∧
      readItem state task = encode value := by
  obtain ⟨value, found, available, closed⟩ := complete
  exact ⟨value, found, available, closed, by simp only [readItem, found, Option.getD_some]⟩

/-- Retain literal keys and ordered task rows when reading the completed table. -/
def table (state : TaskState width Symbol Guard) (entries : DelayedEmptinessExplore.Table Task Value) :
    ConservativeEmptinessExplore.Table :=
  entries.map (fun entry => (entry.key, entry.rows.map (List.map (readItem state))))

/-- Completed row readout retains exactly the actual stored table keys. -/
theorem table_keys (state : TaskState width Symbol Guard) (entries : DelayedEmptinessExplore.Table Task Value) :
    (table state entries).map Prod.fst = entries.map Entry.key := by
  simp only [table, List.map_map, Function.comp_def]

/-- Actual source admission bounds also bound the literal completed table length. -/
theorem table_length_le [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget [] pending before final after) :
    (table after final).length ≤ budget := by
  simpa only [table, List.length_map, List.length_nil, Nat.zero_add] using trace.length_le

/-- After actual row completion, the source budget bounds the equality-stop fixed-point phase. -/
theorem grow_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget [] pending before final after) :
    ConservativeEmptinessTable.grow (table after final) (budget + 1) (fun _ => false) =
      some (ConservativeEmptinessTable.possible (table after final)) := by
  have bound := table_length_le trace
  exact ConservativeEmptinessTable.grow_rounds_complete (table after final) budget 0
    (by simpa only [Nat.zero_add] using bound)

/-- Actual source leaves derive final resident records without a final validity premise. -/
theorem records [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget [] pending before final after)
    (ready : SourceEmptinessTasks.Ready emptyGuard conjoin before) :
    SourceEmptinessInventory.Records (heap after) (SourceDelayedEmptinessInventory.entries final) :=
  SourceDelayedEmptinessInventory.final_records (laws emptyGuard conjoin) trace ready (by intro _ impossible; cases impossible)

/-- The literal final table derives certified complete-record readback from actual source leaves. -/
theorem readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget [] pending before final after)
    (ready : SourceEmptinessTasks.Ready emptyGuard conjoin before)
    (ops : EqualityReduction.Operations (SourceEmptinessKeys.Closed (heap after)) Symbol)
    (emptyField : ops.empty = SourceEmptinessKeys.empty (heap after)) :
    ConservativeEmptinessRows.Readback ops
      (SourceEmptinessInventory.read (heap after) (SourceDelayedEmptinessInventory.entries final)
        (records trace ready) (table after final)) (SourceEmptinessKeys.classify (table after final)) :=
  SourceDelayedEmptinessInventory.readback (laws emptyGuard conjoin) trace ready
    (by intro _ impossible; cases impossible) (table after final) (table_keys after final) ops emptyField

local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Reached source exploration retains normalized fields through every actual native force and row read. -/
theorem fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (trace : Run (width := width) top conjoin budget seen pending before final after) :
    SourceEmptinessTasks.Ready top conjoin before → SourceEqualityNativeDemandFieldHeap.Heap (heap before) →
      SourceEqualityNativeDemandFieldHeap.Heap (heap after) := by
  induction trace with
  | done => intro ready initial; exact initial
  | empty forced encoded rest ih =>
      intro ready initial
      exact ih (forced.effects ready).1 (SourceEmptinessTaskFields.force_fields forced ready initial)
  | skipped forced encoded skipped rest ih =>
      intro ready initial
      exact ih (forced.effects ready).1 (SourceEmptinessTaskFields.force_fields forced ready initial)
  | admit forced encoded fresh exposed rest ih =>
      intro ready initial
      have first := forced.effects ready
      have firstFields := SourceEmptinessTaskFields.force_fields forced ready initial
      exact ih (exposed.effects first.1).1 (SourceEmptinessTaskFields.expose_fields exposed first.1 firstFields)

/-- Original construction starts an empty task scope at its exact physical heap. -/
def initial (width : Nat) (heap : InternedConstructorTemplates.State Symbol Guard) : TaskState width Symbol Guard :=
  SourceEmptinessTasks.start (SourceEqualityNativeInitial.cold width heap)

/-- Every original normalized closed input derives the initial task domain and normalized physical fields. -/
theorem source [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression) :
    ∃ value before, InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value before ∧
      SourceEmptinessTasks.Ready top conjoin (initial width before) ∧
      SourceEqualityNativeDemandFieldHeap.Heap (heap (initial width before)) ∧
      Available (heap (initial width before)) value ∧ value.free = [] := by
  obtain ⟨value, before, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value before built
  have ready := SourceEqualityNativeInitial.ready width top conjoin before semantic
  refine ⟨value, before, built, SourceEmptinessTasks.start_ready _ ready, ?_,
    (InternedFreshOrdinaryFacts.closed_verified expression).result value before built,
    InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value before built⟩
  change SourceEqualityNativeDemandFieldHeap.Heap before
  simpa only [SourceEqualityNativeDemandFieldHeap.Heap, built, InternedNestedConstruction.Outcome.state] using
    InternedFreshOrdinaryConstraintHeap.build_heap
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression [] InternedConstructorTemplates.empty
      (InternedFreshOrdinaryConstraintHeap.empty_heap _) annotations

end MicroCFTA.SourceEmptinessTaskTrace
