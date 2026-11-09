import MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterialization
import MicroCFTA.SourceCurrentConjunctionRequirementCellsEffects
import MicroCFTA.SourceCurrentConjunctionRequirementRowsFrame
import MicroCFTA.SourceCurrentConjunctionRequirementPublication

/-!
# Scheduling every unfinished private cell

Every unfinished requirement cell occurs in a pending requirement task.
Every pending row spine has a pending row task. Actual allocation schedules
the exact new handles. Actual forcing publishes a completed value before
removing its task. Thus a drained queue has only cached private cells.
No native readiness, successful future work, or terminal cache is assumed.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistCoverage
open InternedConstructorTemplates
open SourceCurrentConjunctionSharedWorklistStep
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Spine" => SourceCurrentConjunctionRequirementRows.Spine Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "cellLookup" => SourceCurrentConjunctionRequirementCells.lookup
local notation "spineLookup" => SourceCurrentConjunctionRequirementRows.lookupSpine

/-- A literal pending requirement list contains the handle. -/
def Queued (handle : Nat) (pending : List (Task Symbol Formula)) : Prop :=
  ∃ handles, Task.requirements handles ∈ pending ∧ handle ∈ handles

/-- Every unfinished private descriptor retains a task in the same queue. -/
structure Coverage (storage : Storage) (pending : List (Task Symbol Formula)) : Prop where
  cells : ∀ handle cell, cellLookup handle storage.requirements = some cell →
    (∃ nodes, cell = .done nodes) ∨ Queued handle pending
  spines : ∀ handle tuples, spineLookup handle storage = some (.pending tuples) →
    Task.rows handle ∈ pending

/-- The actual work state schedules all unfinished private cells. -/
abbrev Covered (before : WorkState) := Coverage before.storage before.pending

private theorem queue_mono (storage : Storage) (first last : List (Task Symbol Formula))
    (covered : Coverage storage first) (included : ∀ task ∈ first, task ∈ last) : Coverage storage last := by
  constructor
  · intro handle cell found
    rcases covered.cells handle cell found with cached | ⟨handles, queued, member⟩
    · exact Or.inl cached
    · exact Or.inr ⟨handles, included _ queued, member⟩
  · intro handle tuples found
    exact included _ (covered.spines handle tuples found)

private theorem queue_cons (storage : Storage) (task : Task Symbol Formula) (pending : List (Task Symbol Formula))
    (covered : Coverage storage pending) : Coverage storage (task :: pending) :=
  queue_mono storage pending _ covered (fun _ member => List.mem_cons_of_mem _ member)

private theorem queue_swap (storage : Storage) (first second : Task Symbol Formula)
    (rest : List (Task Symbol Formula)) (covered : Coverage storage (first :: second :: rest)) :
    Coverage storage (second :: first :: rest) := by
  apply queue_mono storage _ _ covered
  intro task member
  rcases List.mem_cons.mp member with same | member
  · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl same))
  · rcases List.mem_cons.mp member with same | member
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)

private theorem queued_drop_rows (handle target : Nat) (rest : List (Task Symbol Formula))
    (queued : Queued handle (.rows target :: rest)) : Queued handle rest := by
  obtain ⟨handles, member, own⟩ := queued
  rcases List.mem_cons.mp member with impossible | member
  · cases impossible
  · exact ⟨handles, member, own⟩

private theorem nodes_drop (nodes : List Node) (storage : Storage) (rest : List (Task Symbol Formula))
    (covered : Coverage storage (.nodes nodes :: rest)) : Coverage storage rest := by
  constructor
  · intro handle cell found
    rcases covered.cells handle cell found with cached | ⟨handles, member, own⟩
    · exact Or.inl cached
    · rcases List.mem_cons.mp member with impossible | member
      · cases impossible
      · exact Or.inr ⟨handles, member, own⟩
  · intro handle tuples found
    rcases List.mem_cons.mp (covered.spines handle tuples found) with impossible | member
    · cases impossible
    · exact member

private theorem allocate_cells (cells : List Cell) (storage : Storage) (pending : List (Task Symbol Formula))
    (covered : Coverage storage pending) :
    let allocated := SourceCurrentConjunctionRequirementRows.allocateCells cells storage.requirements
    Coverage {storage with requirements := allocated.2} (.requirements allocated.1 :: pending) := by
  constructor
  · intro handle cell found
    by_cases old : handle < storage.requirements.cells.length
    · have original : cellLookup handle storage.requirements = some cell := by
        change (SourceCurrentConjunctionRequirementRows.allocateCells cells storage.requirements).2.cells[handle]? = some cell at found
        rw [SourceCurrentConjunctionRequirementRows.allocateCells_order,
          List.getElem?_append_left old] at found
        exact found
      rcases covered.cells handle cell original with cached | ⟨handles, queued, member⟩
      · exact Or.inl cached
      · exact Or.inr ⟨handles, List.mem_cons_of_mem _ queued, member⟩
    · have inside := (List.getElem?_eq_some_iff.mp found).1
      change handle < (SourceCurrentConjunctionRequirementRows.allocateCells cells storage.requirements).2.cells.length at inside
      rw [SourceCurrentConjunctionRequirementRows.allocateCells_order] at inside
      simp only [List.length_append] at inside
      refine Or.inr ⟨_, List.mem_cons_self, ?_⟩
      rw [SourceCurrentConjunctionRequirementRows.allocateCells_handles]
      apply List.mem_range'.mpr
      refine ⟨handle - storage.requirements.cells.length, by omega, ?_⟩
      simp only [Nat.one_mul]
      omega
  · intro handle tuples found
    exact List.mem_cons_of_mem _ (covered.spines handle tuples found)

private theorem allocate_spine (tuples : List (List Row)) (storage : Storage)
    (pending : List (Task Symbol Formula)) (covered : Coverage storage pending) :
    let allocated := SourceCurrentConjunctionRequirementRows.allocateSpine (.pending tuples) storage
    Coverage allocated.2 (.rows allocated.1 :: pending) := by
  constructor
  · intro handle cell found
    rcases covered.cells handle cell found with cached | ⟨handles, queued, member⟩
    · exact Or.inl cached
    · exact Or.inr ⟨handles, List.mem_cons_of_mem _ queued, member⟩
  · intro handle rows found
    by_cases old : handle < storage.spines.length
    · have original : spineLookup handle storage = some (.pending rows) := by
        change (storage.spines ++ [.pending tuples])[handle]? = some (.pending rows) at found
        rw [List.getElem?_append_left old] at found
        exact found
      exact List.mem_cons_of_mem _ (covered.spines handle rows original)
    · have inside := (List.getElem?_eq_some_iff.mp found).1
      change handle < (storage.spines ++
        [SourceCurrentConjunctionRequirementRows.Spine.pending tuples]).length at inside
      simp only [List.length_append, List.length_singleton] at inside
      have same : handle = storage.spines.length := by omega
      subst handle
      exact List.mem_cons_self

private theorem update_spine (target : Nat) (replacement : Spine) (storage : Storage)
    (pending : List (Task Symbol Formula)) (covered : Coverage storage pending)
    (scheduled : Task.rows target ∈ pending) :
    Coverage (SourceCurrentConjunctionRequirementRows.updateSpine target replacement storage) pending := by
  constructor
  · exact covered.cells
  · intro handle tuples found
    by_cases same : handle = target
    · subst handle
      exact scheduled
    · have original : spineLookup handle storage = some (.pending tuples) := by
        change (storage.spines.set target replacement)[handle]? = some (.pending tuples) at found
        rw [List.getElem?_set_ne (Ne.symm same)] at found
        exact found
      exact covered.spines handle tuples original

private theorem publish_spine (target : Nat) (row : Option (List Nat × Nat)) (storage : Storage)
    (rest : List (Task Symbol Formula)) (covered : Coverage storage (.rows target :: rest))
    (original : Spine) (present : spineLookup target storage = some original) :
    Coverage (SourceCurrentConjunctionRequirementRows.updateSpine target (.done row) storage) rest := by
  constructor
  · intro handle cell found
    rcases covered.cells handle cell found with cached | queued
    · exact Or.inl cached
    · exact Or.inr (queued_drop_rows handle target rest queued)
  · intro handle tuples found
    by_cases same : handle = target
    · subst handle
      have cached := SourceCurrentConjunctionRequirementRows.lookupSpine_update target original (.done row) storage present
      have impossible := Option.some.inj (cached.symm.trans found)
      cases impossible
    · have old : spineLookup handle storage = some (.pending tuples) := by
        change (storage.spines.set target (.done row))[handle]? = some (.pending tuples) at found
        rw [List.getElem?_set_ne (Ne.symm same)] at found
        exact found
      rcases List.mem_cons.mp (covered.spines handle tuples old) with equal | member
      · exact False.elim (same (Task.rows.inj equal))
      · exact member

private def Prepared (pending : List (Task Symbol Formula)) :
    SourceCurrentConjunctionRequirementRows.Outcome Symbol Formula (Option (List Nat)) → Prop
  | .failed _ after | .done none after => Coverage after pending
  | .done (some handles) after => Coverage after (.requirements handles :: pending)

private theorem prepare_covered (tuple : List Row) (storage : Storage) (pending : List (Task Symbol Formula))
    (covered : Coverage storage pending) :
    Prepared pending (SourceCurrentConjunctionRequirementRows.prepareTuple tuple storage) := by
  unfold SourceCurrentConjunctionRequirementRows.prepareTuple
  dsimp only
  split
  · exact ⟨covered.cells, covered.spines⟩
  · exact ⟨covered.cells, covered.spines⟩
  · split
    · exact ⟨covered.cells, covered.spines⟩
    · let current : Storage := {storage with requirements := {storage.requirements with
        physical := ⟨storage.requirements.physical.heap,
          (SourceCurrentConjunctionEquality.fold tuple storage.requirements.physical.equality).2⟩}}
      exact allocate_cells _ current pending ⟨covered.cells, covered.spines⟩

private def RowPost (target : Nat) (rest : List (Task Symbol Formula)) :
    SourceCurrentConjunctionRequirementRows.Outcome Symbol Formula (Option (List Nat × Nat)) → Prop
  | .failed _ after => Coverage after (.rows target :: rest)
  | .done none after => Coverage after rest
  | .done (some (handles, tail)) after => Coverage after (.requirements handles :: .rows tail :: rest)

private theorem pending_rows (target : Nat) (tuples : List (List Row)) (storage : Storage)
    (rest : List (Task Symbol Formula)) (covered : Coverage storage (.rows target :: rest))
    (found : spineLookup target storage = some (.pending tuples)) :
    RowPost target rest (SourceCurrentConjunctionRequirementRows.nextRow target storage) := by
  open SourceCurrentConjunctionRequirementRows in
  induction tuples generalizing storage with
  | nil =>
      rw [nextRow_nil target storage found]
      exact publish_spine target none storage rest covered (.pending []) found
  | cons tuple tuples ih =>
      have first := prepare_covered tuple storage (.rows target :: rest) covered
      have spines := prepareTuple_spines tuple storage
      cases prepared : prepareTuple tuple storage with
      | failed fault after =>
          rw [nextRow_failed target tuple tuples storage after fault found prepared]
          simpa only [prepared, Prepared, RowPost] using first
      | done row after =>
          rw [prepared] at spines
          change after.spines = storage.spines at spines
          have retained : spineLookup target after = some (.pending (tuple :: tuples)) := by
            change after.spines[target]? = some (.pending (tuple :: tuples))
            rw [spines]
            exact found
          cases row with
          | none =>
              have current : Coverage after (.rows target :: rest) := by
                simpa only [prepared, Prepared] using first
              rw [nextRow_rejected target tuple tuples storage after found prepared]
              exact ih _ (update_spine target (.pending tuples) after _ current List.mem_cons_self)
                (lookupSpine_update target (.pending (tuple :: tuples)) (.pending tuples) after retained)
          | some handles =>
              have current : Coverage after (.requirements handles :: .rows target :: rest) := by
                simpa only [prepared, Prepared] using first
              have reordered := queue_swap after (.requirements handles) (.rows target) rest current
              have allocated := allocate_spine tuples after (.rows target :: .requirements handles :: rest) reordered
              let added := allocateSpine (.pending tuples) after
              have swapped := queue_swap added.2 (.rows added.1) (.rows target)
                (.requirements handles :: rest) allocated
              have old : spineLookup target added.2 = some (.pending (tuple :: tuples)) := by
                change (after.spines ++ [.pending tuples])[target]? = _
                rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp retained).1]
                exact retained
              have published := publish_spine target (some (handles, added.1)) added.2
                (.rows added.1 :: .requirements handles :: rest) swapped (.pending (tuple :: tuples)) old
              rw [nextRow_live target tuple tuples storage after handles found prepared]
              exact queue_swap _ (.rows added.1) (.requirements handles) rest published

private theorem rows_covered (target : Nat) (storage : Storage) (rest : List (Task Symbol Formula))
    (covered : Coverage storage (.rows target :: rest)) :
    RowPost target rest (SourceCurrentConjunctionRequirementRows.nextRow target storage) := by
  open SourceCurrentConjunctionRequirementRows in
  cases found : spineLookup target storage with
  | none =>
      rw [nextRow_missing target storage found]
      exact covered
  | some spine =>
      cases spine with
      | pending tuples => exact pending_rows target tuples storage rest covered found
      | done row =>
          rw [nextRow_hit target row storage found]
          have finished : Coverage storage rest := by
            constructor
            · intro handle cell present
              rcases covered.cells handle cell present with cached | queued
              · exact Or.inl cached
              · exact Or.inr (queued_drop_rows handle target rest queued)
            · intro handle tuples present
              rcases List.mem_cons.mp (covered.spines handle tuples present) with equal | member
              · have same : handle = target := Task.rows.inj equal
                subst handle
                have impossible := Option.some.inj (found.symm.trans present)
                cases impossible
              · exact member
          cases row with
          | none => exact finished
          | some row =>
              rcases row with ⟨handles, tail⟩
              exact queue_cons _ (.requirements handles) _ (queue_cons _ (.rows tail) _ finished)

/-- The initial empty private heaps have no unfinished descriptor to schedule. -/
theorem initial_covered (budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Covered (SourceCurrentConjunctionSharedWorklistStep.initial budget start before) := by
  constructor
  · intro handle cell found
    change ([] : List Cell)[handle]? = some cell at found
    simp only [List.getElem?_nil] at found
    cases found
  · intro handle tuples found
    change ([] : List Spine)[handle]? = some (.pending tuples) at found
    simp only [List.getElem?_nil] at found
    cases found

/-- A drained covered queue has completed caches at every allocated private handle. -/
theorem drained_cached (before : WorkState) (covered : Covered before) (empty : before.pending = []) :
    SourceCurrentConjunctionSharedWorklistMaterialization.CellsCached before.storage ∧
      SourceCurrentConjunctionSharedWorklistMaterialization.SpinesCached before.storage := by
  constructor
  · intro handle cell found
    rcases covered.cells handle cell found with cached | ⟨handles, queued, _⟩
    · exact cached
    · rw [empty] at queued
      cases queued
  · intro handle spine found
    cases spine with
    | done row => exact ⟨row, rfl⟩
    | pending tuples =>
        have queued := covered.spines handle tuples found
        rw [empty] at queued
        cases queued

private theorem queued_trim (target query : Nat) (handles : List Nat) (rest : List (Task Symbol Formula))
    (different : query ≠ target) (queued : Queued query (.requirements (target :: handles) :: rest)) :
    Queued query (.requirements handles :: rest) := by
  obtain ⟨values, member, own⟩ := queued
  rcases List.mem_cons.mp member with same | member
  · have equal : values = target :: handles := Task.requirements.inj same
    subst values
    rcases List.mem_cons.mp own with same | own
    · exact False.elim (different same)
    · exact ⟨handles, List.mem_cons_self, own⟩
  · exact ⟨values, List.mem_cons_of_mem _ member, own⟩

private def Forced (storage : Storage) (target : Nat) (handles : List Nat) (rest : List (Task Symbol Formula)) :
    SourceCurrentConjunctionRequirementCells.Outcome Symbol Formula (List Node) → Prop
  | .failed _ cells => Coverage {storage with requirements := cells} (.requirements (target :: handles) :: rest)
  | .done _ cells => Coverage {storage with requirements := cells} (.requirements handles :: rest)

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem force_covered (p h target : Nat) (handles : List Nat) (storage : Storage)
    (rest : List (Task Symbol Formula)) (covered : Coverage storage (.requirements (target :: handles) :: rest)) :
    Forced storage target handles rest (SourceCurrentConjunctionRequirementCells.force p h target storage.requirements) := by
  have other := SourceCurrentConjunctionRequirementCellsEffects.force_other p h target storage.requirements
  cases actual : SourceCurrentConjunctionRequirementCells.force p h target storage.requirements with
  | failed fault cells =>
      constructor
      · intro handle cell found
        by_cases same : handle = target
        · subst handle
          exact Or.inr ⟨target :: handles, List.mem_cons_self, List.mem_cons_self⟩
        · have kept := other handle same
          rw [actual] at kept
          exact covered.cells handle cell (kept.symm.trans found)
      · exact covered.spines
  | done nodes cells =>
      constructor
      · intro handle cell found
        by_cases same : handle = target
        · subst handle
          have published := SourceCurrentConjunctionRequirementPublication.force_done p h target
            storage.requirements cells nodes actual
          exact Or.inl ⟨nodes, (Option.some.inj (found.symm.trans published))⟩
        · have kept := other handle same
          rw [actual] at kept
          rcases covered.cells handle cell (kept.symm.trans found) with cached | queued
          · exact Or.inl cached
          · exact Or.inr (queued_trim target handle handles rest same queued)
      · intro handle tuples found
        rcases List.mem_cons.mp (covered.spines handle tuples found) with impossible | member
        · cases impossible
        · exact List.mem_cons_of_mem _ member

variable [DecidableEq Symbol]

private theorem visit_covered (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (covered : Coverage before.storage rest) :
    Covered (visit h nodes rest before).state := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact covered
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact covered
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact queue_cons _ (.nodes nodes) _ ⟨covered.cells, covered.spines⟩
          | done result physical =>
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact ⟨covered.cells, covered.spines⟩
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      exact ⟨covered.cells, covered.spines⟩
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      exact allocate_spine (tuple :: tuples) _ rest ⟨covered.cells, covered.spines⟩

/-- Every actual successful or failed step retains scheduling for every unfinished private cell. -/
theorem step_covered (p h : Nat) (before : WorkState) (covered : Covered before) :
    Covered (step p h before).state := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact covered
  | cons task rest =>
      have current : Coverage before.storage (task :: rest) := by
        rw [← pending]
        exact covered
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          exact visit_covered h nodes rest before (nodes_drop nodes before.storage rest current)
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              constructor
              · intro handle cell found
                rcases current.cells handle cell found with cached | ⟨handles, member, own⟩
                · exact Or.inl cached
                · rcases List.mem_cons.mp member with same | member
                  · have equal : handles = [] := Task.requirements.inj same
                    subst handles
                    cases own
                  · exact Or.inr ⟨handles, member, own⟩
              · intro handle tuples found
                rcases List.mem_cons.mp (current.spines handle tuples found) with impossible | member
                · cases impossible
                · exact member
          | cons handle handles =>
              have forced := force_covered p h handle handles before.storage rest current
              cases actual : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending actual]
                  rw [actual] at forced
                  simpa only [Forced, Covered, Outcome.state, pending] using forced
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending actual]
                  rw [actual] at forced
                  exact visit_covered h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}} forced
      | rows handle =>
          have advanced := rows_covered handle before.storage rest current
          cases actual : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending actual]
              rw [actual] at advanced
              simpa only [RowPost, Covered, Outcome.state, pending] using advanced
          | done row storage =>
              rw [actual] at advanced
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending actual]
                  exact advanced
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending actual]
                  exact advanced

end MicroCFTA.SourceCurrentConjunctionSharedWorklistCoverage
