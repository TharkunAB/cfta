import MicroCFTA.SourceCurrentConjunctionRowsAllocation

/-!
# Finite allocated conjunction exploration

The pending list retains the source guard order. Only admission decreases
the budget. Each admission constructs its actual rows and both returned
states before prepending its requirements. Open pending inputs can be
skipped. No completed row supplier or future heap invariant is supplied.
The chosen completed read schedule does not specify lazy GHC demand.
-/
namespace MicroCFTA.SourceCurrentConjunctionWorklist
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionRowsAllocation (Ready Effects Rows RowsReady)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Value Symbol Guard → Bool)

/-- Closedness reads the free references of the actual source value. -/
def closed (value : Value Symbol Guard) : Bool := value.free.isEmpty

/-- Successful source admission gives closedness of every original operand. -/
theorem closed_values (nodes : List (Value Symbol Guard)) (allClosed : nodes.all closed = true) : ClosedValues nodes := by
  intro value member
  have own := List.all_eq_true.mp allClosed value member
  exact List.isEmpty_iff.mp own

/-- Pending operands must be available, but can remain open until admission. -/
def PendingReady (state : Physical) (pending : List (List (Value Symbol Guard))) : Prop :=
  ∀ nodes ∈ pending, Values state.heap nodes

/-- Stored entries retain their original physical operands and every requirement. -/
def EntryReady (state : Physical) (entry : Entry) : Prop :=
  Values state.heap entry.nodes ∧ ClosedValues entry.nodes ∧ entry.nodes.any isEmpty = false ∧ RowsReady state entry.rows

/-- Every actual entry remains resident at the returned constructor heap. -/
def TableReady (state : Physical) (table : List Entry) : Prop := ∀ entry ∈ table, EntryReady state entry

/-- Constructor growth retains pending operands without a closedness assumption. -/
theorem pending_keeps {before after : Physical} (keeps : Keeps before.heap after.heap)
    {pending : List (List (Value Symbol Guard))} (ready : PendingReady before pending) : PendingReady after pending :=
  fun nodes member value included => keeps.available value (ready nodes member value included)

/-- Constructor growth retains all original and generated table operands. -/
theorem table_keeps {before after : Physical} (keeps : Keeps before.heap after.heap)
    {table : List Entry} (ready : TableReady before table) : TableReady after table := by
  intro entry member
  have own := ready entry member
  exact ⟨fun value included => keeps.available value (own.1 value included), own.2.1, own.2.2.1,
    SourceCurrentConjunctionRowsAllocation.rows_keeps keeps own.2.2.2⟩

/-- Actual worklist steps retain source skips, inserted rows, and both physical states. -/
inductive Run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → List Entry → List (List (Value Symbol Guard)) → Physical → List Entry → Physical → Prop where
  | done : Run budget table [] state table state
  | empty (impossible : nodes.any isEmpty = true)
      (rest : Run budget table pending before final after) : Run budget table (nodes :: pending) before final after
  | skip (nonempty : nodes.any isEmpty = false)
      (skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = true)
      (rest : Run budget table pending before final after) : Run budget table (nodes :: pending) before final after
  | admit (nonempty : nodes.any isEmpty = false)
      (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
      (rows : Rows nodes before requirements middle)
      (rest : Run (budget - 1) (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ pending) middle final after) :
      Run budget table (nodes :: pending) before final after

/-- Every finite initial worklist derives its actual completed rows and finite admission bound. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (budget : Nat) (table : List Entry) (pending : List (List (Value Symbol Guard)))
    (before : Physical) (ready : Ready before) (stored : TableReady before table) (available : PendingReady before pending) :
    ∃ final after, Run budget table pending before final after ∧ Effects before after ∧
      TableReady after final ∧ final.length ≤ table.length + budget := by
  cases pending with
  | nil => exact ⟨table, before, .done, Effects.refl before ready, stored, by omega⟩
  | cons nodes pending =>
      have tail : PendingReady before pending := fun nodes member => available nodes (List.mem_cons_of_mem _ member)
      cases impossible : nodes.any isEmpty with
      | true =>
          obtain ⟨final, after, actual, effect, finalReady, bound⟩ := complete budget table pending before ready stored tail
          exact ⟨final, after, .empty impossible actual, effect, finalReady, bound⟩
      | false =>
          cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
          | true =>
              obtain ⟨final, after, actual, effect, finalReady, bound⟩ := complete budget table pending before ready stored tail
              exact ⟨final, after, .skip impossible skipped actual, effect, finalReady, bound⟩
          | false =>
              have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes skipped
              have inputs := available nodes List.mem_cons_self
              have noFree := closed_values nodes admitted.2.1
              obtain ⟨requirements, middle, rows, own, requirementReady⟩ :=
                SourceCurrentConjunctionRowsAllocation.rows_complete nodes before ready inputs noFree
              have nextTable : TableReady middle (⟨nodes, requirements⟩ :: table) := by
                intro entry member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨fun value included => own.keeps.available value (inputs value included), noFree, impossible, requirementReady⟩
                · exact table_keeps own.keeps stored entry member
              have nextPending : PendingReady middle (requirements.flatten ++ pending) := by
                intro requirement member
                rcases List.mem_append.mp member with generated | earlier
                · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
                  exact (requirementReady row rowIn requirement requirementIn).1
                · exact pending_keeps own.keeps tail requirement earlier
              obtain ⟨final, after, actual, effect, finalReady, bound⟩ := complete (budget - 1)
                (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ pending) middle own.ready nextTable nextPending
              refine ⟨final, after, .admit impossible skipped rows actual, own.trans effect, finalReady, ?_⟩
              simp only [List.length_cons] at bound
              omega
termination_by (budget, pending.length)
decreasing_by
  all_goals simp_wf
  all_goals first
    | apply Prod.Lex.left; omega
    | apply Prod.Lex.right; simp_all

/-- Empty-start exploration constructs every stored row without a completed-table oracle. -/
theorem entered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (budget : Nat) (pending : List (List (Value Symbol Guard))) (before : Physical)
    (ready : Ready before) (available : PendingReady before pending) :
    ∃ final after, Run budget [] pending before final after ∧ Effects before after ∧
      TableReady after final ∧ final.length ≤ budget := by
  simpa only [List.length_nil, Nat.zero_add] using complete budget [] pending before ready
    (by intro entry member; cases member) available

/-- Actual exploration retains old table reads and unique identity-list keys. -/
theorem Run.retains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))} {before after : Physical}
    (actual : Run budget table pending before final after) :
    (∀ ids entry, SourceCurrentConjunctionEmptinessTable.lookup key ids table = some entry →
      SourceCurrentConjunctionEmptinessTable.lookup key ids final = some entry) ∧
    ((table.map (fun entry => SourceCurrentConjunctionEmptinessTable.keys key entry.nodes)).Nodup →
      (final.map (fun entry => SourceCurrentConjunctionEmptinessTable.keys key entry.nodes)).Nodup) := by
  induction actual with
  | done => exact ⟨fun _ _ found => found, id⟩
  | empty _ _ ih => exact ih
  | skip _ _ _ ih => exact ih
  | @admit budget table nodes before requirements middle pending final after nonempty fresh rows rest ih =>
      have absent := (SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes fresh).2.2
      constructor
      · intro ids entry found
        apply ih.1 ids entry
        by_cases same : ids = SourceCurrentConjunctionEmptinessTable.keys key nodes
        · subst ids; rw [absent] at found; cases found
        · simpa only [SourceCurrentConjunctionEmptinessTable.lookup, same, ite_false] using found
      · intro unique
        apply ih.2
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨(SourceCurrentConjunctionEmptinessTable.lookup_none_iff key _ table).mp absent, unique⟩

end MicroCFTA.SourceCurrentConjunctionWorklist
