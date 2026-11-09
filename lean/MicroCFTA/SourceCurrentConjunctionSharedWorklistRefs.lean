import MicroCFTA.SourceCurrentConjunctionSharedWorklistWeight
import MicroCFTA.SourceCurrentConjunctionRequirementRowsOrigins
import MicroCFTA.SourceCurrentConjunctionRequirementPublication

/-!
# Present row handles in actual shared-worklist outcomes

Appending actual credits preserves every earlier queue handle. Positive
sampling allocates a handle within the aligned post-state credit list.
A returned live row publishes its cached head and has a present tail.
The post-state credits are an internal witness from the actual credit
producer. No native readiness or future successful work is required here.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistRefs
open InternedConstructorTemplates
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistWeight (RowsPresent)
open SourceCurrentConjunctionRequirementRowsOrigins (Credits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula

private theorem nodes_present (credits : List Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (present : RowsPresent credits rest) : RowsPresent credits (.nodes nodes :: rest) := by
  intro handle member
  rcases List.mem_cons.mp member with impossible | member
  · cases impossible
  · exact present handle member

private theorem requirements_present (credits handles : List Nat) (rest : List (Task Symbol Formula))
    (present : RowsPresent credits rest) : RowsPresent credits (.requirements handles :: rest) := by
  intro handle member
  rcases List.mem_cons.mp member with impossible | member
  · cases impossible
  · exact present handle member

private theorem rows_present (credits : List Nat) (handle : Nat) (rest : List (Task Symbol Formula))
    (own : ∃ credit, credits[handle]? = some credit) (present : RowsPresent credits rest) :
    RowsPresent credits (.rows handle :: rest) := by
  intro query member
  rcases List.mem_cons.mp member with same | member
  · have equal : query = handle := Task.rows.inj same
    subst query
    exact own
  · exact present query member

private theorem index_present {credits : List Nat}
    {state : SourceCurrentConjunctionRequirementRows.State Symbol Formula}
    (valid : Credits credits state) (handle : Nat) (inside : handle < state.spines.length) :
    ∃ credit, credits[handle]? = some credit := by
  have bounded : handle < credits.length := by rw [valid.length]; exact inside
  exact ⟨credits[handle], List.getElem?_eq_some_iff.mpr ⟨bounded, rfl⟩⟩

/-- The initial queue has no row handle and needs no credits. -/
theorem initial_present (budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    RowsPresent [] (SourceCurrentConjunctionSharedWorklistStep.initial budget start before).pending := by
  apply nodes_present [] [start] []
  intro handle member
  cases member

/-- An appended actual credit suffix retains every earlier row-handle lookup. -/
theorem append_present (credits added : List Nat) (pending : List (Task Symbol Formula))
    (present : RowsPresent credits pending) : RowsPresent (credits ++ added) pending := by
  intro handle member
  obtain ⟨credit, found⟩ := present handle member
  refine ⟨credit, ?_⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual visit retains old queue references and derives its newly allocated row reference. -/
theorem visit_present (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (credits added : List Nat) (present : RowsPresent credits rest)
    (post : Credits (credits ++ added) (visit h nodes rest before).state.storage) :
    RowsPresent (credits ++ added) (visit h nodes rest before).state.pending := by
  have retained := append_present credits added rest present
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact retained
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact retained
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact nodes_present _ nodes rest retained
          | done result physical =>
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact retained
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      exact retained
                  | cons tuple tuples =>
                      have actual := visit_positive h nodes rest before physical tuple tuples empty skipped sampled
                      rw [actual] at post ⊢
                      apply rows_present _ _ rest _ retained
                      apply index_present post
                      change before.storage.spines.length <
                        (before.storage.spines ++ [SourceCurrentConjunctionRequirementRows.Spine.pending
                          (tuple :: tuples)]).length
                      simp only [List.length_append, List.length_singleton]
                      omega

/-- Every actual step retains present row handles, including faults and newly returned cached tails. -/
theorem step_present (p h : Nat) (before : WorkState) (credits added : List Nat)
    (present : RowsPresent credits before.pending)
    (post : Credits (credits ++ added) (step p h before).state.storage) :
    RowsPresent (credits ++ added) (step p h before).state.pending := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      intro handle member
      change Task.rows handle ∈ before.pending at member
      rw [pending] at member
      cases member
  | cons task rest =>
      have restPresent : RowsPresent credits rest := by
        intro handle member
        apply present handle
        rw [pending]
        exact List.mem_cons_of_mem _ member
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending] at post ⊢
          exact visit_present h nodes rest before credits added restPresent post
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact append_present credits added rest restPresent
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle
                  before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact append_present credits added before.pending present
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced] at post ⊢
                  exact visit_present h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}} credits added
                    (requirements_present credits handles rest restPresent) post
      | rows handle =>
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact append_present credits added before.pending present
          | done row storage =>
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact append_present credits added rest restPresent
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced] at post ⊢
                  have published := SourceCurrentConjunctionRequirementPublication.nextRow_done handle
                    before.storage storage (some (handles, tail)) advanced
                  obtain ⟨_, next, _, tailFound, _, _⟩ :=
                    SourceCurrentConjunctionRequirementRowsOrigins.cached_tail post handle tail handles published
                  exact requirements_present _ handles (.rows tail :: rest)
                    (rows_present _ tail rest ⟨next, tailFound⟩ (append_present credits added rest restPresent))

end MicroCFTA.SourceCurrentConjunctionSharedWorklistRefs
