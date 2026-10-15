import MicroCFTA.SourceEndpointMemoPublication
import MicroCFTA.SourceEndpointMemoSource

/-!
# No active ancestor demand in resident descendant traversal

The proof derives the active-key condition from strict stored-child descent
and coherent physical identities. It proves the exact completed memo result
for the sequential active-call machine. It does not assume that the machine
finishes or that future memos are valid.
-/
namespace MicroCFTA.SourceEndpointMemoPublicationCorrect
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEndpointMemo
open SourceEndpointMemoPublication (Active active_child not_busy Outcome)
open SourceEndpointMemoAncestry (Step)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained

mutual
/-- Publishing an active root before its body does not introduce an ancestor-key block. -/
theorem run_agrees (value : Value Symbol Guard) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : Available heap value) (active : List (Value Symbol Guard)) (ordered : Active heap value active)
    (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    SourceEndpointMemoPublication.run value active memos =
      .done (SourceEndpointMemo.run value memos).1 (SourceEndpointMemo.run value memos).2 := by
  rw [SourceEndpointMemoPublication.run.eq_def, SourceEndpointMemo.run.eq_def]
  cases found : memos.descendants value.referenceOf with
  | some pair => rcases pair with ⟨original, answer⟩; rfl
  | none =>
      simp only [not_busy value active heap coherent available ordered, Bool.false_eq_true, ↓reduceIte]
      cases value with
      | empty => simp [Value.depth]
      | reference name => simp [Value.depth]
      | mu entry body depth ordinary => simp [Value.depth]
      | union entry members depth free =>
          by_cases zero : depth = 0
          · simp [Value.depth, zero]
          · have children : ∀ child ∈ members, Available heap child := available.children
            have current : ∀ child ∈ members, Active heap child (Value.union entry members depth free :: active) := by
              intro child member
              exact active_child heap _ child available active ordered (.union zero member)
            have calls := many_agrees members heap coherent children _ current memos valid
            simp only [Value.depth, beq_iff_eq, zero, ↓reduceIte]
            rw [calls]
      | node entry edges depth free =>
          by_cases zero : depth = 0
          · simp [Value.depth, zero]
          · have children : ∀ edge ∈ edges, ∀ child ∈ edge.children, Available heap child := by
              intro edge member child selected
              exact available.children child (List.mem_flatMap.mpr ⟨edge, member, selected⟩)
            have current : ∀ edge ∈ edges, ∀ child ∈ edge.children,
                Active heap child (Value.node entry edges depth free :: active) := by
              intro edge member child selected
              exact active_child heap _ child available active ordered (.node zero member selected)
            have calls := rows_agrees edges heap coherent children _ current memos valid
            simp only [Value.depth, beq_iff_eq, zero, ↓reduceIte]
            rw [calls]
termination_by sizeOf value

/-- Every actual child call is below the active ancestors, including after a false sibling. -/
theorem many_agrees (values : List (Value Symbol Guard)) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : ∀ value ∈ values, Available heap value) (active : List (Value Symbol Guard))
    (ordered : ∀ value ∈ values, Active heap value active) (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    SourceEndpointMemoPublication.many values active memos =
      .done (SourceEndpointMemo.many values memos).1 (SourceEndpointMemo.many values memos).2 := by
  cases values with
  | nil => simp [SourceEndpointMemoPublication.many, SourceEndpointMemo.many]
  | cons first rest =>
      rw [SourceEndpointMemoPublication.many, SourceEndpointMemo.many]
      rw [run_agrees first heap coherent (available first (by simp)) active (ordered first (by simp)) memos valid]
      have checked := SourceEndpointMemoCorrect.run_checked first heap coherent (available first (by simp)) memos valid
      cases answer : (SourceEndpointMemo.run first memos).1 with
      | true => simp [answer]
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact many_agrees rest heap coherent (fun value member => available value (by simp [member]))
            active (fun value member => ordered value (by simp [member])) _ checked.valid
termination_by sizeOf values

/-- False original rows retain the active ancestor condition and both current valid memos. -/
theorem rows_agrees (edges : List (EdgeValue Symbol Guard)) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : ∀ edge ∈ edges, ∀ child ∈ edge.children, Available heap child) (active : List (Value Symbol Guard))
    (ordered : ∀ edge ∈ edges, ∀ child ∈ edge.children, Active heap child active)
    (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    SourceEndpointMemoPublication.rows edges active memos =
      .done (SourceEndpointMemo.rows edges memos).1 (SourceEndpointMemo.rows edges memos).2 := by
  cases edges with
  | nil => simp [SourceEndpointMemoPublication.rows, SourceEndpointMemo.rows]
  | cons first rest => cases first with
    | mk entry children =>
        rw [SourceEndpointMemoPublication.rows, SourceEndpointMemo.rows]
        rw [many_agrees children heap coherent (available (.mk entry children) (by simp)) active
          (ordered (.mk entry children) (by simp)) memos valid]
        have checked := SourceEndpointMemoCorrect.many_checked children heap coherent
          (available (.mk entry children) (by simp)) memos valid
        cases answer : (SourceEndpointMemo.many children memos).1 with
        | true => simp [answer]
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact rows_agrees rest heap coherent (fun edge member => available edge (by simp [member]))
              active (fun edge member => ordered edge (by simp [member])) _ checked.valid
termination_by sizeOf edges
end

/-- A resident query with no active ancestors completes with the exact concrete answer and memo histories. -/
theorem cold_complete (value : Value Symbol Guard) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : Available heap value) (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    ∃ after, SourceEndpointMemoPublication.run value [] memos =
      .done (SourceEndpointReachability.reaches source value) after ∧
      SourceEndpointMemo.Valid heap after ∧ Keeps memos after := by
  have checked := SourceEndpointMemoCorrect.run_checked value heap coherent available memos valid
  refine ⟨(SourceEndpointMemo.run value memos).2, ?_, checked.valid, checked.keeps⟩
  rw [run_agrees value heap coherent available [] (by intro ancestor member; cases member) memos valid, checked.answer]

/-- Original construction derives finite sequential helper demand with no active-ancestor assumption. -/
theorem source_complete [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard) :
    ∃ value heap, InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value heap ∧
      ∃ after, SourceEndpointMemoPublication.run value [] SourceEndpointMemo.empty =
        .done (SourceEndpointReachability.reaches source value) after ∧
        SourceEndpointMemo.Valid heap after ∧ Keeps SourceEndpointMemo.empty after := by
  obtain ⟨value, heap, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  let original := InternedFreshOrdinaryGateRank.fromCompleted expression value heap done
  exact ⟨value, heap, done, cold_complete value heap original.context.normal.facts.coherent
    original.available SourceEndpointMemo.empty (empty_valid heap)⟩

end MicroCFTA.SourceEndpointMemoPublicationCorrect
