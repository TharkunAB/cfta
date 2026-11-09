import MicroCFTA.SourceCurrentConjunctionSharedWorklistVisitProgress
import MicroCFTA.SourceCurrentConjunctionRequirementRowsOrigins
import MicroCFTA.SourceCurrentConjunctionRequirementPublication

/-!
# Progress of an actual successful shared-worklist step

A successful transition lowers the remaining tuple budget or its fixed
finite queue vector. The actual credit producer supplies post-state credits.
Cache publication identifies the returned row tail. Its stored credit is
strictly smaller than the removed head credit. No future rank or worker
success is assumed. Whole-call contracts remain separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistStepProgress
open InternedConstructorTemplates (EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistWeight
open SourceCurrentConjunctionRequirementRowsOrigins (Credits)
variable {Symbol Formula : Type}
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual successful nonterminal step lowers the internally certified lexicographic rank. -/
theorem step_decreases (bound p h : Nat) (credits added : List Nat)
    (before after : State Symbol Formula)
    (bounded : ∀ credit ∈ credits, credit ≤ bound)
    (present : RowsPresent credits before.pending)
    (actual : step p h before = .done .more after)
    (post : Credits (credits ++ added) after.storage) :
    Prod.Lex (fun first last : Nat => first < last) (HeightOrder.VectorBelow (bound + 2))
      (after.budget, rank bound (credits ++ added) after.pending)
      (before.budget, rank bound credits before.pending) := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending] at actual
      cases actual
  | cons task rest =>
      have restPresent : RowsPresent credits rest := by
        intro handle member
        apply present handle
        rw [pending]
        exact List.mem_cons_of_mem _ member
      have restRank : rank bound (credits ++ added) rest = rank bound credits rest := by
        funext index
        exact congrFun (weight_append_credits credits added rest restPresent) index.val
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending] at actual
          have removed : HeightOrder.VectorBelow (bound + 2)
              (rank bound credits rest) (rank bound credits before.pending) := by
            rw [pending]
            simpa only [List.nil_append] using nodes_removed bound credits nodes [] rest
          simpa only [pending] using SourceCurrentConjunctionSharedWorklistVisitProgress.visit_decreases
            bound h credits added nodes rest before after restPresent removed actual
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending] at actual
              cases actual
              apply Prod.Lex.right
              change HeightOrder.VectorBelow (bound + 2)
                (rank bound (credits ++ added) rest) (rank bound credits (.requirements [] :: rest))
              rw [restRank]
              simpa only [List.nil_append] using requirements_nil_removed bound credits [] rest
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle
                  before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced] at actual
                  cases actual
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced] at actual
                  have remainingPresent : RowsPresent credits (.requirements handles :: rest) := by
                    intro query member
                    rcases List.mem_cons.mp member with impossible | member
                    · cases impossible
                    · exact restPresent query member
                  have removed : HeightOrder.VectorBelow (bound + 2)
                      (rank bound credits (.requirements handles :: rest))
                      (rank bound credits before.pending) := by
                    rw [pending]
                    simpa only [List.nil_append] using
                      requirement_removed bound credits handle handles [] rest
                  simpa only [pending] using SourceCurrentConjunctionSharedWorklistVisitProgress.visit_decreases
                    bound h credits added nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                    after remainingPresent removed actual
      | rows handle =>
          obtain ⟨credit, own⟩ := present handle (by rw [pending]; exact List.mem_cons_self)
          have ownBound : credit ≤ bound := bounded credit (List.mem_of_getElem? own)
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced] at actual
              cases actual
          | done row storage =>
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced] at actual
                  cases actual
                  apply Prod.Lex.right
                  change HeightOrder.VectorBelow (bound + 2)
                    (rank bound (credits ++ added) rest) (rank bound credits (.rows handle :: rest))
                  rw [restRank]
                  simpa only [List.nil_append] using
                    rows_removed bound credits handle credit [] rest own ownBound
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced] at actual
                  cases actual
                  have published := SourceCurrentConjunctionRequirementPublication.nextRow_done
                    handle before.storage storage (some (handles, tail)) advanced
                  obtain ⟨ownAfter, nextCredit, afterFound, tailFound, smaller, _⟩ :=
                    SourceCurrentConjunctionRequirementRowsOrigins.cached_tail post handle tail handles published
                  have extended : (credits ++ added)[handle]? = some credit := by
                    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp own).1]
                    exact own
                  have same : ownAfter = credit := Option.some.inj (afterFound.symm.trans extended)
                  have tailSmaller : nextCredit < credit := by simpa only [same] using smaller
                  apply Prod.Lex.right
                  change HeightOrder.VectorBelow (bound + 2)
                    (rank bound (credits ++ added) (.requirements handles :: .rows tail :: rest))
                    (rank bound credits (.rows handle :: rest))
                  have allPresent : RowsPresent credits ([] ++ .rows handle :: rest) := by
                    simpa only [List.nil_append, pending] using present
                  simpa only [List.nil_append] using
                    rows_live_append bound credits added handle tail credit nextCredit handles [] rest
                      own ownBound tailFound tailSmaller allPresent

end MicroCFTA.SourceCurrentConjunctionSharedWorklistStepProgress
