import MicroCFTA.SourceCurrentConjunctionRequirementRowsOrigins

/-!
# Original bounds for actual row-spine credits

The fixed bound applies to every allocated credit. A live row allocates its
literal remaining raw length. That length is smaller than the old head
credit. Rejection, cached hits, and failures retain the existing bound.
The proof derives credits for every actual outcome. The bound is not an
additional worker allowance.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsCreditBounds
open InternedConstructorTemplates
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementRowsOrigins (Credits Bound)
variable {Symbol Formula : Type}
local notation "Row" => EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "SpineState" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

private theorem append_bounded (bound : Nat) (credits : List Nat) (next : Nat)
    (bounded : ∀ credit ∈ credits, credit ≤ bound) (enough : next ≤ bound) :
    ∀ credit ∈ credits ++ [next], credit ≤ bound := by
  intro credit member
  rcases List.mem_append.mp member with old | fresh
  · exact bounded credit old
  · have same : credit = next := List.mem_singleton.mp fresh
    simpa only [same] using enough

private theorem update_credits {credits : List Nat} {before : SpineState}
    (valid : Credits credits before) {handle credit : Nat}
    (own : credits[handle]? = some credit) (replacement : Spine Symbol Formula)
    (bound : Bound credits credit replacement) :
    Credits credits (updateSpine handle replacement before) := by
  have inside : handle < before.spines.length := by
    have bounded := (List.getElem?_eq_some_iff.mp own).1
    rw [valid.length] at bounded
    exact bounded
  refine ⟨by simpa only [updateSpine, List.length_set] using valid.length, ?_⟩
  intro index cell found
  change (before.spines.set handle replacement)[index]? = some cell at found
  by_cases same : handle = index
  · subst index
    rw [List.getElem?_set_self inside] at found
    cases found
    exact ⟨credit, own, bound⟩
  · rw [List.getElem?_set_ne same] at found
    exact valid.cells index cell found

/-- Initialization derives empty credits within every fixed original bound. -/
theorem initial (bound : Nat)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Credits [] (SourceCurrentConjunctionRequirementRows.initial before) ∧
      ∀ credit ∈ ([] : List Nat), credit ≤ bound := by
  refine ⟨SourceCurrentConjunctionRequirementRowsOrigins.initial before, ?_⟩
  intro credit member
  cases member

/-- Actual pending allocation derives its bounded credit from the supplied raw length. -/
theorem allocate_pending (bound : Nat) {credits : List Nat} {before : SpineState}
    (valid : Credits credits before) (bounded : ∀ credit ∈ credits, credit ≤ bound)
    (tuples : List (List Row)) (enough : tuples.length ≤ bound) :
    Credits (credits ++ [tuples.length]) (allocateSpine (.pending tuples) before).2 ∧
      ∀ credit ∈ credits ++ [tuples.length], credit ≤ bound :=
  ⟨SourceCurrentConjunctionRequirementRowsOrigins.allocate_pending valid tuples,
    append_bounded bound credits tuples.length bounded enough⟩

private theorem pending_bounded (bound : Nat) (tuples : List (List Row)) :
    ∀ (handle : Nat) (before : SpineState) (credits : List Nat),
      Credits credits before → (∀ credit ∈ credits, credit ≤ bound) →
      lookupSpine handle before = some (.pending tuples) →
      ∃ added, Credits (credits ++ added) (nextRow handle before).state ∧
        ∀ credit ∈ credits ++ added, credit ≤ bound := by
  induction tuples with
  | nil =>
      intro handle before credits valid bounded found
      obtain ⟨credit, own, _⟩ := valid.cells handle (.pending []) found
      refine ⟨[], ?_⟩
      rw [nextRow_nil handle before found]
      simpa only [List.append_nil, Outcome.state] using
        And.intro (update_credits valid own (.done none) True.intro) bounded
  | cons tuple rest ih =>
      intro handle before credits valid bounded found
      obtain ⟨credit, own, headBound⟩ := valid.cells handle (.pending (tuple :: rest)) found
      change (tuple :: rest).length ≤ credit at headBound
      have ownBound : credit ≤ bound := bounded credit (List.mem_of_getElem? own)
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          have kept := SourceCurrentConjunctionRequirementRowsOrigins.prepareTuple_credits valid tuple
          rw [prepared] at kept
          refine ⟨[], ?_⟩
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          simpa only [List.append_nil, Outcome.state] using And.intro kept bounded
      | done result after =>
          have retained := prepareTuple_spines tuple before
          rw [prepared] at retained
          change after.spines = before.spines at retained
          have kept : Credits credits after :=
            SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid retained
          cases result with
          | none =>
              have shorter : Bound credits credit (Spine.pending rest) := by
                change rest.length ≤ credit
                simp only [List.length_cons] at headBound
                omega
              have continued := update_credits kept own (.pending rest) shorter
              have afterFound : lookupSpine handle after = some (.pending (tuple :: rest)) := by
                change after.spines[handle]? = some (.pending (tuple :: rest))
                rw [retained]
                exact found
              have nextFound := lookupSpine_update handle (.pending (tuple :: rest))
                (.pending rest) after afterFound
              obtain ⟨added, post⟩ := ih handle _ credits continued bounded nextFound
              refine ⟨added, ?_⟩
              rw [nextRow_rejected handle tuple rest before after found prepared]
              exact post
          | some row =>
              have smaller : rest.length < credit := by
                simp only [List.length_cons] at headBound
                omega
              have tailBound : rest.length ≤ bound := by omega
              obtain ⟨allocated, allBounded⟩ := allocate_pending bound kept bounded rest tailBound
              have ownAfter : (credits ++ [rest.length])[handle]? = some credit := by
                rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp own).1]
                exact own
              have tailCredit : (credits ++ [rest.length])[after.spines.length]? =
                  some rest.length := by
                rw [← kept.length]
                simp
              have published := update_credits allocated ownAfter
                (Spine.done (some (row, after.spines.length)))
                (show Bound (credits ++ [rest.length]) credit
                  (Spine.done (some (row, after.spines.length))) from
                  ⟨rest.length, tailCredit, smaller⟩)
              refine ⟨[rest.length], ?_⟩
              rw [nextRow_live handle tuple rest before after row found prepared]
              exact ⟨published, allBounded⟩

/-- Every actual row outcome derives appended credits within the same original bound. -/
theorem nextRow_bounded (bound handle : Nat) {credits : List Nat} {before : SpineState}
    (valid : Credits credits before) (bounded : ∀ credit ∈ credits, credit ≤ bound) :
    ∃ added, Credits (credits ++ added) (nextRow handle before).state ∧
      ∀ credit ∈ credits ++ added, credit ≤ bound := by
  cases found : lookupSpine handle before with
  | none =>
      refine ⟨[], ?_⟩
      rw [nextRow_missing handle before found]
      simpa only [List.append_nil, Outcome.state] using And.intro valid bounded
  | some cell =>
      cases cell with
      | pending tuples => exact pending_bounded bound tuples handle before credits valid bounded found
      | done row =>
          refine ⟨[], ?_⟩
          rw [nextRow_hit handle row before found]
          simpa only [List.append_nil, Outcome.state] using And.intro valid bounded

end MicroCFTA.SourceCurrentConjunctionRequirementRowsCreditBounds
