import MicroCFTA.ConstrainedRecursionGate

/-!
# Completion of ranked recursive gate evaluation

A ranked unbounded computation has a finite successful fuel amount. The
proof combines the finite child lists with the same lexicographic measure
used by the unbounded worker. Fuel is an instrument, not a semantic limit.
-/
namespace MicroCFTA.RankedGateCompletion
open EqualityNormalize ConstrainedRecursionGate
open RecursiveReductionBarrier (finite)

/-- Finitely many individually completed requests share a finite fuel amount. -/
theorem common_fuel (test : Nat → Item → Option Bool) (target : Item → Bool)
    (stable : ∀ fuel extra item, test fuel item = some (target item) →
      test (fuel + extra) item = some (target item))
    (items : List Item) (complete : ∀ item ∈ items, ∃ fuel, test fuel item = some (target item)) :
    ∃ fuel, ∀ item ∈ items, test fuel item = some (target item) := by
  induction items with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
      obtain ⟨headFuel, head⟩ := complete first (by simp)
      obtain ⟨tailFuel, tail⟩ := ih (fun item member => complete item (by simp [member]))
      refine ⟨headFuel + tailFuel, ?_⟩
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact stable headFuel tailFuel _ head
      · simpa [Nat.add_comm] using stable tailFuel headFuel item (tail item member)

/-- Completed child requests make the ordered Boolean disjunction complete. -/
theorem anyKnown_exact (test : Item → Option Bool) (target : Item → Bool)
    (items : List Item) (same : ∀ item ∈ items, test item = some (target item)) :
    anyKnown test items = some (items.any target) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      have head := same first (by simp)
      have tail := ih (fun item member => same item (by simp [member]))
      cases value : target first <;> simp [anyKnown, head, value, tail]

/-- Every ranked source dispatch has a finite completed instrumented run. -/
theorem completes (read : ConstrainedRecursionGate.Read Node) (ranking : UnfoldingRank read)
    (path : Path) (node : Node) :
    ∃ fuel, nodeMeets read fuel path node = some (total read ranking path node) := by
  rw [total.eq_def]
  cases view : read.view node with
  | reference | union =>
      exact ⟨1, by simp [nodeMeets, dispatch, view]⟩
  | empty =>
      refine ⟨1, ?_⟩
      cases path <;> cases closed : finite read.toRead node <;>
        simp [nodeMeets, dispatch, view, closed]
  | binder =>
      by_cases closed : finite read.toRead node = true
      · exact ⟨1, by simp [nodeMeets, dispatch, view, closed]⟩
      · cases plain : read.unconstrained node with
        | false => exact ⟨1, by simp [nodeMeets, dispatch, view, closed, plain]⟩
        | true =>
            by_cases free : (read.free node).isEmpty = true
            · exact ⟨1, by simp [nodeMeets, dispatch, view, closed, plain, free]⟩
            · obtain ⟨fuel, completed⟩ := completes read ranking path (read.unfold node)
              refine ⟨fuel + 1, ?_⟩
              simpa only [nodeMeets, dispatch, view, closed, plain, free,
                Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte] using completed
  | branches edges =>
      by_cases closed : finite read.toRead node = true
      · exact ⟨1, by simp [nodeMeets, dispatch, view, closed]⟩
      · cases path with
        | nil => exact ⟨1, by simp [nodeMeets, dispatch, view, closed]⟩
        | cons index rest =>
            let target := fun nodes : List Node => match nodes[index]? with
              | none => false
              | some next => total read ranking rest next
            have each : ∀ nodes ∈ edges, ∃ fuel,
                child (nodeMeets read fuel) nodes index rest = some (target nodes) := by
              intro nodes _
              cases present : nodes[index]? with
              | none => exact ⟨0, by simp [child, target, present]⟩
              | some next =>
                  obtain ⟨fuel, completed⟩ := completes read ranking rest next
                  exact ⟨fuel, by simpa [child, target, present] using completed⟩
            have stable : ∀ fuel extra nodes,
                child (nodeMeets read fuel) nodes index rest = some (target nodes) →
                child (nodeMeets read (fuel + extra)) nodes index rest = some (target nodes) := by
              intro fuel extra nodes completed
              cases present : nodes[index]? with
              | none => simpa [child, present] using completed
              | some next =>
                  simpa only [child, present] using
                    fuel_stable read fuel extra rest next (target nodes) (by simpa [child, present] using completed)
            obtain ⟨fuel, common⟩ := common_fuel
              (fun fuel nodes => child (nodeMeets read fuel) nodes index rest) target stable edges each
            refine ⟨fuel + 1, ?_⟩
            simp only [nodeMeets, dispatch, view, closed, Bool.false_eq_true, ↓reduceIte]
            exact anyKnown_exact (fun nodes => child (nodeMeets read fuel) nodes index rest) target edges common
termination_by (path.length, ranking.rank node)
decreasing_by
  · apply Prod.Lex.right
    exact ranking.decreases node view plain (Bool.eq_false_iff.mpr free)
  · apply Prod.Lex.left
    simp

/-- Every larger fuel amount returns the same ranked source decision. -/
theorem eventually_exact (read : ConstrainedRecursionGate.Read Node) (ranking : UnfoldingRank read)
    (path : Path) (node : Node) :
    ∃ bound, ∀ extra, nodeMeets read (bound + extra) path node = some (total read ranking path node) := by
  obtain ⟨bound, completed⟩ := completes read ranking path node
  exact ⟨bound, fun extra => fuel_stable read bound extra path node _ completed⟩

end MicroCFTA.RankedGateCompletion
