import MicroCFTA.EndpointRecursionGate
import MicroCFTA.RankedGateCompletion

/-!
# Completion of the endpoint-descendant gate

The pure gate uses the policy from main 24a710a3. Its endpoint predicate is
an explicit Boolean read. The existing rank controls same-path unfolding.
This module does not interpret the source predicate or its global memo.
-/
namespace MicroCFTA.EndpointGateCompletion
open Language EqualityNormalize EndpointRecursionGate
open RecursiveReductionBarrier (finite)
open ConstrainedRecursionGate (UnfoldingRank anyKnown child)
open RankedGateCompletion (common_fuel anyKnown_exact)

/-- The total gate retains the current endpoint rule and source dispatch order. -/
def total (read : Read Node) (ranking : UnfoldingRank read.previous)
    (path : Path) (node : Node) : Bool :=
  match _view : read.view node with
  | .reference | .union => true
  | _ =>
      if finite read.toRead node then false
      else match _binder : read.view node with
        | .binder =>
            if _plain : read.unconstrained node then
              if _closed : (read.free node).isEmpty then false
              else total read ranking path (read.unfold node)
            else true
        | _ => match path with
            | [] => !(read.free node).isEmpty || read.reaches node
            | index :: rest => match read.view node with
                | .branches edges => edges.any (fun nodes =>
                    match nodes[index]? with
                    | none => false
                    | some next => total read ranking rest next)
                | _ => false
termination_by (path.length, ranking.rank node)
decreasing_by
  · apply Prod.Lex.right
    exact ranking.decreases node _binder _plain (Bool.eq_false_iff.mpr _closed)
  · apply Prod.Lex.left
    simp

/-- Each ranked gate query has a finite completed instrumented execution. -/
theorem completes (read : Read Node) (ranking : UnfoldingRank read.previous)
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

/-- All larger fuel amounts return the same total gate decision. -/
theorem eventually_exact (read : Read Node) (ranking : UnfoldingRank read.previous)
    (path : Path) (node : Node) :
    ∃ bound, ∀ extra, nodeMeets read (bound + extra) path node = some (total read ranking path node) := by
  obtain ⟨bound, completed⟩ := completes read ranking path node
  exact ⟨bound, fun extra => fuel_stable read bound extra path node _ completed⟩

/-- Any completed instrumented query agrees with the ranked total worker. -/
theorem completed_agrees (read : Read Node) (ranking : UnfoldingRank read.previous)
    (fuel : Nat) (path : Path) (node : Node) (result : Bool)
    (completed : nodeMeets read fuel path node = some result) :
    total read ranking path node = result := by
  obtain ⟨bound, exact⟩ := completes read ranking path node
  have first := fuel_stable read fuel bound path node result completed
  have second := fuel_stable read bound fuel path node _ exact
  have same : some result = some (total read ranking path node) :=
    first.symm.trans (by simpa only [Nat.add_comm] using second)
  exact Option.some.inj same.symm

/-- A total equality-path check starts below the edge root. -/
def totalMeets (read : Read Node) (ranking : UnfoldingRank read.previous)
    (nodes : List Node) : Path → Bool
  | [] => false
  | index :: rest => match nodes[index]? with
      | none => false
      | some node => total read ranking rest node

/-- The total class decision uses the original path order. -/
def totalClass (read : Read Node) (ranking : UnfoldingRank read.previous)
    (nodes : List Node) (paths : Class) : Bool :=
  paths.any (totalMeets read ranking nodes)

/-- A completed path check agrees with its total decision. -/
theorem meets_completed_agrees (read : Read Node) (ranking : UnfoldingRank read.previous)
    (fuel : Nat) (nodes : List Node) (path : Path) (result : Bool)
    (completed : meets read fuel nodes path = some result) :
    totalMeets read ranking nodes path = result := by
  cases path with
  | nil => simpa [meets, totalMeets] using completed
  | cons index rest =>
      cases present : nodes[index]? with
      | none => simpa [meets, child, totalMeets, present] using completed
      | some node =>
          simpa only [totalMeets, present] using completed_agrees read ranking fuel rest node result
            (by simpa [meets, child, present] using completed)

/-- Every total path decision has a finite completed instrumented check. -/
theorem meets_completes (read : Read Node) (ranking : UnfoldingRank read.previous)
    (nodes : List Node) (path : Path) :
    ∃ fuel, meets read fuel nodes path = some (totalMeets read ranking nodes path) := by
  cases path with
  | nil => exact ⟨0, rfl⟩
  | cons index rest =>
      cases present : nodes[index]? with
      | none => exact ⟨0, by simp [meets, child, totalMeets, present]⟩
      | some node =>
          obtain ⟨fuel, completed⟩ := completes read ranking rest node
          exact ⟨fuel, by simpa [meets, child, totalMeets, present] using completed⟩

/-- Additional fuel preserves a completed path check. -/
theorem meets_fuel_stable (read : Read Node) (fuel extra : Nat) (nodes : List Node)
    (path : Path) (result : Bool) (completed : meets read fuel nodes path = some result) :
    meets read (fuel + extra) nodes path = some result := by
  cases path with
  | nil => exact completed
  | cons index rest =>
      cases present : nodes[index]? with
      | none => simpa [meets, child, present] using completed
      | some node =>
          simpa only [meets, child, present] using fuel_stable read fuel extra rest node result
            (by simpa [meets, child, present] using completed)

/-- Completed class checks agree without assumptions on unvisited paths. -/
theorem class_completed_agrees (read : Read Node) (ranking : UnfoldingRank read.previous)
    (fuel : Nat) (nodes : List Node) (paths : Class) (result : Bool)
    (completed : classMeets read fuel nodes paths = some result) :
    totalClass read ranking nodes paths = result :=
  ConstrainedRecursionGate.anyKnown_agrees _ _
    (fun path result found => meets_completed_agrees read ranking fuel nodes path result found)
    paths result completed

/-- Each finite class has a common fuel amount for its total decision. -/
theorem class_completes (read : Read Node) (ranking : UnfoldingRank read.previous)
    (nodes : List Node) (paths : Class) :
    ∃ fuel, classMeets read fuel nodes paths = some (totalClass read ranking nodes paths) := by
  obtain ⟨fuel, common⟩ := common_fuel
    (fun fuel path => meets read fuel nodes path) (totalMeets read ranking nodes)
    (fun fuel extra path completed => meets_fuel_stable read fuel extra nodes path _ completed)
    paths (fun path _ => meets_completes read ranking nodes path)
  exact ⟨fuel, anyKnown_exact _ _ paths common⟩

end MicroCFTA.EndpointGateCompletion
