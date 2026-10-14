import MicroCFTA.SourceColdReaderBudget
import MicroCFTA.SourceColdSharedRowsTable

/-!
# Finite stateful cold shared traversal

A cold read either reduces the finite unfinished-Mu budget or retains the
identical cache. In the latter case, a new row reduces the finite unvisited
identity budget. Skipping a known or empty value reduces pending work.
-/
namespace MicroCFTA.SourceColdSharedRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedShallowHeap MergedPhysicalWarmup
open SourceColdUnfoldBudget
open SourcePreparedSharedRows (reference)

/-- Count identities that the source map has not visited. -/
def missing (seen : Rows Symbol Guard) : List Nat → Nat
  | [] => 0
  | identity :: rest => (if (seen identity).isNone then 1 else 0) + missing seen rest

/-- Preserving earlier map entries cannot increase the unvisited identity count. -/
theorem missing_mono (before after : Rows Symbol Guard) (growth : Extends before after) (identities : List Nat) :
    missing after identities ≤ missing before identities := by
  induction identities with
  | nil => exact Nat.le_refl _
  | cons identity rest ih =>
      cases found : before identity with
      | none => cases later : after identity <;> simp [missing, found, later] <;> omega
      | some edges =>
          have later := growth identity edges found
          simpa [missing, found, later] using ih

/-- First insertion of an issued identity strictly reduces its finite unvisited budget. -/
theorem missing_put_lt (seen : Rows Symbol Guard) (identities : List Nat) (identity : Nat)
    (member : identity ∈ identities) (edges : List (EdgeValue Symbol Guard)) (absent : seen identity = none) :
    missing (Cache.put seen identity edges) identities < missing seen identities := by
  induction identities with
  | nil => cases member
  | cons first rest ih =>
      have monotone := missing_mono seen (Cache.put seen identity edges) (put_extends seen identity edges absent) rest
      rcases List.mem_cons.mp member with rfl | member
      · simp [missing, Cache.put, absent]
        omega
      · have shorter := ih member
        by_cases same : first = identity
        · subst first
          simp [missing, Cache.put, absent]
          omega
        · simp only [missing, Cache.put, ite_eq_right same]
          omega

/-- Every available closed worklist in a prepared source cache has a completed actual cold trace. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (inventory : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (covered : Covers before inventory)
    (seen : Rows Symbol Guard) (pending : List (Value Symbol Guard)) (inputs : Inputs before pending) :
    ∃ rows after, Trace before seen pending rows after := by
  cases pending with
  | nil => exact ⟨seen, before, .nil _ _⟩
  | cons value rest =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs before rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
      have advance (identity : Nat) (same : reference value = some identity) :
          ∃ rows after, Trace before seen (value :: rest) rows after := by
        cases present : seen identity with
        | some edges =>
            obtain ⟨rows, after, trace⟩ := complete inventory before facts prepared covered seen rest tail
            exact ⟨rows, after, .known value identity edges same present trace⟩
        | none =>
            obtain ⟨fuel, edges, after, done, afterFacts, afterPrepared, growth, history, unchanged, _, _, _⟩ :=
              MergedColdReaderFacts.read_closed value before facts prepared own.1 own.2
            have afterCovered := covered.preserve before after facts inventory unchanged
            have next := next_inputs fuel value before facts prepared own.1 own.2 edges after rest tail done
            have smaller : Prod.Lex (fun (a b : Nat) => a < b)
                (Prod.Lex (fun (a b : Nat) => a < b) (fun (a b : Nat) => a < b))
                (remaining after inventory, missing (Cache.put seen identity edges) (List.range after.nodes.next),
                  (edges.flatMap EdgeValue.children ++ rest).length)
                (remaining before inventory, missing seen (List.range before.nodes.next), (value :: rest).length) := by
              have monotone := remaining_mono before after facts.coherent.valid growth inventory
              by_cases sameBudget : remaining after inventory = remaining before inventory
              · have unchangedCache := SourceColdReaderBudget.nodeEdges_unchanged fuel before facts prepared inventory covered
                  value own.1 edges after done sameBudget
                subst after
                apply Prod.Lex.right
                apply Prod.Lex.left
                exact missing_put_lt seen (List.range before.nodes.next) identity
                  (List.mem_range.mpr (SourcePreparedSharedRows.reference_bounded before facts value own.1 identity same)) edges present
              · apply Prod.Lex.left
                omega
            obtain ⟨rows, final, trace⟩ := complete inventory after afterFacts afterPrepared afterCovered
              (Cache.put seen identity edges) (edges.flatMap EdgeValue.children ++ rest) next
            exact ⟨rows, final, .read value identity fuel edges same present done trace⟩
      cases value with
      | empty =>
          obtain ⟨rows, after, trace⟩ := complete inventory before facts prepared covered seen rest tail
          exact ⟨rows, after, .empty trace⟩
      | reference name => simp [Value.free] at own
      | node entry edges depth free | union entry members depth free | mu entry body depth ordinary =>
          exact advance entry.identity rfl
termination_by (remaining before inventory, missing seen (List.range before.nodes.next), pending.length)
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [List.length_cons, List.length_append, List.length_flatMap]
  all_goals first
    | exact smaller
    | (apply Prod.Lex.right; apply Prod.Lex.right; omega)

/-- The actual initial record inventory derives finite cold execution without warmup or a supplied trace. -/
theorem cold_finite [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (value : Value Symbol Guard)
    (available : Available before value) (closed : value.free = []) :
    ∃ rows after outer inner, Trace before (fun _ => none) [value] rows after ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner before (fun _ => none) [value] = .done rows after := by
  obtain ⟨rows, after, trace⟩ := complete (InternedRecordCoherence.nodeInventory before) before facts prepared
    (initial_covers before facts) (fun _ => none) [value] (by
      intro child member
      rw [List.mem_singleton.mp member]
      exact ⟨available, closed⟩)
  obtain ⟨outer, inner, done⟩ := trace.finite
  exact ⟨rows, after, outer, inner, trace, done⟩

end MicroCFTA.SourceColdSharedRows
