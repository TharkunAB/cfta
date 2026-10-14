import MicroCFTA.SourceFreshOrdinaryColdSharedRows
import MicroCFTA.MergedFreshOrdinaryColdBudget

/-!
# Finite general repaired shared-row traversal

The shared worklist uses actual repaired cold reads. An allocating read
reduces the finite unfinished-Mu degree vector. An unchanged cache lets the
new row consume an unvisited issued identity. Known rows consume pending
work. These priorities give a finite trace without preparation.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdSharedTermination
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedMuDepthInventory (Bounded)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows Inputs missing missing_put_lt)
open SourcePreparedSharedRows (reference)
open SourceFreshOrdinaryColdSharedRows (Trace)

noncomputable section

/-- Prioritize unfinished Mu degrees, then missing rows, then pending length. -/
def measure [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (state : State Symbol Guard)
    (seen : Rows Symbol Guard) (pending : List (Value Symbol Guard)) : (Fin limit → Nat) × Nat × Nat :=
  (fun index => InternedFreshMuUnfoldBudget.count state index,
    missing seen (List.range state.nodes.next), pending.length)

local instance (limit : Nat) : WellFoundedRelation (Fin limit → Nat) :=
  ⟨HeightOrder.VectorBelow limit, HeightOrder.vector_wellFounded limit⟩

/-- Every available closed shared worklist has a finite actual trace, including new Mu allocations. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before) (heap : InternedOpenDepthReadback.Heap before)
    (bounded : Bounded before limit) (seen : Rows Symbol Guard) (pending : List (Value Symbol Guard))
    (inputs : Inputs before pending) :
    ∃ rows after, Trace before seen pending rows after ∧ InternedOpenDepthReadback.Heap after ∧ Bounded after limit := by
  cases pending with
  | nil => exact ⟨seen, before, .nil _ _, heap, bounded⟩
  | cons value rest =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs before rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
      have advance (identity : Nat) (same : reference value = some identity) :
          ∃ rows after, Trace before seen (value :: rest) rows after ∧ InternedOpenDepthReadback.Heap after ∧ Bounded after limit := by
        cases present : seen identity with
        | some edges =>
            obtain ⟨rows, after, trace, afterHeap, afterBounded⟩ := complete limit before semantic covered heap bounded seen rest tail
            exact ⟨rows, after, .known value identity edges same present trace, afterHeap, afterBounded⟩
        | none =>
            obtain ⟨fuel, edges, after, done, afterSemantic, afterCovered, afterHeap, growth, history, resident, closedEdges, _⟩ :=
              MergedFreshOrdinaryColdTermination.read_closed value before semantic covered heap own.1 own.2
            obtain ⟨_, afterBounded, progress⟩ := MergedFreshOrdinaryColdBudget.nodeEdges_progress fuel limit value before
              semantic covered heap bounded own.1 own.2 edges after done
            have next : Inputs after (edges.flatMap EdgeValue.children ++ rest) := by
              intro child member
              rcases List.mem_append.mp member with first | later
              · obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp first
                exact ⟨afterSemantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge edgeIn) child childIn,
                  closedEdges edge edgeIn child childIn⟩
              · exact ⟨(tail child later).1.grows before after growth history, (tail child later).2⟩
            have smaller : Prod.Lex (HeightOrder.VectorBelow limit) (Prod.Lex Nat.lt Nat.lt)
                (measure limit after (Cache.put seen identity edges) (edges.flatMap EdgeValue.children ++ rest))
                (measure limit before seen (value :: rest)) := by
              rcases progress with strict | sameCache
              · exact .left _ _ strict
              · subst after
                apply Prod.Lex.right
                apply Prod.Lex.left
                exact missing_put_lt seen (List.range before.nodes.next) identity
                  (List.mem_range.mpr (SourcePreparedSharedRows.reference_bounded before semantic.1.normal.facts value own.1 identity same)) edges present
            obtain ⟨rows, final, trace, finalHeap, finalBounded⟩ := complete limit after afterSemantic afterCovered afterHeap afterBounded
              (Cache.put seen identity edges) (edges.flatMap EdgeValue.children ++ rest) next
            exact ⟨rows, final, .read value identity fuel edges same present done trace, finalHeap, finalBounded⟩
      cases value with
      | empty =>
          obtain ⟨rows, after, trace, afterHeap, afterBounded⟩ := complete limit before semantic covered heap bounded seen rest tail
          exact ⟨rows, after, .empty trace, afterHeap, afterBounded⟩
      | reference name => simp [Value.free] at own
      | node entry edges depth free | union entry members depth free | mu entry body depth ordinary => exact advance entry.identity rfl
termination_by measure limit before seen pending
decreasing_by
  all_goals simp_wf
  all_goals simp_all only
  all_goals first
    | exact smaller
    | (apply Prod.Lex.right; apply Prod.Lex.right; change rest.length < rest.length + 1; omega)

/-- The actual initial inventory gives stable finite execution bounds for the whole repaired shared traversal. -/
theorem cold_finite [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before) (heap : InternedOpenDepthReadback.Heap before)
    (value : Value Symbol Guard) (available : Available before value) (closed : value.free = []) :
    ∃ rows after outer inner, Trace before (fun _ => none) [value] rows after ∧ InternedOpenDepthReadback.Heap after ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner before (fun _ => none) [value] = .done rows after := by
  obtain ⟨rows, after, trace, afterHeap, _⟩ := complete (maximumDepth (nodeInventory before) + 1) before semantic covered heap
    (InternedMuDepthInventory.initial_bounded before semantic.1.normal.facts) (fun _ => none) [value]
    (by intro child member; simpa only [List.mem_singleton.mp member] using And.intro available closed)
  obtain ⟨outer, inner, stable⟩ := trace.finite
  exact ⟨rows, after, outer, inner, trace, afterHeap, stable⟩

/-- Actual closed source construction derives every cache premise of finite repaired shared traversal. -/
theorem constructed_cold_finite [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) :
    ∃ rows after outer inner, Trace state (fun _ => none) [value] rows after ∧ InternedOpenDepthReadback.Heap after ∧
      ∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner state (fun _ => none) [value] = .done rows after := by
  have heap : InternedOpenDepthReadback.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  exact cold_finite state (SourceRecursiveIntersectionSemanticHeap.constructed expression value state built)
    (InternedFreshOrdinaryCoverage.closed_covered expression value state built) heap value
    ((InternedFreshOrdinaryFacts.closed_verified expression).result value state built)
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built)

end
end MicroCFTA.SourceFreshOrdinaryColdSharedTermination
