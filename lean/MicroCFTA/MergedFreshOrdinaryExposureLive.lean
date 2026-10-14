import MicroCFTA.MergedFreshOrdinaryColdEffects

/-!
# Empty-child normalization after repaired exposure

Every exposed edge comes from an ordinary source record. The stored live-edge
invariant excludes empty children. Actual unfolding retains this invariant.
-/
namespace MicroCFTA.MergedFreshOrdinaryExposureLive
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedSourceExposure (Result)
open MergedFreshOrdinaryExposure

/-- Every edge in a returned exposure lacks an empty child. -/
def Live : Result Symbol Guard → Prop
  | .done edges _ => ∀ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false
  | _ => True

/-- Prepending live ordinary edges retains the exposure property. -/
theorem prepend (result : Result Symbol Guard) (live : Live result) (edges : List (EdgeValue Symbol Guard))
    (earlier : ∀ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false) :
    Live (result.prepend edges) := by
  cases result with
  | done values after => exact fun edge member => (List.mem_append.mp member).elim (earlier edge) (live edge)
  | unresolved | pending | exhausted => trivial

/-- Canonical edge ordering retains the same empty-child property. -/
theorem canonical (result : Result Symbol Guard) (live : Live result) : Live result.canonical := by
  cases result with
  | done values after => exact fun edge member => live edge (canonicalEdges_member values edge member)
  | unresolved | pending | exhausted => trivial

/-- The actual repaired closure worklist returns only live ordinary edges. -/
theorem collect_live [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending) (closed : ClosedValues pending) :
    Live (collect fuel state seen pending) := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> simp [collect, Live]
  | succ fuel ih =>
      cases pending with
      | nil => exact fun _ member => False.elim (List.not_mem_nil member)
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have valueClosed := closed value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have restClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state semantic covered seen rest restInputs restClosed
          | reference name => trivial
          | node entry edges depth free =>
              exact prepend _ (ih state semantic covered seen rest restInputs restClosed) edges
                (InternedLiveEdges.resident_live state semantic.1.normal.live (.node entry edges depth free) available.resident)
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic covered seen rest restInputs restClosed
              · have next := ih state semantic covered (entry.identity :: seen) (members ++ rest)
                    (fun child member => (List.mem_append.mp member).elim (available.children child) (restInputs child))
                    (fun child member => (List.mem_append.mp member).elim
                      (MergedColdReaderClosed.union_members_closed state semantic.1.normal.facts entry members depth free available valueClosed child)
                      (restClosed child))
                simpa only [collect, ite_eq_right visited] using next
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic covered seen rest restInputs restClosed
              · obtain ⟨result, after, done, context, heap, finalCovered, resultAvailable, growth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    state semantic.1 available semantic.2 covered
                have resultClosed := InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
                  state semantic.1 available valueClosed result after done
                have next := ih after ⟨context, heap⟩ finalCovered (entry.identity :: seen) (result :: rest)
                  (fun child member => (List.mem_cons.mp member).elim
                    (fun same => same ▸ resultAvailable) (fun later => (restInputs child later).grows state after growth history))
                  (fun child member => (List.mem_cons.mp member).elim (fun same => same ▸ resultClosed) (restClosed child))
                simpa only [collect, ite_eq_right visited, done] using next

/-- Every actual direct or closure reader path excludes empty children in its returned edges. -/
theorem nodeEdges_live [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (available : Available state value) (closed : value.free = []) : Live (nodeEdges fuel value state) := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (root : Value Symbol Guard)
      (rootAvailable : Available current root) (rootClosed : root.free = []) :
      Live (collect fuel current [] [root]).canonical :=
    canonical _ (collect_live fuel current currentSemantic currentCovered [] [root]
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootClosed))
  cases value with
  | empty | reference => exact fun _ member => False.elim (List.not_mem_nil member)
  | node entry edges depth free =>
      exact InternedLiveEdges.resident_live state semantic.1.normal.live _ available.resident
  | union entry members depth free => exact fallback state semantic covered _ available closed
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, context, heap, finalCovered, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have next := fallback after ⟨context, heap⟩ finalCovered _ (available.grows state after growth history) closed
      cases result with
      | node entry edges depth free =>
          simpa only [nodeEdges, done, Live, InternedLiveEdges.ValueLive, InternedEdgeResidency.nodeEdges] using
            InternedLiveEdges.resident_live after context.normal.live (.node entry edges depth free) resultAvailable.resident
      | empty | reference | union | mu => simpa only [nodeEdges, done] using next

end MicroCFTA.MergedFreshOrdinaryExposureLive
