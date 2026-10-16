import MicroCFTA.SourceCurrentHereditaryConstruction
import MicroCFTA.SourceEqualityRequiredHead

/-!
# Local annotations through actual recursive row exposure

Each completed read uses its actual unfolding and ordered worklist. The
conditional Mu certificates follow the same returned cache. Only annotations
of the supplied value and its actual replacements are used. Other resident
edge guards remain unrestricted.
-/
namespace MicroCFTA.SourceCurrentHereditaryExposure
open InternedRecordCoherence
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome)
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryConstructors (Edge)
open SourceCurrentHereditaryConstruction (MuStored)
open MergedFreshOrdinaryExposure
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedSourceExposure (Result)

private theorem prepend_done (result : Result Symbol Guard) (leading edges : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : result.prepend leading = .done edges after) :
    ∃ suffix, result = .done suffix after ∧ edges = leading ++ suffix := by
  cases result with
  | done suffix state =>
      obtain ⟨rfl, rfl⟩ := Result.done.inj done
      exact ⟨suffix, rfl, rfl⟩
  | unresolved | pending | exhausted => cases done

private theorem canonical_done (result : Result Symbol Guard) (edges : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : result.canonical = .done edges after) :
    ∃ original, result = .done original after ∧ edges = canonicalEdges original := by
  cases result with
  | done original state =>
      obtain ⟨rfl, rfl⟩ := Result.done.inj done
      exact ⟨original, rfl, rfl⟩
  | unresolved | pending | exhausted => cases done

/-- A completed actual cold worklist retains its causal store and every returned row annotation. -/
theorem collect [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (fuel : Nat)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values state pending)
    (closed : ClosedValues pending) (annotated : ∀ value ∈ pending, Annotated valid value)
    (stored : MuStored valid state) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.collect fuel state seen pending = .done edges after) :
    MuStored valid after ∧ ∀ edge ∈ edges, Edge valid edge := by
  induction fuel generalizing state seen pending edges after with
  | zero =>
      cases pending with
      | nil =>
          obtain ⟨rfl, rfl⟩ := Result.done.inj done
          exact ⟨stored, by intro edge member; cases member⟩
      | cons => cases done
  | succ fuel ih =>
      cases pending with
      | nil =>
          obtain ⟨rfl, rfl⟩ := Result.done.inj done
          exact ⟨stored, by intro edge member; cases member⟩
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have valueClosed := closed value List.mem_cons_self
          have valueAnnotated := annotated value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have restClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
          have restAnnotated : ∀ child ∈ rest, Annotated valid child := fun child member =>
            annotated child (List.mem_cons_of_mem _ member)
          have facts := semantic.1.normal.facts
          cases value with
          | empty => exact ih state semantic covered seen rest restInputs restClosed restAnnotated stored edges after done
          | reference name => cases done
          | node entry rows depth free =>
              obtain ⟨suffix, returned, same⟩ := prepend_done _ rows edges after done
              have tail := ih state semantic covered seen rest restInputs restClosed restAnnotated stored suffix after returned
              refine ⟨tail.1, ?_⟩
              intro edge member
              rw [same] at member
              rcases List.mem_append.mp member with original | later
              · exact SourceCurrentHereditaryConstructors.node_edge valueAnnotated edge original
              · exact tail.2 edge later
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · have tail : MergedFreshOrdinaryExposure.collect fuel state seen rest = .done edges after := by
                  simpa only [MergedFreshOrdinaryExposure.collect, visited, ↓reduceIte] using done
                exact ih state semantic covered seen rest restInputs restClosed restAnnotated stored edges after tail
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with original | later
                  · exact available.children child original
                  · exact restInputs child later
                have nextClosed : ClosedValues (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with original | later
                  · exact MergedColdReaderClosed.union_members_closed state facts entry members depth free available valueClosed child original
                  · exact restClosed child later
                have nextAnnotated : ∀ child ∈ members ++ rest, Annotated valid child := by
                  intro child member
                  rcases List.mem_append.mp member with original | later
                  · exact SourceCurrentHereditaryUnconstrained.union_member valueAnnotated child original
                  · exact restAnnotated child later
                have tail : MergedFreshOrdinaryExposure.collect fuel state (entry.identity :: seen) (members ++ rest) = .done edges after := by
                  simpa only [MergedFreshOrdinaryExposure.collect, visited, ↓reduceIte] using done
                exact ih state semantic covered (entry.identity :: seen) (members ++ rest)
                  nextInputs nextClosed nextAnnotated stored edges after tail
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · have tail : MergedFreshOrdinaryExposure.collect fuel state seen rest = .done edges after := by
                  simpa only [MergedFreshOrdinaryExposure.collect, visited, ↓reduceIte] using done
                exact ih state semantic covered seen rest restInputs restClosed restAnnotated stored edges after tail
              · have checked := SourceCurrentHereditaryConstruction.unfold valid (.mu entry body depth ordinary)
                  state facts available valueAnnotated stored
                obtain ⟨result, middle, unfolded, context, heap, nextCovered, resultAvailable, growth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    state semantic.1 available semantic.2 covered
                have nextStore : MuStored valid middle := by simpa only [unfolded, Outcome.state] using checked.stored
                have resultAnnotated := checked.result result middle unfolded
                have resultClosed := InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
                  state semantic.1 available valueClosed result middle unfolded
                have nextInputs : Values middle (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact (restInputs child member).grows state middle growth history
                have nextClosed : ClosedValues (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultClosed
                  · exact restClosed child member
                have nextAnnotated : ∀ child ∈ result :: rest, Annotated valid child := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAnnotated
                  · exact restAnnotated child member
                have tail : MergedFreshOrdinaryExposure.collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges after := by
                  simpa only [MergedFreshOrdinaryExposure.collect, visited, ↓reduceIte, unfolded] using done
                exact ih middle ⟨context, heap⟩ nextCovered (entry.identity :: seen) (result :: rest)
                  nextInputs nextClosed nextAnnotated nextStore edges after tail

/-- Actual row normalization follows its own direct Mu read and canonicalized fallback. -/
theorem nodeEdges [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (fuel : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (available : Available state value) (closed : value.free = [])
    (annotated : Annotated valid value) (stored : MuStored valid state)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges after) :
    MuStored valid after ∧ ∀ edge ∈ edges, Edge valid edge := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (rootAvailable : Available current root) (rootClosed : root.free = [])
      (rootAnnotated : Annotated valid root) (currentStore : MuStored valid current)
      (actual : (MergedFreshOrdinaryExposure.collect fuel current [] [root]).canonical = .done edges after) :
      MuStored valid after ∧ ∀ edge ∈ edges, Edge valid edge := by
    obtain ⟨original, raw, same⟩ := canonical_done _ edges after actual
    have checked := collect valid fuel current currentSemantic currentCovered [] [root]
      (by intro value member; exact (List.mem_singleton.mp member) ▸ rootAvailable)
      (by intro value member; exact (List.mem_singleton.mp member) ▸ rootClosed)
      (by intro value member; exact (List.mem_singleton.mp member) ▸ rootAnnotated)
      currentStore original after raw
    exact ⟨checked.1, fun edge member => checked.2 edge (canonicalEdges_member original edge (same ▸ member))⟩
  cases value with
  | empty | reference =>
      obtain ⟨rfl, rfl⟩ := Result.done.inj done
      exact ⟨stored, by intro edge member; cases member⟩
  | node entry rows depth free =>
      obtain ⟨rfl, rfl⟩ := Result.done.inj done
      exact ⟨stored, fun edge member => SourceCurrentHereditaryConstructors.node_edge annotated edge member⟩
  | union entry members depth free => exact fallback _ state semantic covered available closed annotated stored done
  | mu entry body depth ordinary =>
      have checked := SourceCurrentHereditaryConstruction.unfold valid (.mu entry body depth ordinary)
        state semantic.1.normal.facts available annotated stored
      obtain ⟨result, middle, unfolded, context, heap, nextCovered, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have nextStore : MuStored valid middle := by simpa only [unfolded, Outcome.state] using checked.stored
      have resultAnnotated := checked.result result middle unfolded
      have originalAvailable := available.grows state middle growth history
      cases result with
      | node entry rows depth free =>
          simp only [MergedFreshOrdinaryExposure.nodeEdges, unfolded] at done
          obtain ⟨rfl, rfl⟩ := Result.done.inj done
          exact ⟨nextStore, fun edge member => SourceCurrentHereditaryConstructors.node_edge resultAnnotated edge member⟩
      | empty | reference | union | mu =>
          apply fallback (.mu entry body depth ordinary) middle ⟨context, heap⟩ nextCovered
            originalAvailable closed annotated nextStore
          simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded] using done

/-- A supplied actual head graph derives its local output without a global guard heap. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : SourceEqualityRequiredHead.Head value before result after) (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = []) (annotated : Annotated valid value)
    (stored : MuStored valid before) : MuStored valid after ∧ Annotated valid result := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      have localRows := nodeEdges valid fuel value before ready.semantic ready.covered available closed annotated stored edges middle exposed
      have physical := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value before ready.semantic ready.covered available closed
      have resident := physical.edges edges middle exposed
      have semantic := physical.semantic
      have middleFacts : Facts middle := by simpa only [exposed, Result.state] using semantic.1.normal.facts
      constructor
      · simpa only [rebuilt] using localRows.1.makeNode edges
      · simpa only [rebuilt] using SourceCurrentHereditaryConstructors.makeNode valid edges middle
          middleFacts.coherent middleFacts.linked resident localRows.2

end MicroCFTA.SourceCurrentHereditaryExposure
