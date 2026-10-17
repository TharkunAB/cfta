import MicroCFTA.SourceCurrentHereditaryExposure
import MicroCFTA.SourceCurrentConstrainedCapPaths

/-!
# Initial signed masks through actual recursive row exposure

The actual worklist retains the same signed path at its returned heap.
A Mu boundary uses its hereditary annotation and the causal Mu store.
Other resident values can have unrelated guards. Each theorem uses the
actual completed read. No theorem assumes its returned path mask.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapPathExposure
open InternedRecordCoherence
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome)
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCapPaths (Supported)
open SourceEqualityProjectionGraph (select)
open SourceCurrentHereditaryConstruction (MuStored)
open MergedFreshOrdinaryExposure
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedSourceExposure (Result)

/-- A returned row checks only the actual signed child selected by the initial path. -/
def Row (valid : Guard → Prop) (index : Int) (path : List Int) (edge : EdgeValue Symbol Guard) : Prop :=
  ∀ child, select edge.children index = some child → Supported valid path child

/-- Actual canonical node work retains the same path mask of its supplied rows. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (index : Int) (path : List Int)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) (resident : Edges state edges)
    (supported : ∀ edge ∈ edges, Row valid index path edge) :
    Supported valid (index :: path) (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have selected : Edges state (canonicalEdges (surviving edges)) :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have masked : ∀ edge ∈ canonicalEdges (surviving edges), Row valid index path edge :=
    fun edge member => supported edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold InternedConstructorTemplates.makeNode
  dsimp only
  split
  · exact .plain _ .empty
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [Edges, same] using selected)
    simp only [run, exactResult, identifyNode]
    exact Supported.node index path entry _ _ _ (by simpa only [Row, same] using masked)

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

/-- A completed actual cold worklist retains its causal store and every returned row mask. -/
theorem collect [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (index : Int) (path : List Int) (fuel : Nat)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values state pending)
    (closed : ClosedValues pending) (annotated : ∀ value ∈ pending, Supported valid (index :: path) value)
    (stored : MuStored valid state) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.collect fuel state seen pending = .done edges after) :
    MuStored valid after ∧ ∀ edge ∈ edges, Row valid index path edge := by
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
          have restAnnotated : ∀ child ∈ rest, Supported valid (index :: path) child := fun child member =>
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
              · exact valueAnnotated.node_selected edge original
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
                have nextAnnotated : ∀ child ∈ members ++ rest, Supported valid (index :: path) child := by
                  intro child member
                  rcases List.mem_append.mp member with original | later
                  · exact valueAnnotated.union_member child original
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
                  state facts available ((SourceCurrentConstrainedCapPaths.binder_iff valid (index :: path) entry body depth ordinary).mp valueAnnotated) stored
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
                have nextAnnotated : ∀ child ∈ result :: rest, Supported valid (index :: path) child := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact Supported.plain (index :: path) resultAnnotated
                  · exact restAnnotated child member
                have tail : MergedFreshOrdinaryExposure.collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges after := by
                  simpa only [MergedFreshOrdinaryExposure.collect, visited, ↓reduceIte, unfolded] using done
                exact ih middle ⟨context, heap⟩ nextCovered (entry.identity :: seen) (result :: rest)
                  nextInputs nextClosed nextAnnotated nextStore edges after tail

/-- Actual row normalization follows its own direct Mu read and canonicalized fallback. -/
theorem nodeEdges [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (index : Int) (path : List Int) (fuel : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (available : Available state value) (closed : value.free = [])
    (annotated : Supported valid (index :: path) value) (stored : MuStored valid state)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges after) :
    MuStored valid after ∧ ∀ edge ∈ edges, Row valid index path edge := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (rootAvailable : Available current root) (rootClosed : root.free = [])
      (rootAnnotated : Supported valid (index :: path) root) (currentStore : MuStored valid current)
      (actual : (MergedFreshOrdinaryExposure.collect fuel current [] [root]).canonical = .done edges after) :
      MuStored valid after ∧ ∀ edge ∈ edges, Row valid index path edge := by
    obtain ⟨original, raw, same⟩ := canonical_done _ edges after actual
    have checked := collect valid index path fuel current currentSemantic currentCovered [] [root]
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
      exact ⟨stored, fun edge member => annotated.node_selected edge member⟩
  | union entry members depth free => exact fallback _ state semantic covered available closed annotated stored done
  | mu entry body depth ordinary =>
      have checked := SourceCurrentHereditaryConstruction.unfold valid (.mu entry body depth ordinary)
        state semantic.1.normal.facts available ((SourceCurrentConstrainedCapPaths.binder_iff valid (index :: path) entry body depth ordinary).mp annotated) stored
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
          exact ⟨nextStore, fun edge member => (Supported.plain (index :: path) resultAnnotated).node_selected edge member⟩
      | empty | reference | union | mu =>
          apply fallback (.mu entry body depth ordinary) middle ⟨context, heap⟩ nextCovered
            originalAvailable closed annotated nextStore
          simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded] using done

/-- A supplied actual head graph derives its local output at the exact returned heap. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (index : Int) (path : List Int)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : SourceEqualityRequiredHead.Head value before result after) (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = []) (annotated : Supported valid (index :: path) value)
    (stored : MuStored valid before) : MuStored valid after ∧ Supported valid (index :: path) result := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      have localRows := nodeEdges valid index path fuel value before ready.semantic ready.covered available closed annotated stored edges middle exposed
      have physical := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value before ready.semantic ready.covered available closed
      have resident := physical.edges edges middle exposed
      have semantic := physical.semantic
      have middleFacts : Facts middle := by simpa only [exposed, Result.state] using semantic.1.normal.facts
      constructor
      · simpa only [rebuilt] using localRows.1.makeNode edges
      · simpa only [rebuilt] using makeNode valid index path edges middle
          middleFacts.coherent middleFacts.linked resident localRows.2

end MicroCFTA.SourceCurrentConstrainedCapPathExposure
