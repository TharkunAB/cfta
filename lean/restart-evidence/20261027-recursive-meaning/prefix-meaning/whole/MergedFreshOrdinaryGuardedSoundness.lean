import MicroCFTA.MergedFreshOrdinaryGuardedEffects

/-!
# Independent-language soundness of actual repaired cold reads

Each returned constructor edge denotes only terms accepted by an original
root. The proof follows actual cache growth and exact unfolding languages.
Skipping a visited root is sound. Completeness needs a separate leastness law.
-/
namespace MicroCFTA.MergedFreshOrdinaryGuardedSoundness
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage InternedGuardedProbeHeap
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)

/-- A stored ordinary node contains the independent language of each actual edge. -/
theorem edge_into_node (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Guard) (member : edge ∈ edges)
    (term : Term Symbol) (accepted : edgeMeaning holds ambient edge term) :
    meaning holds ambient (.node entry edges depth free) term := by
  rw [meaning]
  exact ⟨⟨edge, member⟩, accepted⟩

/-- Every constructor edge returned by the actual growing-cache worklist is sound for one original root. -/
theorem collect_sound [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : Heap state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) (closed : ClosedValues pending) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : collect fuel state seen pending = .done edges after) :
    ∀ edge ∈ edges, ∀ term, edgeMeaning holds ambient edge term → ∃ value ∈ pending, meaning holds ambient value term := by
  induction fuel generalizing state seen pending edges after with
  | zero =>
      cases pending with
      | nil => cases done; simp
      | cons => cases done
  | succ fuel ih =>
      cases pending with
      | nil => cases done; simp
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have valueClosed := closed value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have restClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
          have restore (value : Value Symbol Guard) (term : Term Symbol)
              (accepted : ∃ child ∈ rest, meaning holds ambient child term) :
              ∃ child ∈ value :: rest, meaning holds ambient child term := by
            obtain ⟨child, member, accepted⟩ := accepted
            exact ⟨child, List.mem_cons_of_mem _ member, accepted⟩
          cases value with
          | empty =>
              intro edge member term accepted
              exact restore .empty term (ih state semantic covered heap seen rest restInputs restClosed edges after done edge member term accepted)
          | reference => cases done
          | node entry own depth free =>
              cases tailDone : collect fuel state seen rest with
              | unresolved | pending | exhausted => simp only [collect, tailDone, Result.prepend] at done; cases done
              | done values final =>
                  have same : own ++ values = edges ∧ final = after := by
                    simpa only [collect, tailDone, Result.prepend, Result.done.injEq] using done
                  cases same.2
                  rw [← same.1]
                  intro edge member term accepted
                  rcases List.mem_append.mp member with ownMember | restMember
                  · exact ⟨_, List.mem_cons_self, edge_into_node holds ambient entry own depth free edge ownMember term accepted⟩
                  · exact restore _ term (ih state semantic covered heap seen rest restInputs restClosed values after tailDone edge restMember term accepted)
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · have tailDone : collect fuel state seen rest = .done edges after := by
                  simpa only [collect, ite_eq_left visited] using done
                intro edge member term accepted
                exact restore _ term (ih state semantic covered heap seen rest restInputs restClosed edges after tailDone edge member term accepted)
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                have nextClosed : ClosedValues (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact MergedColdReaderClosed.union_members_closed state semantic.1.normal.facts entry members depth free available valueClosed child first
                  · exact restClosed child later
                have nextDone : collect fuel state (entry.identity :: seen) (members ++ rest) = .done edges after := by
                  simpa only [collect, ite_eq_right visited] using done
                intro edge member term accepted
                obtain ⟨child, source, accepted⟩ := ih state semantic covered heap (entry.identity :: seen)
                  (members ++ rest) nextInputs nextClosed edges after nextDone edge member term accepted
                rcases List.mem_append.mp source with first | later
                · refine ⟨_, List.mem_cons_self, ?_⟩
                  rw [meaning]
                  exact ⟨⟨child, first⟩, accepted⟩
                · exact ⟨child, List.mem_cons_of_mem _ later, accepted⟩
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · have tailDone : collect fuel state seen rest = .done edges after := by
                  simpa only [collect, ite_eq_left visited] using done
                intro edge member term accepted
                exact restore _ term (ih state semantic covered heap seen rest restInputs restClosed edges after tailDone edge member term accepted)
              · have checked := InternedGuardedStoredExecution.unfold_checked (.mu entry body depth ordinary) state semantic.1 heap available
                obtain ⟨result, middle, unfolded, context, cached, finalCovered, resultAvailable, growth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    state semantic.1 available semantic.2 covered
                have afterHeap : Heap middle := by simpa only [unfolded, InternedNestedConstruction.Outcome.state] using checked.heap
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
                have nextDone : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges after := by
                  simpa only [collect, ite_eq_right visited, unfolded] using done
                intro edge member term accepted
                obtain ⟨child, source, accepted⟩ := ih middle ⟨context, cached⟩ finalCovered afterHeap (entry.identity :: seen)
                  (result :: rest) nextInputs nextClosed edges after nextDone edge member term accepted
                rcases List.mem_cons.mp source with rfl | later
                · exact ⟨_, List.mem_cons_self, (checked.result _ middle unfolded holds ambient) ▸ accepted⟩
                · exact ⟨child, List.mem_cons_of_mem _ later, accepted⟩

/-- Public actual cold exposure returns only independently accepted guarded constructor edges. -/
theorem nodeEdges_sound [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (heap : Heap state) (available : Available state value) (closed : value.free = [])
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : nodeEdges fuel value state = .done edges after) :
    ∀ edge ∈ edges, ∀ term, edgeMeaning holds ambient edge term → meaning holds ambient value term := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (currentHeap : Heap current) (input : Available current root)
      (rootClosed : root.free = []) (completed : (collect fuel current [] [root]).canonical = .done edges after) :
      ∀ edge ∈ edges, ∀ term, edgeMeaning holds ambient edge term → meaning holds ambient root term := by
    cases readDone : collect fuel current [] [root] with
    | unresolved | pending | exhausted => simp only [readDone, Result.canonical] at completed; cases completed
    | done values final =>
        have same : canonicalEdges values = edges ∧ final = after := by
          simpa only [readDone, Result.canonical, Result.done.injEq] using completed
        cases same.2
        intro edge member term accepted
        obtain ⟨source, included, accepted⟩ := collect_sound holds ambient fuel current currentSemantic currentCovered currentHeap [] [root]
          (by intro value member; rw [List.mem_singleton.mp member]; exact input)
          (by intro value member; rw [List.mem_singleton.mp member]; exact rootClosed)
          values after readDone edge (canonicalEdges_member values edge (same.1 ▸ member)) term accepted
        simpa only [List.mem_singleton.mp included] using accepted
  cases value with
  | empty | reference => cases done; simp
  | node entry own depth free =>
      cases done
      exact fun edge member term accepted => edge_into_node holds ambient entry edges depth free edge member term accepted
  | union => exact fallback _ state semantic covered heap available closed done
  | mu entry body depth ordinary =>
      have checked := InternedGuardedStoredExecution.unfold_checked (.mu entry body depth ordinary) state semantic.1 heap available
      obtain ⟨result, middle, unfolded, context, cached, finalCovered, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have afterHeap : Heap middle := by simpa only [unfolded, InternedNestedConstruction.Outcome.state] using checked.heap
      have rootAvailable := available.grows state middle growth history
      cases result with
      | node actual own level free =>
          have same : own = edges ∧ middle = after := by
            simpa only [nodeEdges, unfolded, Result.done.injEq] using done
          cases same.2
          intro edge member term accepted
          rw [← same.1] at member
          exact (checked.result _ after unfolded holds ambient) ▸ edge_into_node holds ambient actual own level free edge member term accepted
      | empty | reference | union | mu =>
          apply fallback _ middle ⟨context, cached⟩ finalCovered afterHeap rootAvailable closed
          simpa only [nodeEdges, unfolded] using done

end MicroCFTA.MergedFreshOrdinaryGuardedSoundness
