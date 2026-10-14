import MicroCFTA.MergedFreshOrdinaryGraph

/-!
# Constructor origins of actual repaired cold reads

Each returned edge has an actual repaired epsilon path from a requested
root in every cache that extends the final cache. The proof follows actual
ordered effects and uses exact unfolding replay after cache growth.
-/
namespace MicroCFTA.MergedFreshOrdinaryExposureOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedConstruction
open InternedRecordCoherence InternedNestedFacts InternedNestedProvenance
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open MergedFreshOrdinaryGraph
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open Productivity

/-- Each returned edge has a source path in every later extension of the actual returned cache. -/
theorem collect_origins [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : collect fuel state seen pending = .done edges after)
    (view : State Symbol Guard) (growth : Grows after view) :
    ∀ edge ∈ edges, Origin view pending edge := by
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
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have tailSeeds : ∀ child ∈ rest, Reachable (successors view) (value :: rest) child :=
            fun child member => .seed (List.mem_cons_of_mem _ member)
          cases value with
          | empty =>
              intro edge member
              exact (ih state semantic covered seen rest restInputs edges after done growth edge member).from_seeds
                view rest (.empty :: rest) tailSeeds edge
          | reference name => cases done
          | node entry own depth free =>
              cases tailDone : collect fuel state seen rest with
              | unresolved | pending | exhausted => simp only [collect, tailDone, Result.prepend] at done; cases done
              | done values final =>
                  have same : own ++ values = edges ∧ final = after := by
                    simpa only [collect, tailDone, Result.prepend, Result.done.injEq] using done
                  cases same.2
                  rw [← same.1]
                  intro edge member
                  rcases List.mem_append.mp member with ownMember | restMember
                  · exact ⟨_, .seed List.mem_cons_self, ownMember⟩
                  · exact (ih state semantic covered seen rest restInputs values after tailDone growth edge restMember).from_seeds
                      view rest _ tailSeeds edge
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · have tailDone : collect fuel state seen rest = .done edges after := by
                  simpa only [collect, ite_eq_left visited] using done
                intro edge member
                exact (ih state semantic covered seen rest restInputs edges after tailDone growth edge member).from_seeds
                  view rest _ tailSeeds edge
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                have nextDone : collect fuel state (entry.identity :: seen) (members ++ rest) = .done edges after := by
                  simpa only [collect, ite_eq_right visited] using done
                intro edge member
                apply (ih state semantic covered (entry.identity :: seen) (members ++ rest) nextInputs edges after nextDone growth edge member).from_seeds
                  view (members ++ rest) _ ?_ edge
                intro child member
                rcases List.mem_append.mp member with first | later
                · exact .step (.seed List.mem_cons_self) first
                · exact tailSeeds child later
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · have tailDone : collect fuel state seen rest = .done edges after := by
                  simpa only [collect, ite_eq_left visited] using done
                intro edge member
                exact (ih state semantic covered seen rest restInputs edges after tailDone growth edge member).from_seeds
                  view rest _ tailSeeds edge
              · obtain ⟨result, middle, unfolded, middleContext, middleHeap, middleCovered, resultAvailable, firstGrowth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    state semantic.1 available semantic.2 covered
                have nextInputs : Values middle (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact (restInputs child member).grows state middle firstGrowth history
                have nextDone : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges after := by
                  simpa only [collect, ite_eq_right visited, unfolded] using done
                have later : Grows middle after := by
                  simpa only [nextDone, Result.state] using
                    (MergedFreshOrdinaryColdReplay.collect_correct fuel middle middleContext.normal.facts.coherent.valid
                      (entry.identity :: seen) (result :: rest)).2
                have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay (.mu entry body depth ordinary) state view result middle
                  semantic.1.normal.facts.coherent.valid unfolded (grows_trans later growth)
                intro edge member
                apply (ih middle ⟨middleContext, middleHeap⟩ middleCovered (entry.identity :: seen) (result :: rest) nextInputs
                  edges after nextDone growth edge member).from_seeds view (result :: rest) _ ?_ edge
                intro child member
                rcases List.mem_cons.mp member with same | member
                · rw [same]
                  exact .step (.seed List.mem_cons_self) (by simp only [MergedFreshOrdinaryGraph.successors, replay, List.mem_singleton])
                · exact tailSeeds child member

/-- Direct source branches and canonical closure output retain exact edge origins. -/
theorem nodeEdges_origins [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (available : Available state value)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges after)
    (view : State Symbol Guard) (growth : Grows after view) :
    ∀ edge ∈ edges, Origin view [value] edge := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentSemantic : SemanticHeap current)
      (currentCovered : Covered [] current) (input : Available current root)
      (completed : (collect fuel current [] [root]).canonical = .done edges after) :
      ∀ edge ∈ edges, Origin view [root] edge := by
    cases readDone : collect fuel current [] [root] with
    | unresolved | pending | exhausted => simp only [readDone, Result.canonical] at completed; cases completed
    | done values final =>
        have same : canonicalEdges values = edges ∧ final = after := by
          simpa only [readDone, Result.canonical, Result.done.injEq] using completed
        cases same.2
        intro edge member
        apply collect_origins fuel current currentSemantic currentCovered [] [root]
          (by intro value member; rw [List.mem_singleton.mp member]; exact input)
          values after readDone view growth edge
        exact canonicalEdges_member values edge (same.1 ▸ member)
  cases value with
  | empty | reference => cases done; simp
  | node entry own depth free =>
      cases done
      intro edge member
      exact ⟨_, .seed List.mem_cons_self, member⟩
  | union entry members depth free => exact fallback _ state semantic covered available done
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, middleContext, middleHeap, middleCovered, resultAvailable, firstGrowth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have rootAvailable := available.grows state middle firstGrowth history
      cases result with
      | node actual own level free =>
          have same : own = edges ∧ middle = after := by
            simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded, Result.done.injEq] using done
          cases same.2
          have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay (.mu entry body depth ordinary) state view (.node actual own level free)
            after semantic.1.normal.facts.coherent.valid unfolded growth
          intro edge member
          exact ⟨.node actual own level free, .step (.seed List.mem_cons_self)
            (by simp only [MergedFreshOrdinaryGraph.successors, replay, List.mem_singleton]), same.1 ▸ member⟩
      | empty | reference | union | mu =>
          apply fallback _ middle ⟨middleContext, middleHeap⟩ middleCovered rootAvailable
          simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded] using done


end MicroCFTA.MergedFreshOrdinaryExposureOrigins
