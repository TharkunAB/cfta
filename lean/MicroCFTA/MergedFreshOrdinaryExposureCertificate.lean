import MicroCFTA.MergedFreshOrdinaryGraph

/-!
# Complete constructor coverage of fixed-cache repaired reads

An allocation-free completed repaired read supplies a finite certificate
for every reachable constructor. A completed unfolding replays in the final
cache. That exact replay identifies each intermediate cache in a fixed-cache
read. No preparation or no-new-Mu hypothesis is used.
-/
namespace MicroCFTA.MergedFreshOrdinaryExposureCertificate
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open MergedFreshOrdinaryGraph
open MergedSourceExposureCoverage (Covered covered_restore)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- A traversal certificate covers its roots, successor steps, and all copied constructor edges. -/
structure Certificate [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (seen : List Nat) (pending found : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard)) : Prop where
  available : Values state found
  requested : ∀ value ∈ pending, Covered seen found value
  closed : ∀ value ∈ found, ∀ child ∈ successors state value,
    Available state child ∧ Covered seen found child
  edges : ∀ value ∈ found, ∀ edge ∈ InternedEdgeResidency.nodeEdges value, edge ∈ edges

/-- A successful worklist with no cache effect has a finite certificate for its exact source traversal. -/
theorem collect_certificate [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : InternedRecordCoherence.Covered [] state)
    (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) (edges : List (EdgeValue Symbol Guard))
    (done : collect fuel state seen pending = .done edges state) :
    ∃ found, Certificate state seen pending found edges := by
  have facts := semantic.1.normal.facts
  induction fuel generalizing seen pending edges with
  | zero =>
      cases pending with
      | nil => cases done; exact ⟨[], by constructor <;> simp [Values]⟩
      | cons => cases done
  | succ fuel ih =>
      cases pending with
      | nil => cases done; exact ⟨[], by constructor <;> simp [Values]⟩
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have add (found : List (Value Symbol Guard)) (cert : Certificate state seen rest found edges)
              (noNext : successors state value = []) (noEdges : InternedEdgeResidency.nodeEdges value = []) :
              Certificate state seen (value :: rest) (value :: found) edges := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro child member
              rcases List.mem_cons.mp member with rfl | member
              · exact available
              · exact cert.available child member
            · intro child member
              rcases List.mem_cons.mp member with rfl | member
              · exact Or.inr List.mem_cons_self
              · rcases cert.requested child member with old | found
                · exact Or.inl old
                · exact Or.inr (List.mem_cons_of_mem _ found)
            · intro parent member child next
              rcases List.mem_cons.mp member with rfl | member
              · simp [noNext] at next
              · obtain ⟨childAvailable, covered⟩ := cert.closed parent member child next
                refine ⟨childAvailable, ?_⟩
                rcases covered with old | found
                · exact Or.inl old
                · exact Or.inr (List.mem_cons_of_mem _ found)
            · intro parent member edge selected
              rcases List.mem_cons.mp member with rfl | member
              · simp [noEdges] at selected
              · exact cert.edges parent member edge selected
          have expand (entry : Interned InternedBinderProtocol.NodeKey) (field : entryOf value = some entry)
              (next : List (Value Symbol Guard)) (nextEq : successors state value = next)
              (noEdges : InternedEdgeResidency.nodeEdges value = [])
              (availableNext : Values state next)
              (tail : collect fuel state (entry.identity :: seen) (next ++ rest) = .done edges state) :
              ∃ found, Certificate state seen (value :: rest) found edges := by
            have nextInputs : Values state (next ++ rest) := by
              intro child member
              rcases List.mem_append.mp member with member | member
              · exact availableNext child member
              · exact restInputs child member
            obtain ⟨found, cert⟩ := ih (entry.identity :: seen) (next ++ rest) nextInputs edges tail
            refine ⟨value :: found, ?_, ?_, ?_, ?_⟩
            · intro child member
              rcases List.mem_cons.mp member with rfl | member
              · exact available
              · exact cert.available child member
            · intro child member
              rcases List.mem_cons.mp member with rfl | member
              · exact Or.inr List.mem_cons_self
              · exact MergedSourceExposureCoverage.covered_restore state facts seen found value child available (restInputs child member) entry field
                  (cert.requested child (List.mem_append_right _ member))
            · intro parent member child nextMember
              have childAvailable : Available state child := by
                rcases List.mem_cons.mp member with rfl | member
                · exact availableNext child (nextEq ▸ nextMember)
                · exact (cert.closed parent member child nextMember).1
              refine ⟨childAvailable, ?_⟩
              apply MergedSourceExposureCoverage.covered_restore state facts seen found value child available
                childAvailable entry field
              rcases List.mem_cons.mp member with rfl | member
              · exact cert.requested child (List.mem_append_left _ (nextEq ▸ nextMember))
              · exact (cert.closed parent member child nextMember).2
            · intro parent member edge selected
              rcases List.mem_cons.mp member with rfl | member
              · simp [noEdges] at selected
              · exact cert.edges parent member edge selected
          have skip (entry : Interned InternedBinderProtocol.NodeKey) (field : entryOf value = some entry)
              (visited : entry.identity ∈ seen) (tail : collect fuel state seen rest = .done edges state) :
              ∃ found, Certificate state seen (value :: rest) found edges := by
            obtain ⟨found, cert⟩ := ih seen rest restInputs edges tail
            refine ⟨found, cert.available, ?_, cert.closed, cert.edges⟩
            intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact Or.inl ⟨entry, field, visited⟩
            · exact cert.requested child member
          cases value with
          | empty =>
              obtain ⟨found, cert⟩ := ih seen rest restInputs edges done
              exact ⟨.empty :: found, add found cert rfl rfl⟩
          | reference => cases done
          | node entry own depth free =>
              cases tail : collect fuel state seen rest with
              | unresolved | pending | exhausted => simp only [collect, tail, Result.prepend, reduceCtorEq] at done
              | done rows final =>
                  have equal : own ++ rows = edges ∧ final = state := by
                    simpa only [collect, tail, Result.prepend, Result.done.injEq] using done
                  rcases equal with ⟨rfl, rfl⟩
                  obtain ⟨found, cert⟩ := ih seen rest restInputs rows tail
                  refine ⟨.node entry own depth free :: found, ?_, ?_, ?_, ?_⟩
                  · intro child member
                    rcases List.mem_cons.mp member with rfl | member
                    · exact available
                    · exact cert.available child member
                  · intro child member
                    rcases List.mem_cons.mp member with rfl | member
                    · exact Or.inr List.mem_cons_self
                    · rcases cert.requested child member with old | found
                      · exact Or.inl old
                      · exact Or.inr (List.mem_cons_of_mem _ found)
                  · intro parent member child next
                    rcases List.mem_cons.mp member with rfl | member
                    · simp [successors] at next
                    · obtain ⟨childAvailable, covered⟩ := cert.closed parent member child next
                      refine ⟨childAvailable, ?_⟩
                      rcases covered with old | found
                      · exact Or.inl old
                      · exact Or.inr (List.mem_cons_of_mem _ found)
                  · intro parent member edge selected
                    rcases List.mem_cons.mp member with rfl | member
                    · exact List.mem_append_left _ selected
                    · exact List.mem_append_right _ (cert.edges parent member edge selected)
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · exact skip entry rfl visited (by simpa only [collect, ite_eq_left visited] using done)
              · exact expand entry rfl members rfl rfl (fun child member => available.children child member)
                  (by simpa only [collect, ite_eq_right visited] using done)
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · exact skip entry rfl visited (by simpa only [collect, ite_eq_left visited] using done)
              · obtain ⟨result, middle, unfolded, middleContext, _, _, resultAvailable, growth, history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    state semantic.1 available semantic.2 covered
                have nextInputs : Values middle (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact (restInputs child member).grows state middle growth history
                have tail : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges state := by
                  simpa only [collect, ite_eq_right visited, unfolded] using done
                have back : Grows middle state := by
                  simpa only [tail, Result.state] using
                    (MergedFreshOrdinaryColdReplay.collect_correct fuel middle middleContext.normal.facts.coherent.valid
                      (entry.identity :: seen) (result :: rest)).2
                have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay
                  (.mu entry body depth ordinary) state state result middle facts.coherent.valid unfolded back
                have equal := (Outcome.done.inj (unfolded.symm.trans replay)).2
                subst middle
                exact expand entry rfl [result] (by simp only [successors, unfolded]) rfl
                  (by intro child member; rw [List.mem_singleton.mp member]; exact resultAvailable)
                  (by simpa only [List.singleton_append] using tail)

/-- A certificate with no earlier visited identities covers every reachable constructor edge. -/
theorem Certificate.covers [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (pending found : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (cert : Certificate state [] pending found edges) (edge : EdgeValue Symbol Guard)
    (origin : Origin state pending edge) : edge ∈ edges := by
  obtain ⟨source, reached, member⟩ := origin
  have present : source ∈ found := by
    clear member
    induction reached with
    | seed member =>
        rcases cert.requested _ member with ⟨entry, _, absent⟩ | present
        · cases absent
        · exact present
    | step prior member ih =>
        rcases (cert.closed _ ih _ member).2 with ⟨entry, _, absent⟩ | present
        · cases absent
        · exact present
  exact cert.edges source present edge member

/-- Successful closure with no cache effect contains every edge reached from an original worklist root. -/
theorem collect_covers [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : InternedRecordCoherence.Covered [] state)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending)
    (edges : List (EdgeValue Symbol Guard))
    (done : collect fuel state [] pending = .done edges state)
    (edge : EdgeValue Symbol Guard) (origin : Origin state pending edge) : edge ∈ edges := by
  obtain ⟨found, cert⟩ := collect_certificate fuel state semantic covered [] pending inputs edges done
  exact cert.covers state pending found edges edge origin


end MicroCFTA.MergedFreshOrdinaryExposureCertificate
