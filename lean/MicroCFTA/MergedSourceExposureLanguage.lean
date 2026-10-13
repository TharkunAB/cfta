import MicroCFTA.MergedColdReaderFacts
import MicroCFTA.MergedPhysicalLanguage
import MicroCFTA.MergedPhysicalUnion

/-!
# Constructor origins in the actual cold reader

Every returned edge has an actual epsilon path from an input root in the
final cache. Completed unfolding replays in that cache. The argument does
not replace the ordered reader with a precomputed graph traversal.
-/
namespace MicroCFTA.MergedSourceExposureLanguage
open InternedConstructorTemplates InternedProbeProvenance InternedNestedConstruction
open InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open MergedPhysicalWarmup MergedPhysicalComparison MergedSourceExposure MergedColdReaderFacts
open Productivity

/-- A source edge belongs to an ordinary value reached through actual epsilon steps. -/
def Origin [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (roots : List (Value Symbol Guard)) (edge : EdgeValue Symbol Guard) : Prop :=
  ∃ value, Reachable (successors state) roots value ∧ edge ∈ InternedEdgeResidency.nodeEdges value

/-- Replace the reader's worklist seeds by known paths from the original roots. -/
theorem Origin.from_seeds [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (before after : List (Value Symbol Guard))
    (included : ∀ value ∈ before, Reachable (successors state) after value)
    (edge : EdgeValue Symbol Guard) (origin : Origin state before edge) : Origin state after edge := by
  obtain ⟨value, reached, member⟩ := origin
  exact ⟨value, EpsilonUnion.change_seeds _ before after included value reached, member⟩

/-- Each returned edge has a source path in every later extension of the actual returned cache. -/
theorem collect_origins [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (seen : List Nat) (pending : List (Value Symbol Guard))
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
              exact (ih state facts prepared seen rest restInputs edges after done growth edge member).from_seeds
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
                  · exact (ih state facts prepared seen rest restInputs values after tailDone growth edge restMember).from_seeds
                      view rest _ tailSeeds edge
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · have tailDone : collect fuel state seen rest = .done edges after := by
                  simpa only [collect, ite_eq_left visited] using done
                intro edge member
                exact (ih state facts prepared seen rest restInputs edges after tailDone growth edge member).from_seeds
                  view rest _ tailSeeds edge
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                have nextDone : collect fuel state (entry.identity :: seen) (members ++ rest) = .done edges after := by
                  simpa only [collect, ite_eq_right visited] using done
                intro edge member
                apply (ih state facts prepared (entry.identity :: seen) (members ++ rest) nextInputs edges after nextDone growth edge member).from_seeds
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
                exact (ih state facts prepared seen rest restInputs edges after tailDone growth edge member).from_seeds
                  view rest _ tailSeeds edge
              · obtain ⟨result, middle, unfolded⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
                have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
                have middleFacts : Facts middle := by simpa only [unfolded, Outcome.state] using verified.facts
                have middlePrepared : Prepared middle := by
                  simpa only [unfolded, Outcome.state] using prepared.preserve
                    (unfold_noNewMu (.mu entry body depth ordinary) state prepared available)
                have nextInputs : Values middle (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with same | member
                  · rw [same]; exact verified.result result middle unfolded
                  · simpa only [unfolded, Outcome.state] using verified.available child (restInputs child member)
                have nextDone : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges after := by
                  simpa only [collect, ite_eq_right visited, unfolded] using done
                have later : Grows middle after := by
                  simpa only [nextDone, Result.state] using
                    (collect_verified fuel middle middleFacts middlePrepared (entry.identity :: seen) (result :: rest) nextInputs).growth
                have replay := unfold_replay (.mu entry body depth ordinary) state view result middle
                  facts.coherent.valid unfolded (grows_trans later growth)
                intro edge member
                apply (ih middle middleFacts middlePrepared (entry.identity :: seen) (result :: rest) nextInputs
                  edges after nextDone growth edge member).from_seeds view (result :: rest) _ ?_ edge
                intro child member
                rcases List.mem_cons.mp member with same | member
                · rw [same]
                  exact .step (.seed List.mem_cons_self) (by simp only [MergedPhysicalComparison.successors, replay, List.mem_singleton])
                · exact tailSeeds child member

/-- Direct source branches and canonical closure output retain exact edge origins. -/
theorem nodeEdges_origins [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedSourceExposure.nodeEdges fuel value state = .done edges after)
    (view : State Symbol Guard) (growth : Grows after view) :
    ∀ edge ∈ edges, Origin view [value] edge := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentFacts : Facts current)
      (currentPrepared : Prepared current) (input : Available current root)
      (completed : (collect fuel current [] [root]).canonical = .done edges after) :
      ∀ edge ∈ edges, Origin view [root] edge := by
    cases readDone : collect fuel current [] [root] with
    | unresolved | pending | exhausted => simp only [readDone, Result.canonical] at completed; cases completed
    | done values final =>
        have same : canonicalEdges values = edges ∧ final = after := by
          simpa only [readDone, Result.canonical, Result.done.injEq] using completed
        cases same.2
        intro edge member
        apply collect_origins fuel current currentFacts currentPrepared [] [root]
          (by intro value member; rw [List.mem_singleton.mp member]; exact input)
          values after readDone view growth edge
        exact canonicalEdges_member values edge (same.1 ▸ member)
  cases value with
  | empty | reference => cases done; simp
  | node entry own depth free =>
      cases done
      intro edge member
      exact ⟨_, .seed List.mem_cons_self, member⟩
  | union entry members depth free => exact fallback _ state facts prepared available done
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
      have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
      have middleFacts : Facts middle := by simpa only [unfolded, Outcome.state] using verified.facts
      have middlePrepared : Prepared middle := by
        simpa only [unfolded, Outcome.state] using prepared.preserve
          (unfold_noNewMu (.mu entry body depth ordinary) state prepared available)
      have rootAvailable : Available middle (.mu entry body depth ordinary) := by
        simpa only [unfolded, Outcome.state] using verified.available _ available
      cases result with
      | node actual own level free =>
          have same : own = edges ∧ middle = after := by
            simpa only [MergedSourceExposure.nodeEdges, unfolded, Result.done.injEq] using done
          cases same.2
          have replay := unfold_replay (.mu entry body depth ordinary) state view (.node actual own level free)
            after facts.coherent.valid unfolded growth
          intro edge member
          exact ⟨.node actual own level free, .step (.seed List.mem_cons_self)
            (by simp only [MergedPhysicalComparison.successors, replay, List.mem_singleton]), same.1 ▸ member⟩
      | empty | reference | union | mu =>
          apply fallback _ middle middleFacts middlePrepared rootAvailable
          simpa only [MergedSourceExposure.nodeEdges, unfolded] using done

/-- A successful actual edge read cannot introduce a finite accepted term. -/
theorem nodeEdges_sound [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedSourceExposure.nodeEdges fuel value state = .done edges after)
    (view : State Symbol Guard) (growth : Grows after view)
    (meaning : Guard → Language.Term Symbol → Bool) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ edges) (term : Language.Term Symbol)
    (accepted : MergedPhysicalUnion.EdgeAccepts view meaning edge term) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph view meaning) value term := by
  obtain ⟨source, reached, original⟩ := nodeEdges_origins fuel value state facts prepared available
    edges after done view growth edge member
  apply EpsilonUnion.along_reference (MergedPhysicalLanguage.graph view meaning) value source reached term
  cases source with
  | empty | reference | union | mu => simp [InternedEdgeResidency.nodeEdges] at original
  | node entry own depth free =>
      exact (MergedPhysicalUnion.node_exact view meaning entry own depth free term).mpr ⟨edge, original, accepted⟩

end MicroCFTA.MergedSourceExposureLanguage
