import MicroCFTA.MergedSourceExposureLanguage
import MicroCFTA.MergedComparisonReaderReplay

/-!
# Complete edge coverage of the ordered source reader

The actual returned cache gives an exact graph for the original cold
read. Replay retains the original edge list and has no cache effects.
This property supplies a complete traversal certificate.
-/
namespace MicroCFTA.MergedSourceExposureCoverage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open MergedPhysicalWarmup MergedPhysicalComparison MergedSourceExposure MergedColdReaderFacts
open MergedSourceExposureLanguage

/-- A worklist record was visited earlier or occurs in the current traversal certificate. -/
def Covered (seen : List Nat) (found : List (Value Symbol Guard)) (value : Value Symbol Guard) : Prop :=
  (∃ entry, entryOf value = some entry ∧ entry.identity ∈ seen) ∨ value ∈ found

/-- Complete resident records with equal numeric identities have equal payloads. -/
theorem identity_unique (state : State Symbol Guard) (facts : Facts state)
    (first second : Value Symbol Guard) (left : Available state first) (right : Available state second)
    (entry other : Interned InternedBinderProtocol.NodeKey)
    (leftField : entryOf first = some entry) (rightField : entryOf second = some other)
    (same : entry.identity = other.identity) : first = second := by
  have leftStored := left.resident entry leftField
  have rightStored := right.resident other rightField
  obtain ⟨actual, stored, fields⟩ := facts.coherent.nodes entry.key first leftStored
  have equal : actual = entry := Option.some.inj ((fields_entry _ _ _ fields).symm.trans leftField)
  subst actual
  obtain ⟨actual, otherStored, fields⟩ := facts.coherent.nodes other.key second rightStored
  have equal : actual = other := Option.some.inj ((fields_entry _ _ _ fields).symm.trans rightField)
  subst actual
  have keys := (Cache.identity_eq_iff_key_eq state.nodes facts.coherent.valid.2 stored otherStored).mp same
  rw [← keys] at rightStored
  exact Option.some.inj (leftStored.symm.trans rightStored)

/-- Move one newly visited record from the numeric visited set into the certificate. -/
theorem covered_restore (state : State Symbol Guard) (facts : Facts state)
    (seen : List Nat) (found : List (Value Symbol Guard)) (value target : Value Symbol Guard)
    (available : Available state value) (targetAvailable : Available state target)
    (entry : Interned InternedBinderProtocol.NodeKey) (field : entryOf value = some entry)
    (covered : Covered (entry.identity :: seen) found target) : Covered seen (value :: found) target := by
  rcases covered with ⟨other, otherField, member⟩ | later
  · rcases List.mem_cons.mp member with first | old
    · exact Or.inr (List.mem_cons.mpr (Or.inl
        (identity_unique state facts target value targetAvailable available other entry otherField field first)))
    · exact Or.inl ⟨other, otherField, old⟩
  · exact Or.inr (List.mem_cons_of_mem _ later)

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
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) (edges : List (EdgeValue Symbol Guard))
    (done : collect fuel state seen pending = .done edges state) :
    ∃ found, Certificate state seen pending found edges := by
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
              · exact covered_restore state facts seen found value child available (restInputs child member) entry field
                  (cert.requested child (List.mem_append_right _ member))
            · intro parent member child nextMember
              have childAvailable : Available state child := by
                rcases List.mem_cons.mp member with rfl | member
                · exact availableNext child (nextEq ▸ nextMember)
                · exact (cert.closed parent member child nextMember).1
              refine ⟨childAvailable, ?_⟩
              apply covered_restore state facts seen found value child available
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
              · obtain ⟨result, middle, unfolded⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
                have verified := InternedStoredSubstitution.unfold_verified _ state facts available
                have middleFacts : Facts middle := by simpa only [unfolded, Outcome.state] using verified.facts
                have middlePrepared : Prepared middle := by
                  simpa only [unfolded, Outcome.state] using prepared.preserve
                    (unfold_noNewMu (.mu entry body depth ordinary) state prepared available)
                have nextInputs : Values middle (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact verified.result child middle unfolded
                  · simpa only [unfolded, Outcome.state] using verified.available child (restInputs child member)
                have tail : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges state := by
                  simpa only [collect, ite_eq_right visited, unfolded] using done
                have back : Grows middle state := by
                  simpa only [tail, Result.state] using
                    (collect_verified fuel middle middleFacts middlePrepared (entry.identity :: seen) (result :: rest) nextInputs).growth
                have replay := unfold_replay (.mu entry body depth ordinary) state state result middle facts.coherent.valid unfolded back
                have equal := (Outcome.done.inj (unfolded.symm.trans replay)).2
                subst middle
                exact expand entry rfl [result] (by simp only [successors, unfolded]) rfl
                  (by intro child member; rw [List.mem_singleton.mp member]; exact verified.result result state unfolded)
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
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending)
    (edges : List (EdgeValue Symbol Guard))
    (done : collect fuel state [] pending = .done edges state)
    (edge : EdgeValue Symbol Guard) (origin : Origin state pending edge) : edge ∈ edges := by
  obtain ⟨found, cert⟩ := collect_certificate fuel state facts prepared [] pending inputs edges done
  exact cert.covers state pending found edges edge origin

/-- A root with no epsilon successor exposes only its own constructor edges. -/
theorem origin_terminal [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (root : Value Symbol Guard) (terminal : successors state root = [])
    (edge : EdgeValue Symbol Guard) (origin : Origin state [root] edge) :
    edge ∈ InternedEdgeResidency.nodeEdges root := by
  obtain ⟨source, reached, member⟩ := origin
  have equal : source = root := by
    clear member
    induction reached with
    | seed member => exact List.mem_singleton.mp member
    | step prior member ih => simp [ih, terminal] at member
  simpa only [equal] using member

/-- A source with one epsilon successor and no constructor edges delegates every origin to it. -/
theorem origin_single [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (root result : Value Symbol Guard) (next : successors state root = [result])
    (noEdges : InternedEdgeResidency.nodeEdges root = [])
    (edge : EdgeValue Symbol Guard) (origin : Origin state [root] edge) : Origin state [result] edge := by
  obtain ⟨source, reached, member⟩ := origin
  have separated : source = root ∨ Productivity.Reachable (successors state) [result] source := by
    clear member
    induction reached with
    | seed member => exact Or.inl (List.mem_singleton.mp member)
    | step prior member ih =>
        rcases ih with rfl | reached
        · exact Or.inr (.seed (next ▸ member))
        · exact Or.inr (.step reached member)
  rcases separated with rfl | reached
  · simp [noEdges] at member
  · exact ⟨source, reached, member⟩

/-- A successful read with no cache effect covers every actual epsilon constructor origin. -/
theorem nodeEdges_covers_fixed [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (value : Value Symbol Guard) (available : Available state value)
    (edges : List (EdgeValue Symbol Guard))
    (done : MergedSourceExposure.nodeEdges fuel value state = .done edges state)
    (edge : EdgeValue Symbol Guard) (origin : Origin state [value] edge) : edge ∈ edges := by
  have fallback (root : Value Symbol Guard) (input : Available state root)
      (completed : (collect fuel state [] [root]).canonical = .done edges state)
      (origin : Origin state [root] edge) : edge ∈ edges := by
    have inputs : Values state [root] := by
      intro child member
      simpa only [List.mem_singleton.mp member] using input
    cases read : collect fuel state [] [root] with
    | unresolved | pending | exhausted => simp only [read, Result.canonical, reduceCtorEq] at completed
    | done values final =>
        have equal : canonicalEdges values = edges ∧ final = state := by
          simpa only [read, Result.canonical, Result.done.injEq] using completed
        have cache := equal.2
        subst final
        rw [← equal.1]
        exact InternedEdgeResidency.canonicalEdges_retains state facts.coherent values edge
          ((collect_verified fuel state facts prepared [] [root] inputs).edges values state read)
          (collect_covers fuel state facts prepared [root] inputs values read edge origin)
  cases value with
  | empty | reference =>
      have impossible := origin_terminal state _ rfl edge origin
      cases impossible
  | node entry own depth free =>
      cases done
      exact origin_terminal state _ rfl edge origin
  | union entry members depth free => exact fallback _ available done origin
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
      have verified := InternedStoredSubstitution.unfold_verified _ state facts available
      have middleFacts : Facts middle := by simpa only [unfolded, Outcome.state] using verified.facts
      have middlePrepared : Prepared middle := by
        simpa only [unfolded, Outcome.state] using prepared.preserve
          (unfold_noNewMu (.mu entry body depth ordinary) state prepared available)
      have middleAvailable : Available middle (.mu entry body depth ordinary) := by
        simpa only [unfolded, Outcome.state] using verified.available _ available
      have back : Grows middle state := by
        have later := (collect_verified fuel middle middleFacts middlePrepared [] [.mu entry body depth ordinary]
          (by intro child member; rw [List.mem_singleton.mp member]; exact middleAvailable)).canonical _
        cases result with
        | node actual own level free =>
            have equal : own = edges ∧ middle = state := by
              simpa only [MergedSourceExposure.nodeEdges, unfolded, Result.done.injEq] using done
            rw [equal.2]
            exact grows_refl state
        | empty | reference | union | mu =>
            have completed : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done edges state := by
              simpa only [MergedSourceExposure.nodeEdges, unfolded] using done
            simpa only [completed, Result.state] using later.growth
      have replay := unfold_replay (.mu entry body depth ordinary) state state result middle facts.coherent.valid unfolded back
      have same := (Outcome.done.inj (unfolded.symm.trans replay)).2
      subst middle
      cases result with
      | node actual own level free =>
          have equal : own = edges := by
            simpa only [MergedSourceExposure.nodeEdges, unfolded, Result.done.injEq, and_true] using done
          rw [← equal]
          exact origin_terminal state (.node actual own level free) rfl edge (origin_single state _ (.node actual own level free)
            (by simp only [successors, unfolded]) rfl edge origin)
      | empty | reference | union | mu =>
          exact fallback _ available (by simpa only [MergedSourceExposure.nodeEdges, unfolded] using done) origin

/-- Every finite accepted source term has a constructor edge at a finite epsilon origin. -/
theorem accepts_origin [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard) (term : Language.Term Symbol)
    (accepted : EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term) :
    ∃ edge, Origin state [value] edge ∧ MergedPhysicalUnion.EdgeAccepts state meaning edge term := by
  induction accepted using EpsilonUnion.Accepts.rec (motive_2 := fun _ _ _ => True) with
  | @reference root target term member accepted ih =>
      obtain ⟨edge, origin, accepted⟩ := ih
      obtain ⟨source, reached, original⟩ := origin
      exact ⟨edge, ⟨source, EpsilonUnion.reach_trans _ root target source
        (.step (.seed List.mem_cons_self) member) reached, original⟩, accepted⟩
  | @node root edge terms member children guard ih =>
      cases root with
      | empty | reference | union | mu => simp [MergedPhysicalLanguage.graph, constructorRows] at member
      | node entry own depth free =>
          obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
          exact ⟨original, ⟨_, .seed List.mem_cons_self, selected⟩, terms, rfl, children, guard⟩
  | nil => trivial
  | cons => trivial

/-- Exact cold-reader replay gives reverse coverage in each later source cache with retained facts and inputs. -/
theorem nodeEdges_exact [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Available before value) (edges : List (EdgeValue Symbol Guard)) (after view : State Symbol Guard)
    (done : MergedSourceExposure.nodeEdges fuel value before = .done edges after)
    (growth : Grows after view) (viewFacts : Facts view) (viewPrepared : Prepared view)
    (viewAvailable : Available view value) :
    (∀ edge, edge ∈ edges ↔ Origin view [value] edge) ∧
      ∀ meaning term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph view meaning) value term ↔
        ∃ edge ∈ edges, MergedPhysicalUnion.EdgeAccepts view meaning edge term := by
  have replay := MergedComparisonReaderReplay.nodeEdges_replay fuel value before facts prepared available
    edges after view done growth
  have exactEdges : ∀ edge, edge ∈ edges ↔ Origin view [value] edge := fun edge =>
    ⟨nodeEdges_origins fuel value before facts prepared available edges after done view growth edge,
      nodeEdges_covers_fixed fuel view viewFacts viewPrepared value viewAvailable edges replay edge⟩
  refine ⟨exactEdges, ?_⟩
  intro meaning term
  constructor
  · intro accepted
    obtain ⟨edge, origin, edgeAccepted⟩ := accepts_origin view meaning value term accepted
    exact ⟨edge, (exactEdges edge).mpr origin, edgeAccepted⟩
  · rintro ⟨edge, member, accepted⟩
    exact nodeEdges_sound fuel value before facts prepared available edges after done view growth meaning edge member term accepted

/-- A successful cold read has exact edge and finite-term coverage in its actual returned cache. -/
theorem actual_exact [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Available before value) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedSourceExposure.nodeEdges fuel value before = .done edges after) :
    (∀ edge, edge ∈ edges ↔ Origin after [value] edge) ∧
      ∀ meaning term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph after meaning) value term ↔
        ∃ edge ∈ edges, MergedPhysicalUnion.EdgeAccepts after meaning edge term := by
  have verified := nodeEdges_verified fuel value before facts prepared available
  have afterFacts : Facts after := by simpa only [done, Result.state] using verified.facts
  have afterPrepared : Prepared after := by
    simpa only [done, Result.state] using prepared.preserve verified.unchanged
  have afterAvailable : Available after value := by
    simpa only [done, Result.state] using verified.available _ value available
  exact nodeEdges_exact fuel value before facts prepared available edges after after done (grows_refl after)
    afterFacts afterPrepared afterAvailable

/-- Every successful cold read has a later exact observation with the same edge list and no replay effects. -/
theorem observation_exact [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Available before value) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedSourceExposure.nodeEdges fuel value before = .done edges after) :
    ∃ outputs view, warmup (nodeInventory after) after = .done outputs view ∧
      Grows after view ∧ Facts view ∧ Prepared view ∧ Values view outputs ∧ Ready view outputs ∧
      MergedSourceExposure.nodeEdges fuel value view = .done edges view ∧
      (∀ edge, edge ∈ edges ↔ Origin view [value] edge) ∧
      ∀ meaning term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph view meaning) value term ↔
        ∃ edge ∈ edges, MergedPhysicalUnion.EdgeAccepts view meaning edge term := by
  have verified := nodeEdges_verified fuel value before facts prepared available
  have afterFacts : Facts after := by simpa only [done, Result.state] using verified.facts
  have afterPrepared : Prepared after := by
    simpa only [done, Result.state] using prepared.preserve verified.unchanged
  have afterAvailable : Available after value := by
    simpa only [done, Result.state] using verified.available _ value available
  obtain ⟨outputs, view, warmed, viewFacts, growth, history, unchanged, retained, ready⟩ :=
    prepare after afterFacts afterPrepared
  have viewPrepared := afterPrepared.preserve unchanged
  have viewAvailable := afterAvailable.grows after view growth history
  have exactRead := nodeEdges_exact fuel value before facts prepared available edges after view done growth
    viewFacts viewPrepared viewAvailable
  exact ⟨outputs, view, warmed, growth, viewFacts, viewPrepared, retained, ready,
    MergedComparisonReaderReplay.nodeEdges_replay fuel value before facts prepared available edges after view done growth,
    exactRead.1, exactRead.2⟩

end MicroCFTA.MergedSourceExposureCoverage
