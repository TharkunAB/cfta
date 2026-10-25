import MicroCFTA.MergedColdReaderClosedInputs
import MicroCFTA.InternedStoredSubstitutionScope

/-!
# Closed cold reads cannot expose an unresolved reference

Prepared source substitution replaces every free body reference of a
closed Mu with that same closed Mu. Closed captured records stay unchanged.
Actual binder-free reconstruction therefore returns a closed value.
-/
namespace MicroCFTA.MergedColdReaderClosed
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open InternedNormalizationFree InternedStoredSubstitution InternedStoredSubstitutionScope
open InternedStoredClosedMuCompletion MergedPhysicalWarmup
open MergedColdReaderClosedInputs MergedSourceExposure MergedColdReaderTermination

/-- Ordered source leaves are the concatenation of each original child's leaves. -/
theorem manyLeaves_flatMap (values : List (Value Symbol Guard)) : manyLeaves values = values.flatMap leaves := by
  induction values with
  | nil => simp [manyLeaves]
  | cons value rest ih => simp only [manyLeaves, List.flatMap_cons, ih]

/-- Edge preparation retains exactly the leaves of its ordered source children. -/
theorem edgeLeaves_flatMap (edges : List (EdgeValue Symbol Guard)) :
    edgeLeaves edges = (edges.flatMap EdgeValue.children).flatMap leaves := by
  induction edges with
  | nil => simp [edgeLeaves]
  | cons edge rest ih =>
      cases edge
      simp only [edgeLeaves, EdgeValue.children, List.flatMap_cons, List.flatMap_append, manyLeaves_flatMap, ih]

/-- Replacing each actual free name by a closed record closes every prepared lexical input. -/
theorem prepared_leaves_closed (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (prepared : PreparedWithoutMu value)
    (environment : Environment Symbol Guard)
    (replaced : ∀ name ∈ value.free, (input environment (.reference name)).free = []) :
    ∀ leaf ∈ leaves value, (input environment leaf).free = [] := by
  rw [leaves.eq_def]
  split
  · rename_i closed
    intro leaf member
    have same := List.mem_singleton.mp member
    rw [same, input_closed value environment (List.isEmpty_iff.mp closed)]
    exact List.isEmpty_iff.mp closed
  · rename_i opened
    cases prepared with
    | closed value closed => simp [closed] at opened
    | empty => simp [Value.free] at opened
    | reference name =>
        intro leaf member
        rw [List.mem_singleton.mp member]
        exact replaced name (by simp [Value.free])
    | node entry edges depth free children =>
        intro leaf member
        dsimp only at member
        rw [edgeLeaves_flatMap] at member
        obtain ⟨child, included, leafIn⟩ := List.mem_flatMap.mp member
        apply prepared_leaves_closed child state coherent (available.children child included) (children child included) environment ?_ leaf leafIn
        intro name named
        apply replaced name
        rw [Value.free, node_free state coherent entry edges depth free available.resident]
        exact (childFree_member _ name).mpr ⟨child, included, named⟩
    | union entry members depth free children =>
        intro leaf member
        dsimp only at member
        rw [manyLeaves_flatMap] at member
        obtain ⟨child, included, leafIn⟩ := List.mem_flatMap.mp member
        apply prepared_leaves_closed child state coherent (available.children child included) (children child included) environment ?_ leaf leafIn
        intro name named
        apply replaced name
        rw [Value.free, union_free state coherent entry members depth free available.resident]
        exact (childFree_member _ name).mpr ⟨child, included, named⟩
termination_by sizeOf value
decreasing_by
  · obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp included
    have edgeBound := List.sizeOf_lt_of_mem edgeIn
    have childBound := List.sizeOf_lt_of_mem childIn
    cases edge
    simp_all only [EdgeValue.children, EdgeValue.mk.sizeOf_spec, Value.node.sizeOf_spec]
    omega
  · have childBound := List.sizeOf_lt_of_mem included
    simp_all only [Value.union.sizeOf_spec]
    omega

/-- Every actual unfolding of a closed prepared value returns a closed value. -/
theorem unfold_closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = [])
    (result : Value Symbol Guard) (after : State Symbol Guard) (done : unfold value state = .done result after) :
    result.free = [] := by
  cases value with
  | empty | reference | node | union =>
      simp only [unfold, Outcome.done.injEq] at done
      exact done.1 ▸ closed
  | mu entry body depth ordinary =>
      let self := Value.mu entry body depth ordinary
      let environment : Environment Symbol Guard := fun name => if name = .interned entry.identity then some self else none
      have bodyAvailable : Available state body := available.children body (by simp [children])
      have bodyPrepared := prepared entry.key entry body depth ordinary (available.resident entry rfl)
      have replacements : Replacements state environment := by
        intro name replacement found
        by_cases same : name = .interned entry.identity
        · have equal : self = replacement := by simpa only [environment, ite_eq_left same, Option.some.injEq] using found
          exact equal ▸ available
        · simp only [environment, ite_eq_right same, reduceCtorEq] at found
      have leavesClosed : ClosedValues ((leaves body).map (input environment)) := by
        intro value member
        obtain ⟨leaf, leafMember, rfl⟩ := List.mem_map.mp member
        apply prepared_leaves_closed body state facts.coherent bodyAvailable bodyPrepared environment ?_ leaf leafMember
        intro name named
        have same : name = .interned entry.identity := by
          by_cases same : name = .interned entry.identity
          · exact same
          · have retained : name ∈ self.free := by simp only [self, Value.free, List.mem_filter]; exact ⟨named, by simpa using same⟩
            rw [closed] at retained
            cases retained
        simpa only [input, environment, ite_eq_left same, Option.getD_some] using closed
      obtain ⟨built, final, builtDone, builtClosed⟩ := MergedColdReaderClosedInputs.build_closed
        (encode (leaves body) [] body) ((leaves body).map (input environment)) state facts
        (inputs_available body environment state bodyAvailable replacements) leavesClosed
        (encode_withoutMu (leaves body) [] body bodyPrepared)
      have exactDone : unfold self state = .done built final := builtDone
      have same : result = built := (Outcome.done.inj (done.symm.trans exactDone)).1
      simpa only [same] using builtClosed

/-- Each retained member of an available closed union is closed. -/
theorem union_members_closed (state : State Symbol Guard) (facts : Facts state)
    (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard)) (depth free)
    (available : Available state (.union entry members depth free)) (closed : free = []) : ClosedValues members := by
  intro child member
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name named
  have parent : name ∈ childFree members := (childFree_member _ name).mpr ⟨child, member, named⟩
  rw [← union_free state facts.coherent entry members depth free available.resident, closed] at parent
  cases parent

/-- Every stored edge child of an available closed ordinary record is closed. -/
theorem node_children_closed (state : State Symbol Guard) (facts : Facts state)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth free)
    (available : Available state (.node entry edges depth free)) (closed : free = []) : ClosedEdges edges := by
  intro edge member child included
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name named
  have parent : name ∈ childFree (edges.flatMap EdgeValue.children) :=
    (childFree_member _ name).mpr ⟨child, List.mem_flatMap.mpr ⟨edge, member, included⟩, named⟩
  rw [← node_free state facts.coherent entry edges depth free available.resident, closed] at parent
  cases parent

/-- A finished closed worklist returns actual edges with closed children and cannot report a reference error. -/
theorem collect_closed [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) (closed : ClosedValues pending)
    (finished : Finished (collect fuel state seen pending)) :
    ∃ edges after, collect fuel state seen pending = .done edges after ∧ ClosedEdges edges := by
  induction fuel generalizing state seen pending with
  | zero =>
      cases pending with
      | nil => exact ⟨[], state, rfl, by simp [ClosedEdges]⟩
      | cons value rest => simp [collect, Finished] at finished
  | succ fuel ih =>
      cases pending with
      | nil => exact ⟨[], state, rfl, by simp [ClosedEdges]⟩
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have valueClosed := closed value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          have restClosed : ClosedValues rest := fun child member => closed child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state facts prepared seen rest restInputs restClosed finished
          | reference name => simp [Value.free] at valueClosed
          | node entry own depth free =>
              obtain ⟨edges, after, done, edgesClosed⟩ := ih state facts prepared seen rest restInputs restClosed
                ((finished_prepend own _).mp finished)
              refine ⟨own ++ edges, after, by simp only [collect, done, Result.prepend], ?_⟩
              intro edge member
              rcases List.mem_append.mp member with first | later
              · exact node_children_closed state facts entry own depth free available valueClosed edge first
              · exact edgesClosed edge later
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts prepared seen rest restInputs restClosed
                  (by simpa only [collect, ite_eq_left visited] using finished)
              · have memberClosed := union_members_closed state facts entry members depth free available valueClosed
                have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                have nextClosed : ClosedValues (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact memberClosed child first
                  · exact restClosed child later
                simpa only [collect, ite_eq_right visited] using ih state facts prepared (entry.identity :: seen)
                  (members ++ rest) nextInputs nextClosed (by simpa only [collect, ite_eq_right visited] using finished)
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts prepared seen rest restInputs restClosed
                  (by simpa only [collect, ite_eq_left visited] using finished)
              · cases done : unfold (.mu entry body depth ordinary) state with
                | pending => simp only [collect, ite_eq_right visited, done, Finished] at finished
                | done result after =>
                    have verified := unfold_verified (.mu entry body depth ordinary) state facts available
                    have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
                    have afterPrepared : Prepared after := by
                      simpa only [done, Outcome.state] using prepared.preserve (unfold_noNewMu (.mu entry body depth ordinary) state prepared available)
                    have nextInputs : Values after (result :: rest) := by
                      intro child member
                      rcases List.mem_cons.mp member with same | member
                      · rw [same]; exact verified.result result after done
                      · simpa only [done, Outcome.state] using verified.available child (restInputs child member)
                    have nextClosed : ClosedValues (result :: rest) := by
                      intro child member
                      rcases List.mem_cons.mp member with same | member
                      · rw [same]; exact unfold_closed _ state facts prepared available valueClosed result after done
                      · exact restClosed child member
                    simpa only [collect, ite_eq_right visited, done] using ih after afterFacts afterPrepared (entry.identity :: seen)
                      (result :: rest) nextInputs nextClosed (by simpa only [collect, ite_eq_right visited, done] using finished)

/-- The ordered cold source reader succeeds on each available closed root in the prepared fragment. -/
theorem nodeEdges_closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, MergedSourceExposure.nodeEdges fuel value state = .done edges after ∧ ClosedEdges edges := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentFacts : Facts current)
      (currentPrepared : Prepared current) (rootAvailable : Available current root) (rootClosed : root.free = []) :
      ∃ fuel edges after, (collect fuel current [] [root]).canonical = .done edges after ∧ ClosedEdges edges := by
    have inputs : Values current [root] := by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable
    have closed : ClosedValues [root] := by intro value member; simpa only [List.mem_singleton.mp member] using rootClosed
    obtain ⟨fuel, complete⟩ := collect_complete current currentFacts currentPrepared [] (List.range current.nodes.next)
      (initially_covered current currentFacts) [root] inputs
    obtain ⟨edges, after, done, children⟩ := collect_closed fuel current currentFacts currentPrepared [] [root] inputs closed complete
    exact ⟨fuel, canonicalEdges edges, after, by simp only [done, Result.canonical],
      fun edge member => children edge (canonicalEdges_member edges edge member)⟩
  cases value with
  | empty | reference => exact ⟨0, [], state, rfl, by simp [ClosedEdges]⟩
  | node entry edges depth free => exact ⟨0, edges, state, rfl, node_children_closed state facts entry edges depth free available closed⟩
  | union entry members depth free => exact fallback _ state facts prepared available closed
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done⟩ := MergedPhysicalWarmup.unfold_complete (.mu entry body depth ordinary) state prepared available
      have verified := unfold_verified (.mu entry body depth ordinary) state facts available
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
      have afterPrepared : Prepared after := by
        simpa only [done, Outcome.state] using prepared.preserve (unfold_noNewMu (.mu entry body depth ordinary) state prepared available)
      have afterAvailable : Available after (.mu entry body depth ordinary) := by
        simpa only [done, Outcome.state] using verified.available _ available
      have resultClosed := unfold_closed _ state facts prepared available closed result after done
      have resultAvailable := verified.result result after done
      obtain ⟨fuel, edges, final, fallbackDone, children⟩ := fallback _ after afterFacts afterPrepared afterAvailable closed
      cases result with
      | node actual own level free =>
          exact ⟨0, own, after, by simp only [MergedSourceExposure.nodeEdges, done],
            node_children_closed after afterFacts actual own level free resultAvailable resultClosed⟩
      | empty | reference | union | mu =>
          exact ⟨fuel, edges, final, by simpa only [MergedSourceExposure.nodeEdges, done] using fallbackDone, children⟩

end MicroCFTA.MergedColdReaderClosed
