import MicroCFTA.MergedSourceExposure

/-!
# Completion of the actual cold edge reader

Each unseen Mu consumes one initial issued-identity allowance. Actual
unfolding introduces no new Mu in the prepared fragment. Union expansion
decreases structural work. These two measures prove completion in the
source's actual request order.
-/
namespace MicroCFTA.MergedColdReaderTermination
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open InternedShallowHeap MergedPhysicalWarmup MergedSourceExposure
open InternedBinderProtocol (NodeKey)

mutual
/-- Count retained union structure, but stop before actual recursive unfolding. -/
def weight : Value Symbol Guard → Nat
  | .union _ members _ _ => workWeight members + 1
  | _ => 1

/-- The pending reader work is the sum of its finite retained union structures. -/
def workWeight : List (Value Symbol Guard) → Nat
  | [] => 0
  | value :: rest => weight value + workWeight rest
end

/-- Every pending value accounts for at least one reader step. -/
theorem weight_positive (value : Value Symbol Guard) : 0 < weight value := by cases value <;> simp [weight]

/-- Source union concatenation adds the remaining structural work. -/
theorem workWeight_append (first second : List (Value Symbol Guard)) :
    workWeight (first ++ second) = workWeight first + workWeight second := by
  induction first with
  | nil => simp [workWeight]
  | cons value rest ih => simp [workWeight, ih, Nat.add_assoc]

/-- Every current Mu is already visited or retains one finite initial allowance. -/
def Covered (state : State Symbol Guard) (seen remaining : List Nat) : Prop :=
  ∀ entry body depth ordinary, Available state (.mu entry body depth ordinary) →
    entry.identity ∈ seen ∨ entry.identity ∈ remaining

/-- The actual initial issued counter supplies all required Mu allowances. -/
theorem initially_covered (state : State Symbol Guard) (facts : Facts state) :
    Covered state [] (List.range state.nodes.next) := by
  intro entry body depth ordinary available
  have stored := resident_entry state facts.coherent (.mu entry body depth ordinary) available.resident entry rfl
  have issued := (facts.coherent.valid.2.2 entry.key entry stored).2
  exact Or.inr (List.mem_range.mpr (facts.coherent.valid.2.1 entry.identity entry.key issued))

/-- Visiting a union can only reduce the outstanding Mu obligations. -/
theorem Covered.visit (covered : Covered state seen remaining) (identity : Nat) :
    Covered state (identity :: seen) remaining := by
  intro entry body depth ordinary available
  exact (covered entry body depth ordinary available).imp (List.mem_cons_of_mem _) id

/-- One completed unseen Mu consumes its own allowance and preserves all others. -/
theorem Covered.unfold (before after : State Symbol Guard) (facts : Facts before)
    (seen remaining : List Nat) (covered : Covered before seen remaining)
    (identity : Nat) (unchanged : NoNewMu before after) :
    Covered after (identity :: seen) (remaining.erase identity) := by
  intro entry body depth ordinary available
  by_cases same : entry.identity = identity
  · exact Or.inl (List.mem_cons.mpr (Or.inl same))
  have original := facts.cached.nodes entry.key _ (unchanged entry.key entry body depth ordinary (available.resident entry rfl))
  rcases covered entry body depth ordinary original with visited | pending
  · exact Or.inl (List.mem_cons_of_mem _ visited)
  · exact Or.inr ((List.mem_erase_of_ne same).mpr pending)

/-- The actual ordered cold reader reaches a result or its explicit unresolved-reference error. -/
theorem collect_complete [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (seen remaining : List Nat) (covered : Covered state seen remaining)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending) :
    ∃ fuel, Finished (collect fuel state seen pending) := by
  cases pending with
  | nil => exact ⟨0, trivial⟩
  | cons value rest =>
      have available := inputs value List.mem_cons_self
      have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
      cases value with
      | empty =>
          obtain ⟨fuel, complete⟩ := collect_complete state facts prepared seen remaining covered rest restInputs
          exact ⟨fuel + 1, complete⟩
      | reference name => exact ⟨1, trivial⟩
      | node entry edges depth free =>
          obtain ⟨fuel, complete⟩ := collect_complete state facts prepared seen remaining covered rest restInputs
          exact ⟨fuel + 1, (finished_prepend edges _).mpr complete⟩
      | union entry members depth free =>
          by_cases visited : entry.identity ∈ seen
          · obtain ⟨fuel, complete⟩ := collect_complete state facts prepared seen remaining covered rest restInputs
            exact ⟨fuel + 1, by simpa only [collect, ite_eq_left visited] using complete⟩
          · have children : Values state (members ++ rest) := by
              intro value member
              rcases List.mem_append.mp member with child | later
              · exact available.children value child
              · exact restInputs value later
            obtain ⟨fuel, complete⟩ := collect_complete state facts prepared (entry.identity :: seen) remaining
              (covered.visit entry.identity) (members ++ rest) children
            exact ⟨fuel + 1, by simpa only [collect, ite_eq_right visited] using complete⟩
      | mu entry body depth ordinary =>
          by_cases visited : entry.identity ∈ seen
          · obtain ⟨fuel, complete⟩ := collect_complete state facts prepared seen remaining covered rest restInputs
            exact ⟨fuel + 1, by simpa only [collect, ite_eq_left visited] using complete⟩
          · have retained := (covered entry body depth ordinary available).resolve_left visited
            obtain ⟨result, after, done⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
            have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
            have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
            have unchanged : NoNewMu state after := by
              simpa only [done, Outcome.state] using unfold_noNewMu (.mu entry body depth ordinary) state prepared available
            have nextInputs : Values after (result :: rest) := by
              intro value member
              rcases List.mem_cons.mp member with same | member
              · rw [same]; exact verified.result result after done
              · simpa only [done, Outcome.state] using verified.available value (restInputs value member)
            obtain ⟨fuel, complete⟩ := collect_complete after afterFacts (prepared.preserve unchanged)
              (entry.identity :: seen) (remaining.erase entry.identity)
              (covered.unfold state after facts seen remaining entry.identity unchanged) (result :: rest) nextInputs
            exact ⟨fuel + 1, by simpa only [collect, ite_eq_right visited, done] using complete⟩
termination_by (remaining.length, workWeight pending)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; simp_all only [workWeight, weight, workWeight_append]; omega)
    | (apply Prod.Lex.left; rw [List.length_erase_of_mem retained]; have positive := List.length_pos_of_mem retained; omega)

/-- Every available cold root reaches a result or the exact source unresolved-reference error. -/
theorem nodeEdges_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) :
    ∃ fuel, Finished (MergedSourceExposure.nodeEdges fuel value state) := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentFacts : Facts current)
      (currentPrepared : Prepared current) (rootAvailable : Available current root) :
      ∃ fuel, Finished (collect fuel current [] [root]).canonical := by
    obtain ⟨fuel, complete⟩ := collect_complete current currentFacts currentPrepared [] (List.range current.nodes.next)
      (initially_covered current currentFacts) [root] (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)
    exact ⟨fuel, (finished_canonical _).mpr complete⟩
  cases value with
  | empty | reference | node => exact ⟨0, trivial⟩
  | union entry members depth free => exact fallback _ state facts prepared available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
      have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
      have unchanged : NoNewMu state after := by
        simpa only [done, Outcome.state] using unfold_noNewMu (.mu entry body depth ordinary) state prepared available
      have afterAvailable : Available after (.mu entry body depth ordinary) := by
        simpa only [done, Outcome.state] using verified.available _ available
      obtain ⟨fuel, complete⟩ := fallback _ after afterFacts (prepared.preserve unchanged) afterAvailable
      refine ⟨fuel, ?_⟩
      cases result <;> simp only [MergedSourceExposure.nodeEdges, done] <;> first | exact complete | trivial

/-- Extra proof fuel preserves the complete ordered result and exact cache after the reader finishes. -/
theorem collect_stable [DecidableEq (EdgeKey Symbol Guard)] (fuel extra : Nat)
    (state : State Symbol Guard) (seen : List Nat) (pending : List (Value Symbol Guard))
    (finished : Finished (collect fuel state seen pending)) :
    collect (fuel + extra) state seen pending = collect fuel state seen pending := by
  induction fuel generalizing state seen pending with
  | zero =>
      cases pending with
      | nil => simp [collect]
      | cons value rest => simp [collect, Finished] at finished
  | succ fuel ih =>
      cases pending with
      | nil => simp [collect]
      | cons value rest =>
          cases value with
          | empty => simpa only [Nat.succ_add, collect] using ih state seen rest finished
          | reference => simp only [Nat.succ_add, collect]
          | node entry edges depth free =>
              simp only [collect, finished_prepend] at finished
              simp only [Nat.succ_add, collect, ih state seen rest finished]
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [Nat.succ_add, collect, ite_eq_left visited] using ih state seen rest
                  (by simpa only [collect, ite_eq_left visited] using finished)
              · simpa only [Nat.succ_add, collect, ite_eq_right visited] using ih state (entry.identity :: seen) (members ++ rest)
                  (by simpa only [collect, ite_eq_right visited] using finished)
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [Nat.succ_add, collect, ite_eq_left visited] using ih state seen rest
                  (by simpa only [collect, ite_eq_left visited] using finished)
              · cases done : InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                | pending => simp only [collect, ite_eq_right visited, done, Finished] at finished
                | done result after =>
                    simpa only [Nat.succ_add, collect, ite_eq_right visited, done] using ih after (entry.identity :: seen) (result :: rest)
                      (by simpa only [collect, ite_eq_right visited, done] using finished)

/-- The complete source edge reader preserves its result and effects after sufficient proof fuel. -/
theorem nodeEdges_stable [DecidableEq (EdgeKey Symbol Guard)] (fuel extra : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (finished : Finished (MergedSourceExposure.nodeEdges fuel value state)) :
    MergedSourceExposure.nodeEdges (fuel + extra) value state = MergedSourceExposure.nodeEdges fuel value state := by
  have fallback (current : State Symbol Guard) (root : Value Symbol Guard)
      (complete : Finished (collect fuel current [] [root]).canonical) :
      (collect (fuel + extra) current [] [root]).canonical = (collect fuel current [] [root]).canonical :=
    congrArg Result.canonical (collect_stable fuel extra current [] [root] ((finished_canonical _).mp complete))
  cases value with
  | empty | reference | node => rfl
  | union => exact fallback state _ finished
  | mu entry body depth ordinary =>
      cases done : InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state with
      | pending => simp only [MergedSourceExposure.nodeEdges, done]
      | done result after =>
          cases result <;> simp only [MergedSourceExposure.nodeEdges, done] at finished ⊢ <;>
            first | rfl | exact fallback after _ finished

end MicroCFTA.MergedColdReaderTermination
