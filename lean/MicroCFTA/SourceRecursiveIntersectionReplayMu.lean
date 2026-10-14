import MicroCFTA.SourceRecursiveIntersectionReplayCalls

/-!
# Exact replay of recursive source Mu calls

Completed Mu calls retain their actual canonical domain identity and body
result. The optional binder then reuses its completed source constructor.
No source callback purity or output-equivalence premise is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionDomain SourceRecursiveIntersectionControl

/-- A successful lifted constructor outcome retains its actual completed heap and original domain cache. -/
theorem construction_done (outcome : InternedNestedConstruction.Outcome Symbol Guard A) (state : Machine Symbol Guard)
    (value : A) (final : Machine Symbol Guard) (done : construction outcome state = .done value final) :
    ∃ heap, outcome = .done value heap ∧ final = {state with heap := heap} := by
  cases outcome with
  | pending key heap => simp only [construction] at done; cases done
  | done actual heap =>
      simp only [construction] at done
      cases done
      exact ⟨heap, rfl, rfl⟩

/-- Actual optional-binder completion replays the exact result without changing either later cache. -/
theorem maybeMu_replay [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (before after : Machine Symbol Guard) (valid : Valid before) (available : Available before.heap body)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body before.heap) before = .done value final)
    (growth : Extension final after) :
    construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body after.heap) after = .done value after := by
  obtain ⟨heap, completed, finalState⟩ := construction_done _ before value final done
  have heapGrowth : Grows heap after.heap := by simpa only [finalState] using growth.heap
  have repeated := SourceRecursiveIntersectionMaybeMu.replay key body before.heap heap after.heap valid.1 available value completed heapGrowth
  simp only [repeated, construction]

/-- Source Mu-domain allocation, original body calls, and optional-binder construction replay their exact completed result. -/
theorem mu_replay [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : mu call domain left right before = .done value final) (growth : Extension final after) :
    mu call domain left right after = .done value after := by
  cases first : identity left <;> cases second : identity right <;> simp only [mu, first, second] at done ⊢
  all_goals try cases done
  rename_i firstId secondId
  let key := extend domain.key ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair firstId secondId)
  let actual := SourceRecursiveIntersectionEnvironment.enter before.domains domain.key left right firstId secondId
  let enteredState : Machine Symbol Guard := {before with domains := actual.2}
  obtain ⟨enteredValid, _, enteredDomain⟩ := entered before valid domain known left right leftAvailable rightAvailable firstId secondId
  have bodyLeft : Available enteredState.heap (body left) := body_available before.heap left leftAvailable
  have bodyRight : Available enteredState.heap (body right) := body_available before.heap right rightAvailable
  have child := calls actual.1 (body left) (body right) enteredState enteredValid enteredDomain bodyLeft bodyRight
  change (call actual.1 (body left) (body right) enteredState).bind
    (fun bodyValue current => construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair firstId secondId) bodyValue current.heap) current) =
      .done value final at done
  have chain : Checked enteredState
      ((call actual.1 (body left) (body right) enteredState).bind fun bodyValue current =>
        construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair firstId secondId) bodyValue current.heap) current)
      (fun current value => Available current.heap value) := by
    apply checked_bind enteredState _ _ _ _ child
    intro bodyValue current returned currentValid available
    exact construction_checked current currentValid _ Available
      (SourceRecursiveIntersectionMaybeMu.verified _ bodyValue current.heap currentValid.1 available)
  have chainGrowth : Extension enteredState final := by simpa only [done, Result.state] using chain.extension
  have allocation : SourceRecursiveIntersectionEnvironment.enter after.domains domain.key left right firstId secondId =
      (actual.1, after.domains) :=
    make_domain_replay before.domains after.domains key valid.2 ((chainGrowth.trans growth).domains)
  rw [allocation]
  apply bind_replay _ _ enteredState after _ child _ _ _ value final done growth
  · intro bodyValue current returned currentValid available
    exact (construction_checked current currentValid _ Available
      (SourceRecursiveIntersectionMaybeMu.verified _ bodyValue current.heap currentValid.1 available)).extension
  · intro bodyValue current returned later
    exact replay actual.1 (body left) (body right) enteredState after bodyValue current enteredValid enteredDomain
      bodyLeft bodyRight returned later
  · intro bodyValue current returned currentValid available result final completed later
    exact maybeMu_replay _ bodyValue current after currentValid available result final completed later

end MicroCFTA.SourceRecursiveIntersectionKernel
