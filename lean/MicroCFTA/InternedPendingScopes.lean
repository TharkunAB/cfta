import MicroCFTA.InternedPendingOrigins
import MicroCFTA.InternedNestedMissReadback

/-!
# Lexical references of actual pending source reservations

A source reservation stays in the lexical environment of its active
callback and every nested callback. Later cache effects preserve both
its origin and the exact reserved identity.
-/
namespace MicroCFTA.InternedPendingScopes
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedProbeProvenance InternedFreshProbeKeys InternedNestedFacts InternedNestedProvenance
open InternedPendingOrigins InternedNestedCoverage InternedNestedMissReadback InternedNestedSpecialization
open InternedBinderProtocol (Reference NodeKey)

/-- Every pending permission has its actual origin and its reserved reference in the current lexical inputs. -/
def ScopedOrigins (waiting : List NodeKey) (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  Origins waiting state ∧ ∀ key ∈ waiting, ∃ entry, state.nodes.table key = some entry ∧ .reference (.interned entry.identity) ∈ environment

/-- Ordinary later effects retain every active reservation identity and its source origin. -/
theorem ScopedOrigins.grows {waiting : List NodeKey} {environment : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (scope : ScopedOrigins waiting environment before) (growth : Grows before after) : ScopedOrigins waiting environment after := by
  refine ⟨scope.1.grows growth, ?_⟩
  intro key member
  obtain ⟨entry, present, included⟩ := scope.2 key member
  exact ⟨entry, growth.nodes key entry present, included⟩

/-- Each nested probe or body keeps all enclosing pending references in its lexical tail. -/
theorem ScopedOrigins.local {waiting : List NodeKey} {environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (scope : ScopedOrigins waiting environment state) (value : Value Symbol Guard) : ScopedOrigins waiting (value :: environment) state := by
  refine ⟨scope.1, ?_⟩
  intro key member
  obtain ⟨entry, present, included⟩ := scope.2 key member
  exact ⟨entry, present, List.mem_cons_of_mem _ included⟩

/-- Actual reservation adds its fresh local reference and preserves all older lexical reservations. -/
theorem reserve_scope (depth ordinary : Value Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (missing : state.nodes.table (muKey depth ordinary) = none)
    (scope : ScopedOrigins waiting environment state) :
    let entry := Cache.intern state.nodes (muKey depth ordinary)
    ScopedOrigins (muKey depth ordinary :: waiting) (.reference (.interned entry.1.identity) :: environment)
      {state with nodes := entry.2} := by
  refine ⟨reserve_origins depth ordinary state facts depthAvailable ordinaryAvailable missing scope.1, ?_⟩
  intro key member
  rcases List.mem_cons.mp member with rfl | included
  · exact ⟨_, (Cache.intern_correct state.nodes _ facts.coherent.valid.2).2.1, List.mem_cons_self⟩
  · obtain ⟨entry, present, captured⟩ := scope.2 key included
    exact ⟨entry, InternedBinderProtocol.intern_grows state.nodes _ key entry present, List.mem_cons_of_mem _ captured⟩

/-- A successful normalized source callback preserves the original pending coverage. -/
theorem callback_covered [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered waiting state)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : callback body environment name state = .done value final) : Covered waiting final := by
  obtain ⟨raw, middle, bodyDone, filterDone⟩ := bind_done _ _ _ _ completed
  have middleCovered := build_covered body (.reference name :: environment) state valid covered raw middle bodyDone
  have middleValid : InternedConstructorTemplates.Valid middle := by
    simpa only [bodyDone, Outcome.state] using (build_correct body (.reference name :: environment) state valid).1
  exact work_covered (withoutSelfReference name raw) middle middleValid middleCovered value final filterDone

end MicroCFTA.InternedPendingScopes
