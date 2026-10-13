import MicroCFTA.InternedDeepFreeNormalization
import MicroCFTA.InternedFreshOrdinaryNormal

/-!
# Actual callbacks remove root-only local alternatives

A normalized callback can retain its local as a deep reference or as the
single bare self value. This property gives exact deep-name and depth
equations for source cleanup without a whole-body substitution premise.
-/
namespace MicroCFTA.InternedDeepLocalNormal
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedDeepFreeDepth InternedDeepFreeNormalization InternedStoredMuOrigins
open InternedNestedConstruction (Syntax Outcome work finish)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryNormal
open InternedBinderProtocol (Reference NodeKey)

/-- A retained local is deep, except in the direct-self body. -/
def Local (name : Reference) (value : Value Symbol Guard) : Prop :=
  name ∈ value.free → name ∈ deepNames value ∨ value = .reference name

/-- Actual root filtering establishes the local normal form. -/
theorem filter_local [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    Local name (run (withoutSelfReference name value) state).1 := by
  intro member
  by_cases bare : value = .reference name
  · subst value
    exact Or.inr rfl
  · left
    exact (filter_deep name name value state normal available).mpr
      ((filter_free name value state normal available bare).mp member)

/-- Every completed repaired callback has the actual local normal form. -/
theorem callback_local [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : callback expression environment name state = .done value after) : Local name value := by
  have verified := build_verified expression _ state normal.facts inputs
  have retained := InternedFreshOrdinaryNormal.build_normal expression _ state normal inputs
  unfold callback at done
  cases computed : build expression (.reference name :: environment) state with
  | pending key stopped => simp only [computed, Outcome.bind] at done; cases done
  | done body beforeFilter =>
      have beforeNormal : Normal beforeFilter := by simpa only [computed, Outcome.state] using retained
      have available := verified.result body beforeFilter computed
      simp only [computed, Outcome.bind, work, Outcome.done.injEq] at done
      rw [← done.1]
      exact filter_local name body beforeFilter beforeNormal available

/-- A normalized body retains its binder exactly when the local has a deep occurrence. -/
theorem finish_deep (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state body)
    (localNormal : Local (.interned entry.identity) body) (name : Reference) :
    name ∈ deepNames (finish smart (.mu entry body depth ordinary)) ↔
      if smart then
        if .interned entry.identity ∈ deepNames body then name ∈ (Value.mu entry body depth ordinary).free
        else name ∈ deepNames body
      else name ∈ (Value.mu entry body depth ordinary).free := by
  classical
  cases smart with
  | false => simp [finish, deepNames]
  | true =>
      by_cases used : .interned entry.identity ∈ deepNames body
      · have free := deep_free body state coherent available _ used
        have nonbare : body.referenceOf ≠ .ref (.interned entry.identity) := by
          intro same
          have bare := (referenceOf_self_iff _ body).mp same
          simp [bare, deepNames] at used
        simp [finish, cleanup, free, nonbare, used, deepNames]
      · by_cases free : .interned entry.identity ∈ body.free
        · rcases localNormal free with impossible | bare
          · exact False.elim (used impossible)
          · subst body
            simp [finish, cleanup, Value.free, Value.referenceOf, deepNames]
        · simp [finish, cleanup, free, used]

/-- Normalized source cleanup has an exact depth equation from the deep-local test. -/
theorem finish_depth (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state body)
    (localNormal : Local (.interned entry.identity) body) :
    (finish smart (.mu entry body depth ordinary)).depth =
      if smart then
        if .interned entry.identity ∈ deepNames body then body.depth + 1 else body.depth
      else body.depth + 1 := by
  classical
  cases smart with
  | false => simp [finish, Value.depth]
  | true =>
      by_cases used : .interned entry.identity ∈ deepNames body
      · have free := deep_free body state coherent available _ used
        have nonbare : body.referenceOf ≠ .ref (.interned entry.identity) := by
          intro same
          have bare := (referenceOf_self_iff _ body).mp same
          simp [bare, deepNames] at used
        simp [finish, cleanup, free, nonbare, used, Value.depth]
      · by_cases free : .interned entry.identity ∈ body.free
        · rcases localNormal free with impossible | bare
          · exact False.elim (used impossible)
          · subst body
            simp [finish, cleanup, Value.free, Value.referenceOf, Value.depth, deepNames]
        · simp [finish, cleanup, free, used]

end MicroCFTA.InternedDeepLocalNormal
