import MicroCFTA.EnumerationIndexSelection

/-!
# Existing source actions produce correct cached-index states

Every successful assimilation branch lifts to the indexed mutation trace.
This includes repeated representatives and already eliminated sources.
The live branch uses the source's actual intersection, guard, and ordered
slot writes. The maintained invariant is derived at the lifted endpoint.
-/
namespace MicroCFTA.EnumerationIndexSource
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationSemantics
open EnumerationExpandableIndex

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Every successful source assimilation has an indexed endpoint with the same complete original state. -/
theorem assimilation_lift (graph : Graph Symbol Guard) (before : Cached Symbol Guard)
    (target source : Nat) (after : State Symbol Guard) (reached : Reachable graph before)
    (success : Success (EnumerationState.assimilate graph target source) before.core () after) :
    ∃ indexed, Reachable graph indexed ∧ indexed.core = after := by
  have original := success
  by_cases same : target = source
  · subst source
    have unchanged : after = before.core := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    exact ⟨before, reached, unchanged.symm⟩
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, sourceState, sourceLookup, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨sourceRead, sourceSame⟩ := (rawValue_success source before.core sourceState sourceValue).mp sourceLookup
    subst sourceState
    cases sourceValue with
    | eliminated =>
        obtain ⟨_, stateSame⟩ := (success_pure () () before.core after).mp continued
        exact ⟨before, reached, stateSame.symm⟩
    | enumerated fragment =>
        obtain ⟨targetValue, targetState, targetLookup, continued⟩ := (success_bind _ _ _ _ _).mp continued
        exact (success_failure .invalidIntersection targetState after () continued).elim
    | unenumerated sourceNode sourceScs =>
        obtain ⟨targetValue, targetState, targetLookup, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨targetRead, targetSame⟩ := (rawValue_success target before.core targetState targetValue).mp targetLookup
        subst targetState
        cases targetValue with
        | eliminated | enumerated _ => exact (success_failure .invalidIntersection before.core after () continued).elim
        | unenumerated targetNode targetScs =>
            let merged : UVarValue Symbol := .unenumerated (match sourceNode, targetNode with
              | none, node => node | node, none => node | some left, some right => some (graph.intersect left right)) (sourceScs ++ targetScs)
            have intersection : intersectValues graph (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs) = some merged := by
              cases sourceNode <;> cases targetNode <;> rfl
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, _⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have notEmpty : hasEmptyContents graph merged = false := by
              simpa using ((require_success _ before.core checked).mp required).1
            obtain ⟨indexed, _, reachedAfter, execution⟩ := assimilate_source graph before target source sourceNode targetNode
              sourceScs targetScs merged reached same sourceRead targetRead intersection notEmpty
            have afterSame : after = indexed.core := by simpa [Success, execution, ExceptT.run] using original
            exact ⟨indexed, reachedAfter, afterSame.symm⟩

/-- Successful source assimilation derives the exact new expandable and waiting indexes. -/
theorem assimilation_correct (graph : Graph Symbol Guard) (before : Cached Symbol Guard)
    (target source : Nat) (after : State Symbol Guard) (reached : Reachable graph before)
    (success : Success (EnumerationState.assimilate graph target source) before.core () after) :
    ∃ indexed, indexed.core = after ∧ Correct graph indexed := by
  obtain ⟨indexed, reachedAfter, same⟩ := assimilation_lift graph before target source after reached success
  exact ⟨indexed, same, reachedAfter.correct⟩

/-- A successful slot intersection retains every suspended occurrence from both inputs. -/
theorem intersection_references (graph : Graph Symbol Guard) (source target merged : UVarValue Symbol)
    (done : intersectValues graph source target = some merged) :
    references merged = references source ++ references target := by
  cases source <;> cases target <;> simp_all [intersectValues, references]
  subst merged
  rfl

/-- Moving suspended constraints to a representative preserves their full raw-reference multiplicity. -/
theorem assimilation_counts (graph : Graph Symbol Guard) (before : State Symbol Guard)
    (target source : Nat) (sourceValue targetValue merged : UVarValue Symbol) (different : target ≠ source)
    (sourceRead : before.values[source]? = some sourceValue) (targetRead : before.values[target]? = some targetValue)
    (intersection : intersectValues graph sourceValue targetValue = some merged) (uv : Nat) :
    EnumerationWaitingIndex.total uv (assimilated before target source merged).values =
      EnumerationWaitingIndex.total uv before.values := by
  have sourceAfter : (before.values.set target merged)[source]? = some sourceValue := by
    simp [different, sourceRead]
  rw [assimilated, EnumerationWaitingIndex.total_set uv source _ sourceValue .eliminated sourceAfter,
    EnumerationWaitingIndex.total_set uv target _ targetValue merged targetRead,
    intersection_references graph sourceValue targetValue merged intersection,
    EnumerationWaitingIndex.occurrences_append]
  simp only [references, EnumerationWaitingIndex.occurrences]
  omega

/-- The two actual assimilation writes keep the sparse raw waiting map unchanged, including duplicate references. -/
theorem assimilation_waiting (graph : Graph Symbol Guard) (before after : Cached Symbol Guard)
    (target source : Nat) (sourceValue targetValue merged : UVarValue Symbol)
    (reached : Reachable graph before) (different : target ≠ source)
    (sourceRead : before.core.values[source]? = some sourceValue) (targetRead : before.core.values[target]? = some targetValue)
    (intersection : intersectValues graph sourceValue targetValue = some merged)
    (done : EnumerationExpandableIndex.assimilate graph target source merged before = some after) :
    after.waiting = before.waiting := by
  have afterCorrect := (assimilate_reachable graph target source merged before after reached done).correct
  funext uv
  rw [afterCorrect.waiting uv, reached.correct.waiting uv,
    assimilate_core graph target source merged before after done,
    assimilation_counts graph before.core target source sourceValue targetValue merged different sourceRead targetRead intersection uv]

end MicroCFTA.EnumerationIndexSource
