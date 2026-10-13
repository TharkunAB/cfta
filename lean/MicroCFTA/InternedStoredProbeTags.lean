import MicroCFTA.InternedSourceProbeTags
import MicroCFTA.InternedProfileMuOrigins
import MicroCFTA.InternedCleanupEmptiness

/-!
# Every reachable stored Mu has exact empty and direct-self probe tags

Each actual completed payload retains its original verified source prefix.
The three original callback calls therefore establish the body tags for
all stored records, even when a later enclosing construction is pending.
The source smart-empty decision then depends only on the canonical probes.
-/
namespace MicroCFTA.InternedStoredProbeTags
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedActualProbeTags InternedSourceProbeTags InternedProfileMuOrigins
open InternedBinderProtocol (Reference NodeKey)

/-- An actual original construction witness derives both exact stored body tags. -/
theorem origin_tags [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (origin : Origin entry body depth ordinary) : Tags entry body depth ordinary := by
  obtain ⟨expression, environment, before, afterDepth, afterOrdinary, afterBody, normal, inputs, heap,
    depthDone, ordinaryDone, missing, entrySame, bodyDone⟩ := origin
  exact source_calls expression environment before afterDepth afterOrdinary afterBody entry body depth ordinary
    normal inputs heap depthDone ordinaryDone missing entrySame bodyDone

/-- Arbitrary first source execution establishes exact tags for every actual completed recursive record. -/
theorem closed_tags [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    Tags entry body depth ordinary :=
  origin_tags entry body depth ordinary (closed_origins expression key entry body depth ordinary stored)

/-- Empty bodies correspond exactly to two empty canonical probes. -/
theorem closed_empty_body [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    body = .empty ↔ depth = .empty ∧ ordinary = .empty :=
  (closed_tags expression key entry body depth ordinary stored).1

/-- Direct-self bodies correspond exactly to the two source sentinel records. -/
theorem closed_self_body [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    body = .reference (.interned entry.identity) ↔
      depth = .reference .depth ∧ ordinary = .reference (.uninterned 0) := by
  rw [(closed_tags expression key entry body depth ordinary stored).2]
  constructor
  · rintro ⟨same, ordinarySame⟩
    exact ⟨same, by simpa only [same, Value.depth] using ordinarySame⟩
  · rintro ⟨same, ordinarySame⟩
    exact ⟨same, by simpa only [same, Value.depth] using ordinarySame⟩

/-- Actual smart cleanup is empty exactly for the two canonical probe pairs that identify its empty body cases. -/
theorem closed_finish_empty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    finish smart (.mu entry body depth ordinary) = .empty ↔ smart = true ∧
      ((depth = .empty ∧ ordinary = .empty) ∨
        (depth = .reference .depth ∧ ordinary = .reference (.uninterned 0))) := by
  rw [InternedCleanupEmptiness.finish_empty_iff,
    closed_empty_body expression key entry body depth ordinary stored,
    closed_self_body expression key entry body depth ordinary stored]

end MicroCFTA.InternedStoredProbeTags
