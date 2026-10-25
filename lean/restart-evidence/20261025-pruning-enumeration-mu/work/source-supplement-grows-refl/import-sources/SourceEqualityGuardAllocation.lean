import MicroCFTA.SourceEqualityGuardAllocationPlan
import MicroCFTA.SourceEqualityConstraintMemoAllocation

/-!
# Demanded positive-guard equality allocation

Syntax failure performs no allocation. A demanded successful plan retains
every reached normalization and completed combination memo operation.
The first contradictory operand returns before demand of the second payload.
This sequential receipt does not prove GHC runtime evaluation adequacy.
-/
namespace MicroCFTA.SourceEqualityGuardAllocation
open SourceEqualityConstraintAllocation SourceEqualityGuardAllocationPlan
open SourceEqualityConstraintMemoAllocation (State Valid Grows)

/-- Execute one demanded constructor tree through the actual completed operation caches. -/
noncomputable def demand : Plan → State → Except String Value × State
  | .empty, before =>
      let built := intern (some []) before.constraints
      (.ok built.1, { before with constraints := built.2 })
  | .pair left right, before =>
      let built := normalize [[left, right]] before.constraints
      (built.1, { before with constraints := built.2 })
  | .combine first second, before =>
      let head := demand first before
      match head.1 with
      | .error _ => head
      | .ok .contradiction => head
      | .ok first =>
          let tail := demand second head.2
          match tail.1 with
          | .error _ => tail
          | .ok second => SourceEqualityConstraintMemoAllocation.combine first second tail.2

/-- Demand the positive payload only after its pure Maybe syntax test succeeds. -/
noncomputable def demandPositive (guard : SourceGuards.Guard Formula) (before : State) : Except String (Option Value) × State :=
  match make guard with
  | none => (.ok none, before)
  | some plan =>
      let built := demand plan before
      (built.1.map some, built.2)

private theorem grows_trans {before middle after : State} (first : Grows before middle) (second : Grows middle after) :
    Grows before after :=
  ⟨steps_trans first.constraints second.constraints, Cache.extends_trans first.combinations second.combinations,
    Cache.extends_trans first.descents second.descents⟩

private theorem empty_wellFormed : SourceEqualityDescend.WellFormed (some []) := by
  intro records same record member
  cases same
  cases member

private theorem combine_classes (first second result : Value)
    (done : SourceEqualityInheritedPayload.combine first.payload second.payload = .ok result.payload) :
    SourceEqualityInheritedPayload.classes result.payload = SourceCompactGuards.combineEqualities
      (SourceEqualityInheritedPayload.classes first.payload) (SourceEqualityInheritedPayload.classes second.payload) :=
  read_classes _ (SourceEqualityGuardReadback.combine_cached _ _) result.payload done

/-- Every demanded constructor plan completes with exact source classes and all actual allocation receipts. -/
theorem demand_correct (plan : Plan) (before : State) (valid : Valid before) :
    ∃ result, (demand plan before).1 = .ok result ∧ Valid (demand plan before).2 ∧
      Ready (demand plan before).2.constraints result ∧
      SourceEqualityInheritedPayload.classes result.payload = plan.classes ∧ Grows before (demand plan before).2 := by
  induction plan generalizing before with
  | empty =>
      have trace := intern_steps (some []) before.constraints
      refine ⟨(intern (some []) before.constraints).1, rfl, valid.steps _ trace,
        intern_ready (some []) before.constraints valid.constraints empty_wellFormed, ?_,
        ⟨trace, Cache.extends_refl _, Cache.extends_refl _⟩⟩
      rw [intern_payload]
      rfl
  | pair left right =>
      obtain ⟨value, cache, done, _, ready, trace, classes⟩ := normalize_complete [[left, right]] before.constraints valid.constraints
      have actual : demand (.pair left right) before = (.ok value, {before with constraints := cache}) := by
        simp only [demand, done]
      rw [actual]
      exact ⟨value, rfl, valid.steps _ trace, ready, classes, ⟨trace, Cache.extends_refl _, Cache.extends_refl _⟩⟩
  | combine first second firstIH secondIH =>
      obtain ⟨head, headDone, headValid, headReady, headClasses, headGrows⟩ := firstIH before valid
      cases head with
      | contradiction =>
          have actual : demand (.combine first second) before = demand first before := by simp only [demand, headDone]
          rw [actual]
          refine ⟨.contradiction, headDone, headValid, headReady, ?_, headGrows⟩
          have none : first.classes = none := headClasses.symm
          simp only [Plan.classes, none, SourceCompactGuards.combineEqualities, SourceEqualityInheritedPayload.classes, Value.payload, Option.map_none]
      | live identity records =>
          obtain ⟨tail, tailDone, tailValid, tailReady, tailClasses, tailGrows⟩ := secondIH (demand first before).2 headValid
          have currentHead := headReady.grows tailGrows.constraint_growth
          obtain ⟨result, completed, resultValid, resultReady, exactPayload, resultGrows⟩ :=
            SourceEqualityConstraintMemoAllocation.combine_correct (.live identity records) tail (demand second (demand first before).2).2
              tailValid currentHead tailReady
          have actual : demand (.combine first second) before = SourceEqualityConstraintMemoAllocation.combine
              (.live identity records) tail (demand second (demand first before).2).2 := by
            simp only [demand, headDone, tailDone]
          rw [actual]
          refine ⟨result, completed, resultValid, resultReady, ?_, grows_trans headGrows (grows_trans tailGrows resultGrows)⟩
          rw [combine_classes _ _ _ exactPayload, headClasses, tailClasses]
          rfl

/-- Unsupported or reflexive positive syntax returns its Maybe failure without any allocation. -/
theorem demandPositive_none (guard : SourceGuards.Guard Formula) (before : State) (failed : make guard = none) :
    demandPositive guard before = (.ok none, before) := by simp only [demandPositive, failed]

/-- Actual positive-payload demand retains exact normalized source output and valid completed caches. -/
theorem positive_correct (guard : SourceGuards.Guard Formula) (before : State) (valid : Valid before) :
    ∃ result, (demandPositive guard before).1 = .ok result ∧ Valid (demandPositive guard before).2 ∧
      (∀ value, result = some value → Ready (demandPositive guard before).2.constraints value) ∧
      result.map (fun value => SourceEqualityInheritedPayload.classes value.payload) = SourceCompactGuards.positiveNormalized guard ∧
      Grows before (demandPositive guard before).2 := by
  cases found : make guard with
  | none =>
      rw [demandPositive_none guard before found]
      refine ⟨none, rfl, valid, ?_, ?_, SourceEqualityConstraintMemoAllocation.grows_refl before⟩
      · intro value impossible
        cases impossible
      · have exact := make_exact guard
        simpa only [found, Option.map_none] using exact
  | some plan =>
      obtain ⟨result, done, afterValid, ready, classes, grows⟩ := demand_correct plan before valid
      have actual : demandPositive guard before = (.ok (some result), (demand plan before).2) := by
        simp only [demandPositive, found, done, Except.map]
      rw [actual]
      refine ⟨some result, rfl, afterValid, ?_, ?_, grows⟩
      · intro value same
        cases same
        exact ready
      · have exact := make_exact guard
        rw [Option.map_some, classes]
        simpa only [found, Option.map_some] using exact

end MicroCFTA.SourceEqualityGuardAllocation
