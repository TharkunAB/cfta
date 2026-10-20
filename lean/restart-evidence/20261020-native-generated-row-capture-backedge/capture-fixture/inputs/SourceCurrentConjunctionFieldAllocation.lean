import MicroCFTA.SourceCurrentConjunctionEquality
import MicroCFTA.SourceEqualityIntersectionEdgeAllocation

/-!
# Actual allocation receipts for available conjunction fields

Each load uses the interner returned by the actual allocation. Ready
branches derive their normalized raw field from that same operation.
Sentinel construction allocates its canonical empty field. These lemmas
do not identify the older scoped native engine with checked demand.
-/
namespace MicroCFTA.SourceCurrentConjunctionFieldAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Valid Grows)
open SourceCurrentConjunctionEquality (FieldAvailable)
local notation "Raw" => SourceSymbolicIndex.Constraint
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint

/-- A literal normalized constructor receipt derives its actual current load. -/
theorem of_receipt (state : State) (original : Raw Formula)
    (cached : SourceEqualityGuardReadback.Cached original.equalities) (stored : Value)
    (ready : Ready state.constraints stored)
    (built : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload) :
    FieldAvailable state original :=
  ⟨cached, ⟨stored, original.guard⟩,
    (SourceEqualityConstraintFieldLookup.load_of_receipt original state.constraints cached stored built ready).1⟩

/-- Original field construction derives availability and its actual operation growth. -/
theorem construct_field (original : Raw Formula) (before : State) (valid : Valid before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (stored : Value) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (done : construct original.equalities before.constraints = (.ok stored, cache)) :
    Valid {before with constraints := cache} ∧ Grows before {before with constraints := cache} ∧
      FieldAvailable {before with constraints := cache} original := by
  obtain ⟨actual, final, completed, _, ready, steps, built, _⟩ :=
    construct_complete original.equalities cached before.constraints valid.constraints
  have pair := Prod.mk.inj (completed.symm.trans done)
  have same : actual = stored := Except.ok.inj pair.1
  have sameCache : final = cache := pair.2
  subst actual
  subst final
  exact ⟨valid.steps cache steps, ⟨steps, Cache.extends_refl _, Cache.extends_refl _⟩,
    of_receipt _ original cached stored ready built⟩

/-- Actual completed conjunction derives load availability for its returned raw field. -/
theorem conjoin_field [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Allocated Formula) (before : State) (valid : Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored)
    (result : Allocated Formula)
    (done : (SourceEqualityConjoinAllocation.conjoin le first second before).1 = .ok result) :
    Valid (SourceEqualityConjoinAllocation.conjoin le first second before).2 ∧
      Grows before (SourceEqualityConjoinAllocation.conjoin le first second before).2 ∧
      FieldAvailable (SourceEqualityConjoinAllocation.conjoin le first second before).2
        (SourceEqualityConjoinAllocation.readback result) := by
  obtain ⟨actual, completed, finalValid, ready, readback, cached, built, growth⟩ :=
    SourceEqualityConjoinAllocation.conjoin_correct le first second before valid firstReady secondReady
  have same : actual = result := Except.ok.inj (completed.symm.trans done)
  subst actual
  refine ⟨finalValid, growth, of_receipt _ _ cached result.stored ready ?_⟩
  rw [readback]
  exact built

/-- The actual ready intersection branch derives its field at the returned cache. -/
theorem intersection_ready_field [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Allocated Formula) (firstArity secondArity : Nat) (before : State) (valid : Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored)
    (result : Allocated Formula)
    (done : (SourceEqualityIntersectionEdgeAllocation.run le first second firstArity secondArity before).1 =
      .ok (.ready result)) :
    Valid (SourceEqualityIntersectionEdgeAllocation.run le first second firstArity secondArity before).2 ∧
      Grows before (SourceEqualityIntersectionEdgeAllocation.run le first second firstArity secondArity before).2 ∧
      FieldAvailable (SourceEqualityIntersectionEdgeAllocation.run le first second firstArity secondArity before).2
        (SourceEqualityConjoinAllocation.readback result) := by
  obtain ⟨branch, completed, _, finalValid, growth, receipt⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct le first second firstArity secondArity before valid
      firstReady secondReady
  have same : branch = .ready result := Except.ok.inj (completed.symm.trans done)
  obtain ⟨ready, cached, built⟩ := receipt result same
  exact ⟨finalValid, growth, of_receipt _ _ cached result.stored ready built⟩

/-- Actual sentinel allocation derives availability of its canonical empty field. -/
theorem empty_field (before : State) (valid : Valid before) :
    Valid (SourceEqualityMkEdgeAllocation.emptyField before) ∧
      Grows before (SourceEqualityMkEdgeAllocation.emptyField before) ∧
      FieldAvailable (SourceEqualityMkEdgeAllocation.emptyField before)
        (SourceEqualityConstraintConstructors.top (Formula := Formula)) := by
  obtain ⟨finalValid, growth, ready⟩ := SourceEqualityMkEdgeAllocation.emptyField_correct before valid
  refine ⟨finalValid, growth,
    of_receipt _ _ SourceEqualityConstraintConstructors.top_cached (intern (some []) before.constraints).1 ready ?_⟩
  rw [intern_payload]
  rfl

end MicroCFTA.SourceCurrentConjunctionFieldAllocation
