import MicroCFTA.SourceCurrentClassOriginalFields

/-!
# One causal allocation history for original equality fields

Each field constructor uses the interner returned by the preceding event.
Other permitted interner steps can occur between constructors. The history
derives all original field origins and current operation-table validity.
It records earlier execution. It does not allocate fields at class entry.
Actual GHC construction must still supply this history and its coverage.
-/
namespace MicroCFTA.SourceEqualityOriginalAllocationHistory
open SourceEqualityConstraintAllocation
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Guard" => SourceSymbolicIndex.Constraint

/-- Completed original constructors and intervening atomic steps share one interner history. -/
inductive History : Cache.State Key → Cache.State Key → List (Guard Formula) → Prop where
  | start (cache : Cache.State Key) : History cache cache []
  | construct (earlier : History initial before originals)
      (cached : SourceEqualityGuardReadback.Cached original.equalities)
      (done : SourceEqualityConstraintAllocation.construct original.equalities before = (.ok value, after)) :
      History initial after (originals ++ [original])
  | interleave (earlier : History initial before originals) (steps : Cache.Steps before after) :
      History initial after originals

/-- Actual constructor completion derives validity and its literal atomic allocation steps. -/
theorem construct_steps (original : Guard Formula)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (before : Cache.State Key) (valid : Cache.Valid before) (value : Value) (after : Cache.State Key)
    (done : construct original.equalities before = (.ok value, after)) :
    Cache.Valid after ∧ Cache.Steps before after := by
  obtain ⟨actual, final, completed, ready, _, steps, _, _⟩ := construct_complete original.equalities cached before valid
  have pair := Prod.mk.inj (completed.symm.trans done)
  have same : final = after := pair.2
  subst final
  exact ⟨ready, steps⟩

/-- One causal history derives every retained field origin and the complete atomic interner trace. -/
theorem History.verified {initial final : Cache.State Key} {originals : List (Guard Formula)}
    (history : History initial final originals) (valid : Cache.Valid initial) :
    Cache.Valid final ∧ Cache.Steps initial final ∧
      ∀ original ∈ originals, SourceEqualityOriginalFieldOrigins.Origin final original := by
  induction history with
  | start => exact ⟨valid, .refl _, fun _ absent => False.elim (List.not_mem_nil absent)⟩
  | @construct before originals after value original earlier cached done ih =>
      obtain ⟨beforeValid, earlierSteps, origins⟩ := ih
      obtain ⟨afterValid, steps⟩ := construct_steps original cached before beforeValid value after done
      refine ⟨afterValid, steps_trans earlierSteps steps, ?_⟩
      intro field member
      rcases List.mem_append.mp member with old | newest
      · exact (origins field old).grows (Cache.steps_table_extends steps)
      · have same : field = original := List.mem_singleton.mp newest
        subst field
        exact SourceEqualityOriginalFieldOrigins.of_construct original before beforeValid value after done
  | interleave earlier steps ih =>
      exact ⟨Cache.steps_valid ih.1 steps, steps_trans ih.2.1 steps,
        fun original member => (ih.2.2 original member).grows (Cache.steps_table_extends steps)⟩

/-- Original literal coverage derives the complete source-build allocation inventory from one history. -/
theorem History.inventory {initial final : Cache.State Key} {originals : List (Guard Formula)}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol (Guard Formula))
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals) :
    ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityOriginalFieldOrigins.Origin final original :=
  fun original member => (history.verified valid).2.2 original (covered original member)

/-- Empty completed operation tables retain the interner produced by the actual earlier history. -/
theorem History.operations_valid {initial final : Cache.State Key} {originals : List (Guard Formula)}
    (history : History initial final originals) (valid : Cache.Valid initial) :
    SourceEqualityConstraintMemoAllocation.Valid (SourceEqualityConstraintMemoAllocation.initial final) :=
  SourceEqualityConstraintMemoAllocation.initial_valid final (history.verified valid).1

/-- Actual source build derives resident original lookup from a single covered earlier allocation history. -/
theorem History.resident_lookup {initial final : Cache.State Key} {originals : List (Guard Formula)}
    (history : History initial final originals) (valid : Cache.Valid initial)
    [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol (Guard Formula))]
    (expression : InternedNestedConstruction.Syntax Symbol (Guard Formula))
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : InternedConstructorTemplates.Value Symbol (Guard Formula))
    (heap : InternedConstructorTemplates.State Symbol (Guard Formula))
    (built : InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value heap)
    (edge : InternedConstructorTemplates.EdgeValue Symbol (Guard Formula))
    (resident : InternedEdgeResidency.EdgeResident heap edge)
    (cached : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities) :
    ∃ loaded : SourceEqualityConjoinAllocation.Constraint Formula,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint final = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧ Ready final loaded.stored ∧
      SourceEqualityPhysicalPayload.read edge.entry.key.constraint.equalities = .ok loaded.stored.payload :=
  SourceEqualityOriginalFieldOrigins.resident_lookup final expression (history.inventory valid expression covered)
    value heap built edge resident cached

end MicroCFTA.SourceEqualityOriginalAllocationHistory
