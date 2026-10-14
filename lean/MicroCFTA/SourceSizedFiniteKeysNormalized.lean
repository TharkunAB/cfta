import MicroCFTA.SourceSizedFiniteKeys
import MicroCFTA.FTAValidationClosed

/-!
# Constraint-preserving map normalization before Sized queries

The public FTA builder merges duplicate keys and sorts them. This raw
normalization retains every constraint and each state's alternative order.
Guard interpretation commutes with the actual source normalization.
-/
namespace MicroCFTA.SourceSizedFiniteKeys
open Language FTAValidation

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- Merge complete raw rows in source order and sort the distinct state keys. -/
def normalized (table : Table State Symbol Payload) : Table State Symbol Payload :=
  ((DistinctRank.distinct (table.map Prod.fst)).mergeSort (fun a b => compare a b != .gt)).map
    fun state => (state, lookup table state)

/-- Raw normalization retains the exact interpreted public FTA table. -/
theorem normalized_interpreted (table : Table State Symbol Payload) (holds : Payload → Term Symbol → Bool) :
    interpreted (normalized table) holds = normalizeRows (interpreted table holds) := by
  unfold normalized
  rw [interpreted]
  simp only [List.map_map, Function.comp_def]
  unfold normalizeRows
  rw [interpreted_keys]
  apply List.map_congr_left
  intro state _
  rw [interpreted_lookup]

/-- Normalization preserves the whole original guarded row function. -/
theorem normalized_graph (table : Table State Symbol Payload) (holds : Payload → Term Symbol → Bool) :
    SourceSizedDecided.automaton (lookup (normalized table)) holds =
      SourceSizedDecided.automaton (lookup table) holds := by
  funext state
  change (lookup (normalized table) state).map (SourceSizedDecided.Row.edge holds) =
    (lookup table state).map (SourceSizedDecided.Row.edge holds)
  rw [← interpreted_lookup, normalized_interpreted, SourceFromTerms.normalize_lookup, interpreted_lookup]

/-- Raw child-key closure derives interpreted child closure for every guard meaning. -/
theorem interpreted_closed (table : Table State Symbol Payload) (closed : Closed table)
    (holds : Payload → Term Symbol → Bool) : FTAValidation.Closed (interpreted table holds) := by
  intro edge member child childIn
  obtain ⟨⟨state, outgoing⟩, row, found⟩ := List.mem_flatMap.mp member
  have lookup := (rowFor_exact _ _ _).mpr ⟨outgoing, row, found⟩
  rw [interpreted_lookup] at lookup
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp lookup
  rw [interpreted_keys]
  exact (SourceDenseRows.mem_keys table child).mp (closed state original present child childIn)

/-- The actual normalized raw table validates exactly when its source FTA builder succeeds. -/
theorem normalized_validated [DecidableEq Symbol] (table : Table State Symbol Payload) (root : State)
    (success : mkFTA root (interpreted table (fun _ _ => true)) =
      .ok (interpreted (normalized table) (fun _ _ => true))) :
    validateRows root (interpreted (normalized table) (fun _ _ => true)) =
      .ok (interpreted (normalized table) (fun _ _ => true)) := by
  rw [normalized_interpreted] at success ⊢
  exact success

end MicroCFTA.SourceSizedFiniteKeys
