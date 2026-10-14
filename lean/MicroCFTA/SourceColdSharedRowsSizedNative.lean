import MicroCFTA.SourceColdSharedRowsTable
import MicroCFTA.SourceSizedFiniteKeysDispatchApi
import MicroCFTA.SourceSizedFiniteKeysPublic

/-!
# Public native Sized dispatch on actual cold output tables

Raw table conversion preserves every state, transition, constraint, and row
order. Successful native dispatch uses the original canonical reference API.
Its accepted terms have exactly the original physical guarded language.
Validation and active equality constraints retain their explicit contracts.
-/
namespace MicroCFTA.SourceColdSharedRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open MergedPhysicalWarmup Language RecursiveSize
open SourceObservations SourceSymbolicIndex SourceGuards SourceSizedDispatcher
open SourcePreparedSharedRows (encode)
variable {Symbol Guard : Type}

/-- Convert the actual shared table without changing any row payload or order. -/
def sizedTable (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard))) :
    SourceSizedFiniteKeys.Table SourceInternedRows.State Symbol Guard :=
  raw.map fun (state, edges) => (state, edges.map fun edge => ⟨edge.label, edge.children, edge.constraint⟩)

/-- Raw Sized conversion retains the exact original guarded table. -/
theorem sized_interpreted (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (meaning : Guard → Term Symbol → Bool) :
    SourceSizedFiniteKeys.interpreted (sizedTable raw) meaning = SourceInternedRows.interpretedRows meaning raw := by
  simp only [SourceSizedFiniteKeys.interpreted, sizedTable, SourceInternedRows.interpretedRows, List.map_map]
  apply List.map_congr_left
  intro entry _
  simp only [Function.comp_apply, List.map_map]
  rfl

/-- The raw original-key lookup has the exact language of the actual returned shared table. -/
theorem sized_graph (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (meaning : Guard → Term Symbol → Bool) :
    SourceSizedDecided.automaton (SourceSizedFiniteKeys.lookup (sizedTable raw)) meaning =
      FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw) := by
  funext state
  rw [← sized_interpreted, SourceSizedFiniteKeys.interpreted_lookup]
  rfl

variable {Formula : Type} [DecidableEq Formula] [Ord (Label Formula)]
  [Std.TransOrd (Label Formula)] [Std.LawfulEqOrd (Label Formula)]
  [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]

/-- Successful native queries on actual cold rows have canonical sequence equality and both signed inverses. -/
theorem Trace.native_correct
    (state final : State (Label Formula) (Constraint Formula)) (value : Value (Label Formula) (Constraint Formula))
    (rows : Rows (Label Formula) (Constraint Formula)) (trace : Trace state (fun _ => none) [value] rows final)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) (closed : value.free = [])
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (valid : FTAValidation.validateRows (encode value)
      (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)))
    (active : ∀ key row, row ∈ SourceSizedFiniteKeys.lookup (sizedTable (table rows keys value)) key →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (formulas : Formulas Formula) (solver : Entailment Formula) (api : Api (Label Formula))
    (success : SourceSizedFiniteKeysDispatch.nativeSized (sizedTable (table rows keys value)) (encode value) valid = .ok api) :
    api = referenceApi (SourceSizedDispatcher.equalityRows
      (SourceSizedFiniteKeys.nativeSorted (sizedTable (table rows keys value)) (encode value) valid)) (encode value) ∧
    (∀ (size : Nat) term, term ∈ api.terms (size : Int) ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (acceptsConstraint formulas solver)) value term ∧ nodeSize term = size) ∧
    (∀ (size : Nat), SourceSizedReference.ClassEvaluation
      (SourceSizedDispatcher.equalityRows (SourceSizedPreprocessing.sortedRows
        (SourceSizedFiniteKeys.input (sizedTable (table rows keys value)) (encode value) valid))) (size + 1) size
      (SourceSizedFiniteKeys.input (sizedTable (table rows keys value)) (encode value) valid).root (api.terms (size : Int))) ∧
    (∀ bound, (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).Nodup ∧
      (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).Pairwise
        (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ term, (∃ bound, term ∈ SourceSizedQueries.through (fun size : Nat => api.terms size) bound) ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (acceptsConstraint formulas solver)) value term) ∧
    (∀ size rank term, (api.rank term).map (fun position => (Int.ofNat position.size, Int.ofNat position.rank)) =
      some (size, rank) ↔ api.unrank size rank = some term) := by
  have publicSuccess := success
  rw [SourceSizedFiniteKeysDispatch.nativeSized_eq] at publicSuccess
  obtain ⟨members, finite, ordered, coverage, inverses⟩ := SourceSizedFiniteKeysPublic.public_correct
    (sizedTable (table rows keys value)) (encode value) valid active formulas solver api publicSuccess
  have language (term : Term (Label Formula)) :
      Accepts (SourceSizedDecided.automaton (SourceSizedFiniteKeys.lookup (sizedTable (table rows keys value)))
        (acceptsConstraint formulas solver)) (encode value) term ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (acceptsConstraint formulas solver)) value term := by
    rw [sized_graph]
    exact trace.table_language state final value rows facts prepared available closed keys domain _ term
  refine ⟨(SourceSizedFiniteKeysDispatch.native_success (sizedTable (table rows keys value)) (encode value) valid api success).2,
    ?_, finite, ordered, ?_, inverses⟩
  · intro size term
    rw [members, language]
  · intro term
    rw [coverage, language]

end MicroCFTA.SourceColdSharedRows
