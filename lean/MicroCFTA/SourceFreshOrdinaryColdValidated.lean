import MicroCFTA.SourceFreshOrdinaryColdClosed
import MicroCFTA.SourceFreshOrdinaryColdCyclicInput
import MicroCFTA.SourceColdSharedRowsSizedNative
import MicroCFTA.SourceSizedFiniteKeysNormalized

/-!
# Actual FTA validation after general repaired cold traversal

Completed traversal declares the root and every child. Raw normalization
copies complete constraints. The public FTA builder can still reject an
inconsistent alphabet; the exact source arity scan determines that result.
-/
namespace MicroCFTA.SourceColdSharedRows
open Language

/-- Raw conversion preserves each state's complete alternatives and constraints. -/
theorem sized_lookup (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (state : SourceInternedRows.State) :
    SourceSizedFiniteKeys.lookup (sizedTable raw) state =
      (SourceInternedRows.lookup raw state).map (fun edge => ⟨edge.label, edge.children, edge.constraint⟩) := by
  simp only [SourceSizedFiniteKeys.lookup, sizedTable, List.flatMap_map, SourceInternedRows.lookup, List.map_flatMap]
  apply TablePosition.flatMap_congr
  intro entry _
  split <;> simp_all

/-- Raw conversion changes no state declaration. -/
theorem sized_keys (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard))) :
    (sizedTable raw).map Prod.fst = raw.map Prod.fst := by
  simp [sizedTable, List.map_map, Function.comp_def]

/-- Derived raw child closure survives the complete Sized row conversion. -/
theorem sized_closed (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (closed : SourceDenseRowsRestrict.Closed raw) : SourceSizedFiniteKeys.Closed (sizedTable raw) := by
  intro state edge member child childIn
  rw [sized_lookup] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rw [SourceDenseRows.mem_keys, sized_keys]
  exact (SourceDenseRows.mem_keys raw child).mp (closed state original present child childIn)

end MicroCFTA.SourceColdSharedRows

namespace MicroCFTA.SourceFreshOrdinaryColdSharedRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourcePreparedSharedRows (encode)
open SourceColdSharedRows (Rows ResidentRows Supported sizedTable table)

variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final)
    (semantic : SemanticHeap state) (covered : Covered [] state)
    (available : Available state value) (closed : value.free = []) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)

include trace semantic covered available closed domain

omit [DecidableEq Symbol] in
/-- Every actual completed repaired trace derives interpreted child closure. -/
theorem Trace.interpreted_closed (holds : Guard → Term Symbol → Bool) :
    FTAValidation.Closed (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) holds) := by
  have inputs : SourceColdSharedRows.Inputs state [value] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro available closed
  have noRows : ResidentRows state (fun _ => none) := by intro identity edges absent; cases absent
  obtain ⟨finalSemantic, finalCovered, _, _, _, resident⟩ := trace.correct semantic covered inputs noRows
  have replayed := trace.replayed semantic covered inputs (by intro identity edges absent; cases absent)
  have children := trace.closed (by intro identity edges absent; cases absent)
  exact SourceSizedFiniteKeys.interpreted_closed _ (SourceColdSharedRows.sized_closed _
    (SourceFreshOrdinaryColdClosed.table_closed final finalSemantic finalCovered rows replayed resident children keys domain value)) holds

/-- Actual cold rows remove both state failures and retain the exact normalized arity scan. -/
theorem Trace.builder_equation :
    FTAValidation.mkFTA (encode value) (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)) =
      match FTAValidation.checkArities (fun _ => none) (FTAValidation.arityEntries
        (FTAValidation.normalizeRows (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)))) with
      | .error error => .error (.inconsistent error)
      | .ok _ => .ok (SourceSizedFiniteKeys.interpreted (SourceSizedFiniteKeys.normalized (sizedTable (table rows keys value))) (fun _ _ => true)) := by
  have supported : Supported rows value := fun identity same => trace.pending_done value List.mem_cons_self identity same
  have root := SourceFreshOrdinaryColdCyclic.root_key rows keys value domain supported
  have declared : encode value ∈
      (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)).map Prod.fst := by
    rw [SourceSizedFiniteKeys.interpreted_keys, SourceColdSharedRows.sized_keys]
    exact (SourceDenseRows.mem_keys _ _).mp root
  rw [SourceSizedFiniteKeys.normalized_interpreted]
  exact FTAValidation.mkFTA_arity _ _ declared
    (trace.interpreted_closed state final value rows semantic covered available closed keys domain _)

/-- Successful cold conversion requires exactly a ranked alphabet, rather than only child closure. -/
theorem Trace.builder_ok_iff :
    FTAValidation.mkFTA (encode value) (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted (SourceSizedFiniteKeys.normalized (sizedTable (table rows keys value))) (fun _ _ => true)) ↔
      ∃ assignment, FTAValidation.Describes assignment (FTAValidation.arityEntries
        (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true))) := by
  have supported : Supported rows value := fun identity same => trace.pending_done value List.mem_cons_self identity same
  have root := SourceFreshOrdinaryColdCyclic.root_key rows keys value domain supported
  have declared : encode value ∈
      (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)).map Prod.fst := by
    rw [SourceSizedFiniteKeys.interpreted_keys, SourceColdSharedRows.sized_keys]
    exact (SourceDenseRows.mem_keys _ _).mp root
  rw [SourceSizedFiniteKeys.normalized_interpreted]
  exact FTAValidation.mkFTA_ranked_iff _ _ declared
    (trace.interpreted_closed state final value rows semantic covered available closed keys domain _)

/-- Every actual failed cold conversion has the source arity error, with no missing or dangling state. -/
theorem Trace.builder_error (error : FTAValidation.Error SourceInternedRows.State Symbol)
    (failed : FTAValidation.mkFTA (encode value)
      (SourceSizedFiniteKeys.interpreted (sizedTable (table rows keys value)) (fun _ _ => true)) = .error error) :
    ∃ arity, error = .inconsistent arity := by
  rw [trace.builder_equation state final value rows semantic covered available closed keys domain] at failed
  split at failed
  · rename_i arity _
    exact ⟨arity, (Except.error.inj failed).symm⟩
  · cases failed

end MicroCFTA.SourceFreshOrdinaryColdSharedRows
