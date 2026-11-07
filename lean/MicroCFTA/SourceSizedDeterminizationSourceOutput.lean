import MicroCFTA.SourceSizedDeterminizationSourceLoop
import MicroCFTA.SourceSizedDeterminizationOrderedOutput

/-!
# Exact canonical queries from the incremental source loop

The source loop computes sorted known sets and incrementally inserts
holder entries. Its returned table supplies closure, structural validation,
finite canonical preparation, and the complete signed query contract.
No caller supplies an output carrier, closure, sort success, or permutation.
The native storage and full Sized dispatch boundaries remain separate.
-/
namespace MicroCFTA.SourceSizedDeterminizationSourceOutput
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows Std
open SourceSizedDeterminizationKernel SourceSizedDeterminizationClosure
open SourceSizedDeterminizationOrderedOutput (grouped table)
attribute [local instance] lexOrd

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
  [Ord State] [TransOrd State] [LawfulEqOrd State] [Ord Symbol]

/-- Final source known-set readback equals the complete output map's key sequence. -/
theorem output_keys (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices) :
    SourceSortedBuckets.keys (SourceSizedDeterminizationOrderedOutput.keyOf states source) choices = known := by
  obtain ⟨before, origin, rfl⟩ :=
    SourceSizedDeterminizationSourceLoop.compile_ready limit states source known choices returned
  exact SourceSizedDeterminizationOrderedOutput.output_keys limit states source before choices origin

/-- Incremental source execution derives closure of the ordered target-map output. -/
theorem compile_closed (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices) :
    Closed states source known (grouped states source choices) :=
  SourceSizedDeterminizationOrderedOutput.grouped_closed states source known choices
    (SourceSizedDeterminizationSourceLoop.compile_closed limit states source known choices returned)

variable [Ord (Sum State (List State))]

/-- Current structural validation succeeds for the returned source table. -/
theorem validation_succeeds (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :
    SourceFTAValidation.validateRows (.inl root)
        (interpreted (table states source known choices) (fun _ _ => true)) =
      .ok (interpreted (table states source known choices) (fun _ _ => true)) :=
  SourceSizedDeterminizationFinite.validation_succeeds states source known (grouped states source choices)
    (compile_closed limit states source known choices returned) root present

/-- Construct the finite canonical input from actual returned source rows. -/
def input (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :=
  SourceSizedStructuralKeys.input (table states source known choices) (.inl root)
    (validation_succeeds limit states source known choices returned root present)

/-- Canonical refinement terminates on the derived finite source output. -/
theorem canonical_completes (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :
    ∃ classes, CanonicalClasses.canonical
      (SourceSizedPreprocessing.graph (input limit states source known choices returned root present)) =
        some classes := CanonicalClasses.canonical_terminates _

/-- Compute the dense canonical sort of the source loop's grouped table. -/
def sortedRows (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :=
  SourceSizedStructuralKeys.nativeSorted (table states source known choices) (.inl root)
    (validation_succeeds limit states source known choices returned root present)

/-- Dense source sorting equals the finite canonical worker's row sequence. -/
theorem sorted_readback [TransOrd Symbol] [LawfulEqOrd Symbol]
    (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states)
    (state : Member (SourceDenseRows.keys (table states source known choices))) :
    (SourceSizedPreprocessing.sortedRows
      (input limit states source known choices returned root present) state).map forget =
        sortedRows limit states source known choices returned root present state.val :=
  SourceSizedStructuralKeys.sorted_readback (table states source known choices) (.inl root)
    (validation_succeeds limit states source known choices returned root present) state

/-- The computed canonical sort derives its own per-row permutation. -/
theorem sorted_permutation (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) (state : Sum State (List State)) :
    (automaton (sortedRows limit states source known choices returned root present)
      (fun _ _ => true) state).Perm
        (SourceSizedDeterminizationRows.rows states source (grouped states source choices) state) := by
  have closed := compile_closed limit states source known choices returned
  have valid := validation_succeeds limit states source known choices returned root present
  have permutation := SourceSizedStructuralKeys.sorted_automaton_perm
    (table states source known choices) (.inl root) valid (fun _ _ => true) state
  unfold SourceSizedDeterminizationOrderedOutput.table at permutation
  rw [SourceSizedDeterminizationFinite.interpreted_rows
    states source known (grouped states source choices) closed] at permutation
  exact permutation

/-- Successful source execution gives all exact signed count, rank, unrank, and prefix laws. -/
theorem queries_exact (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationSourceLoop.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :
    SourceSizedApiLaws.Exact
      (SourceSizedDispatcher.optimizedApi
        (automaton (sortedRows limit states source known choices returned root present) (fun _ _ => true))
        (.inl root)) (Accepts source root) :=
  SourceSizedDeterminizationQueries.closed_ordered_queries_exact states source plain supported known
    (grouped states source choices) (compile_closed limit states source known choices returned) _
    (sorted_permutation limit states source known choices returned root present) root

end MicroCFTA.SourceSizedDeterminizationSourceOutput
