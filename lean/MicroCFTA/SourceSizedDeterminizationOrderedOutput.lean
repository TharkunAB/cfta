import MicroCFTA.SourceSizedDeterminizationOrderedOrigins
import MicroCFTA.SourceSizedDeterminizationFinite
import MicroCFTA.SourceSortedBucketsProjection

/-!
# Target-map output and canonical queries after ordered discovery

The source groups emitted choices by target. It reads the target map in
ascending key order. Original roots concatenate the buckets that contain
that state. Subset states retain their own bucket's transition order.
This file constructs that readback, validates its finite table, computes
the canonical sort, and derives the optimized signed query contract.

The proof uses the ordered discovery result. A caller supplies no output
carrier, closure, canonical success, or row permutation. Native holder-map
updates and Haskell container/machine correspondence remain separate.
-/
namespace MicroCFTA.SourceSizedDeterminizationOrderedOutput
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows Std
open SourceSizedDeterminizationKernel SourceSizedDeterminizationClosure
attribute [local instance] lexOrd

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol] [Ord State]

/-- Each choice belongs to the map bucket of its computed target subset. -/
def keyOf (states : List State) (source : Automaton State Symbol) (choice : Choice State Symbol) :
    List State := target states source choice.1 choice.2

/-- Read complete target buckets in ascending target-key order. -/
def grouped (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) : List (Choice State Symbol) :=
  SourceSortedBuckets.gather (keyOf states source) choices

/-- Target grouping preserves all emitted occurrences. -/
theorem grouped_perm (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) : (grouped states source choices).Perm choices :=
  SourceSortedBuckets.gather_perm _ _

/-- Left rows concatenate the selected target buckets in actual map-key order. -/
theorem left_readback (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) (state : State) :
    SourceSizedDeterminizationRows.rows states source (grouped states source choices) (.inl state) =
      (((SourceSortedBuckets.keys (keyOf states source) choices).filter
        (fun key => decide (state ∈ key))).flatMap
          (fun key => choices.filter fun choice => decide (keyOf states source choice = key))).map
            SourceSizedDeterminizationRows.wrap := by
  change ((SourceSortedBuckets.gather (keyOf states source) choices).filter
    (fun choice => decide (state ∈ keyOf states source choice))).map _ = _
  rw [SourceSortedBuckets.gather_filter (keyOf states source) choices (fun key => decide (state ∈ key))]

/-- Right rows retain the exact original order within their target bucket. -/
theorem right_readback (states : List State) (source : Automaton State Symbol)
    (choices : List (Choice State Symbol)) (key : List State) :
    SourceSizedDeterminizationRows.rows states source (grouped states source choices) (.inr key) =
      (choices.filter fun choice => decide (keyOf states source choice = key)).map
        SourceSizedDeterminizationRows.wrap := by
  change ((SourceSortedBuckets.gather (keyOf states source) choices).filter
    (fun choice => decide (keyOf states source choice = key))).map _ = _
  rw [SourceSortedBucketsProjection.gather_at_key (keyOf states source) choices key]

/-- Reordering whole buckets retains every discovery closure field. -/
theorem grouped_closed (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states source known choices) :
    Closed states source known (grouped states source choices) := by
  have permutation := grouped_perm states source choices
  refine ⟨?_, ?_, ?_, permutation.nodup_iff.mpr closed.distinct, closed.keyDistinct⟩
  · intro state present edge stored keys related
    exact permutation.mem_iff.mpr (closed.covered state present edge stored keys related)
  · intro choice present key child
    exact closed.children choice (permutation.mem_iff.mp present) key child
  · intro choice present
    exact closed.targets choice (permutation.mem_iff.mp present)

variable [Ord Symbol]

/-- Actual successful ordered execution derives closure of the source target-map readback. -/
theorem compile_closed (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices) :
    Closed states source known (grouped states source choices) :=
  grouped_closed states source known choices
    (SourceSizedDeterminizationOrderedRun.compile_closed limit states source known choices returned)

/-- Returned known keys and actual target-map readback have the same canonical key sequence. -/
theorem output_keys [TransOrd State] [LawfulEqOrd State]
    (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices) :
    SourceSortedBuckets.keys (keyOf states source) choices = CanonicalClasses.sortedSet known := by
  apply CanonicalClasses.sortedSet_ext
  intro key
  exact (SourceSizedDeterminizationOrderedOrigins.compile_targets_exact
    limit states source known choices returned key).symm

variable [Ord (Sum State (List State))]

/-- Build the complete raw finite table in target-map output order. -/
def table (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol)) :=
  SourceSizedDeterminizationFinite.table states source known (grouped states source choices)

/-- Current structural validation succeeds for the derived grouped table. -/
theorem validation_succeeds (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :
    SourceFTAValidation.validateRows (.inl root)
        (interpreted (table states source known choices) (fun _ _ => true)) =
      .ok (interpreted (table states source known choices) (fun _ _ => true)) :=
  SourceSizedDeterminizationFinite.validation_succeeds states source known (grouped states source choices)
    (compile_closed limit states source known choices returned) root present

/-- Ordered discovery constructs all finite canonical input fields. -/
def input (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :=
  SourceSizedStructuralKeys.input (table states source known choices) (.inl root)
    (validation_succeeds limit states source known choices returned root present)

/-- Canonical refinement terminates on the input constructed from ordered discovery. -/
theorem canonical_completes (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :
    ∃ classes, CanonicalClasses.canonical
      (SourceSizedPreprocessing.graph (input limit states source known choices returned root present)) =
        some classes := CanonicalClasses.canonical_terminates _

/-- Compute the source dense canonical sort on the grouped original-key rows. -/
def sortedRows (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :=
  SourceSizedStructuralKeys.nativeSorted (table states source known choices) (.inl root)
    (validation_succeeds limit states source known choices returned root present)

/-- Dense source sorting equals the finite worker's actual ordered row list. -/
theorem sorted_readback [TransOrd Symbol] [LawfulEqOrd Symbol]
    (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states)
    (state : Member (SourceDenseRows.keys (table states source known choices))) :
    (SourceSizedPreprocessing.sortedRows
      (input limit states source known choices returned root present) state).map forget =
        sortedRows limit states source known choices returned root present state.val :=
  SourceSizedStructuralKeys.sorted_readback (table states source known choices) (.inl root)
    (validation_succeeds limit states source known choices returned root present) state

/-- The actual computed grouped-table sort supplies its own per-row permutation. -/
theorem sorted_permutation (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) (state : Sum State (List State)) :
    (automaton (sortedRows limit states source known choices returned root present)
      (fun _ _ => true) state).Perm
        (SourceSizedDeterminizationRows.rows states source (grouped states source choices) state) := by
  have closed := compile_closed limit states source known choices returned
  have valid := validation_succeeds limit states source known choices returned root present
  have permutation := SourceSizedStructuralKeys.sorted_automaton_perm
    (table states source known choices) (.inl root) valid (fun _ _ => true) state
  unfold table at permutation
  rw [SourceSizedDeterminizationFinite.interpreted_rows
    states source known (grouped states source choices) closed] at permutation
  exact permutation

/-- Ordered discovery, target grouping, and canonical sorting give all exact signed query laws. -/
theorem queries_exact (limit : Nat) (states : List State) (source : Automaton State Symbol)
    (plain : Decoder.Plain source)
    (supported : ∀ state edge, edge ∈ source state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : SourceSizedDeterminizationOrderedRun.compile limit states source = .ready known choices)
    (root : State) (present : root ∈ states) :
    SourceSizedApiLaws.Exact
      (SourceSizedDispatcher.optimizedApi
        (automaton (sortedRows limit states source known choices returned root present) (fun _ _ => true))
        (.inl root)) (Accepts source root) :=
  SourceSizedDeterminizationQueries.closed_ordered_queries_exact states source plain supported known
    (grouped states source choices) (compile_closed limit states source known choices returned) _
    (sorted_permutation limit states source known choices returned root present) root

end MicroCFTA.SourceSizedDeterminizationOrderedOutput
