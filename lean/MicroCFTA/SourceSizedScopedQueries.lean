import MicroCFTA.SourceSizedScopedErasure
import MicroCFTA.SourceSizedSharedSorting

/-!
# Determinized queries after scoped guard erasure

The shared determinized sort is built at the original initial state.
The scoped check then justifies its exact queries at another declared
state, with the original constraints in the language specification.

This proves the successful determinization branch. The complete Sized
routing, native storage, and original-input work bounds remain separate.
-/
namespace MicroCFTA.SourceSizedScopedQueries
open Language SourceSizedFiniteKeys SourceSizedDecided Std

/-- Equivalent language predicates preserve every observable exact query law. -/
theorem language_congr {Symbol : Type} [DecidableEq Symbol]
    (api : SourceSizedDispatcher.Api Symbol) (first second : Term Symbol → Prop)
    (precise : SourceSizedApiLaws.Exact api first) (same : ∀ term, first term ↔ second term) :
    SourceSizedApiLaws.Exact api second := by
  have equality : first = second := funext fun term => propext (same term)
  exact equality ▸ precise

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]
  [TransOrd State] [LawfulEqOrd State] [Ord (Sum State (List State))]
  [DecidableEq Symbol] [Ord Symbol]
  [DecidableEq Payload]

/-- Original validation, the scoped check, and returned discovery give exact guarded queries. -/
theorem determinized_exact (limit : Int) (table : Table State Symbol Payload)
    (initial root : State) (neutral : Payload) (holds : Payload → Term Symbol → Bool)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (present : root ∈ SourceDenseRows.keys table)
    (passed : SourceSizedScopedErasure.plainCheck table root neutral = true)
    (holdsNeutral : ∀ term, holds neutral term = true)
    (known : List (List State))
    (choices : List (SourceSizedDeterminizationKernel.Choice State Symbol))
    (returned : SourceSizedDeterminizationTableInput.compile limit table = .ready known choices) :
    SourceSizedApiLaws.Exact
      (SourceSizedDispatcher.optimizedApi
        (automaton (SourceSizedDeterminizationTableInput.sortedRows
          limit table initial success known choices returned) (fun _ _ => true)) (.inl root))
      (Accepts (automaton (lookup table) holds) root) := by
  have valid := SourceSizedSharedSorting.reroot_valid table initial root success present
  have precise := SourceSizedDeterminizationTableInput.queries_exact
    limit table root valid known choices returned
  rw [← SourceSizedSharedSorting.determinized_root_independent
    limit table initial root success valid known choices returned] at precise
  exact language_congr _ _ _ precise fun term =>
    (SourceSizedScopedErasure.erasure_exact table root neutral holds valid passed holdsNeutral term).symm

end MicroCFTA.SourceSizedScopedQueries
