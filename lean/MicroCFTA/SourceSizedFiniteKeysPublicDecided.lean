import MicroCFTA.SourceSizedFiniteKeysPublic
import MicroCFTA.SourceSizedDecidedOperational
import MicroCFTA.SourceSizedFiniteKeysCanonical

/-!
# Decided Sized traces over validated finite row-map keys

Evaluator replies can vary between occurrences. Completed successful traces
have exactly the original guarded table language through the signed bound.
Completion requires finite per-call outcomes, not a finite original state
type and not a stable reply function.
-/
namespace MicroCFTA.SourceSizedFiniteKeysPublic
open Language RecursiveSize SourceSizedFiniteKeys SourceSizedDecided
open SourceSizedDecidedPublic SourceSizedDecidedExecution SourceSizedPreprocessing

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State] [DecidableEq Symbol] [Ord Symbol]

/-- Run the actual sorted and trimmed bounded worker on the carrier derived by validation. -/
abbrev DecidedRun (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (evaluates : Payload × Term Symbol → Nat → Guards.Verdict → Prop) (bound : Int)
    (result : Except (Payload × Term Symbol)
      (SourceSizedDecidedTable.Table (SourceDenseRows.Member (SourceDenseRows.keys table)) (Term Symbol)))
    (work : Nat) : Prop :=
  SizesRun (ClassRun (sortedRows (input table root valid)) evaluates) (reached (input table root valid)) bound.toNat result work

/-- A successful trace is exact, canonically ordered, and invertible on original accepted terms. -/
theorem decided_correct [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (evaluates : Payload × Term Symbol → Nat → Guards.Verdict → Prop)
    (holds : Payload → Term Symbol → Bool)
    (adequate : SourceSizedDecidedOperational.Adequate evaluates (fun pair => holds pair.1 pair.2))
    (bound : Int) (output : SourceSizedDecidedTable.Table (SourceDenseRows.Member (SourceDenseRows.keys table)) (Term Symbol))
    (work : Nat) (run : DecidedRun table root valid evaluates bound (.ok output) work) :
    let terms := output (input table root valid).root
    (∀ size term, term ∈ terms size ↔ Accepts (automaton (lookup table) holds) root term ∧
      nodeSize term = size ∧ (size : Int) ≤ bound) ∧
    (∀ size, terms size = if size ≤ bound.toNat then
      SourceSizedReference.classes (automaton (nativeSorted table root valid) holds) size root else []) ∧
    (∀ throughSize, (SourceSizedQueries.through terms throughSize).Nodup ∧
      (SourceSizedQueries.through terms throughSize).Pairwise (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ throughSize term, term ∈ SourceSizedQueries.through terms throughSize ↔
      Accepts (automaton (lookup table) holds) root term ∧ (nodeSize term : Int) ≤ bound ∧ nodeSize term ≤ throughSize) ∧
    (∀ term size rank, SourceSizedQueries.rankSigned terms nodeSize term = some (size, rank) ↔
      SourceSizedQueries.unrankSigned terms size rank = some term) := by
  dsimp only
  have pureRun := SourceSizedDecidedOperational.sizes_success (sortedRows (input table root valid))
    (reached (input table root valid)) evaluates holds adequate run output rfl
  let answer := SourceSizedDecidedOperational.ideal (Function.uncurry holds)
  have pureAdequate := SourceSizedDecidedOperational.ideal_adequate (Function.uncurry holds)
  have membership : ∀ size term, term ∈ output (input table root valid).root size ↔
      Accepts (automaton (lookup table) holds) root term ∧ nodeSize term = size ∧ (size : Int) ≤ bound := by
    intro size term
    rw [SourceSizedDecidedOperational.public_member_iff (input table root valid) evaluates holds adequate bound output work run,
      input_language]
  refine ⟨membership, ?_, ?_, ?_, ?_⟩
  · intro size
    have order := SourceSizedDecidedOperational.public_reference_order (input table root valid) evaluates holds adequate bound output work run size
    have sorted := sorted_classes_exact table root valid holds (input table root valid).root size
    change SourceSizedReference.classes (automaton (sortedRows (input table root valid)) holds) size (input table root valid).root =
      SourceSizedReference.classes (automaton (nativeSorted table root valid) holds) size root at sorted
    rw [order, sorted]
  · intro throughSize
    exact ⟨SourceSizedDecidedQueries.enumeration_nodup _ _ answer holds pureAdequate bound.toNat output pureRun _ throughSize,
      SourceSizedDecidedQueries.size_ordered _ _ answer holds pureAdequate bound.toNat output pureRun _ throughSize⟩
  · intro throughSize term
    rw [SourceSizedQueries.mem_prefix]
    constructor
    · rintro ⟨size, below, present⟩
      obtain ⟨accepted, sized, bounded⟩ := (membership size term).mp present
      exact ⟨accepted, by omega, by omega⟩
    · rintro ⟨accepted, bounded, below⟩
      exact ⟨nodeSize term, below, (membership _ term).mpr ⟨accepted, rfl, bounded⟩⟩
  · intro term size rank
    exact ⟨SourceSizedDecidedQueries.unrankSigned_rankSigned _ _ answer holds pureAdequate bound.toNat output pureRun _ term size rank,
      SourceSizedDecidedQueries.rankSigned_unrankSigned _ _ answer holds pureAdequate bound.toNat output pureRun _ term size rank⟩

/-- Finite evaluator outcomes suffice for every bounded query on the actual finite table keys. -/
theorem decided_finite (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (evaluates : Payload × Term Symbol → Nat → Guards.Verdict → Prop)
    (completed : SourceSizedDecidedOperational.Terminates evaluates) (bound : Int) :
    ∃ result work, DecidedRun table root valid evaluates bound result work :=
  SourceSizedDecidedOperational.public_finite (input table root valid) evaluates completed bound

end MicroCFTA.SourceSizedFiniteKeysPublic
