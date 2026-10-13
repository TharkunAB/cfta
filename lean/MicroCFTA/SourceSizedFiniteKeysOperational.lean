import MicroCFTA.SourceSizedFiniteKeysExecution
import MicroCFTA.SourceSizedLiquidExecutionPublic

/-!
# Original-state bounded IO traces through finite key readback

Occurrence work and every stopping outcome survive state restriction.
The proof reads each frozen raw table through the injective finite keys.
It does not require deterministic evaluator replies or successful outcomes.
-/
namespace MicroCFTA.SourceSizedFiniteKeysOperational
open Language SourceSizedDecided SourceSizedDecidedTable SourceSizedDecidedExecution
open SourceSizedFiniteKeysExecution

/-- Complete original-state class traces induce the same finite state pass and work count. -/
theorem states_pull [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode)
    (source : Table Source Value → Nat → Source → Except Error (List Value) → Nat → Prop)
    (target : Table Target Value → Nat → Target → Except Error (List Value) → Nat → Prop)
    (same : ∀ smaller size state result work, target smaller size (encode state) result work →
      source (pull encode smaller) size state result work)
    (states : List Source) (smaller built : Table Target Value) (size : Nat) (result work)
    (run : StatesRun target smaller size (states.map encode) built result work) :
    StatesRun source (pull encode smaller) size states (pull encode built) (result.map (pull encode)) work := by
  induction states generalizing built result work with
  | nil => cases run; exact .nil
  | cons state rest ih =>
    cases run with
    | error completed => exact .error (same _ _ _ _ _ completed)
    | ok completed tail =>
      have following := ih _ _ _ tail
      rw [insert_pull encode injective] at following
      exact .ok (same _ _ _ _ _ completed) following

/-- Every size trace preserves its output or first error at exactly the same finite work. -/
theorem sizes_pull [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode)
    (source : Table Source Value → Nat → Source → Except Error (List Value) → Nat → Prop)
    (target : Table Target Value → Nat → Target → Except Error (List Value) → Nat → Prop)
    (same : ∀ smaller size state result work, target smaller size (encode state) result work →
      source (pull encode smaller) size state result work)
    (states : List Source) (bound : Nat) (result work)
    (run : SizesRun target (states.map encode) bound result work) :
    SizesRun source states bound (result.map (pull encode)) work := by
  induction run with
  | zero => exact .zero
  | error prior ih => exact .error ih
  | next prior next ih =>
    exact .next ih (states_pull encode injective source target same states _ _ _ _ _ next)

/-- Candidate readback preserves an actual returned-verdict class trace with varying replies. -/
theorem decided_class_pull [DecidableEq Symbol] (encode : Source → Target)
    (source : Source → List (Row Source Symbol Payload)) (target : Target → List (Row Target Symbol Payload))
    (same : ∀ state, target (encode state) = (source state).map (renameRow encode))
    (evaluates : Payload × Term Symbol → Nat → Guards.Verdict → Prop)
    (smaller : Table Target (Term Symbol)) (size : Nat) (state : Source) (result work)
    (run : SourceSizedDecided.ClassRun target evaluates smaller size (encode state) result work) :
    SourceSizedDecided.ClassRun source evaluates (pull encode smaller) size state result work := by
  cases run with
  | done filtered =>
    rw [pairs_pull encode source target same] at filtered
    exact .done filtered

/-- Unknown and unchanged exceptions retain the exact complete constraint trace. -/
theorem liquid_class_pull [DecidableEq Symbol] (encode : Source → Target)
    (source : Source → List (Row Source Symbol Payload)) (target : Target → List (Row Target Symbol Payload))
    (same : ∀ state, target (encode state) = (source state).map (renameRow encode))
    (evaluates : Payload × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (smaller : Table Target (Term Symbol)) (size : Nat) (state : Source) (result work)
    (run : SourceSizedLiquidExecution.ClassRun target evaluates smaller size (encode state) result work) :
    SourceSizedLiquidExecution.ClassRun source evaluates (pull encode smaller) size state result work := by
  cases run with
  | done filtered =>
    rw [pairs_pull encode source target same] at filtered
    exact .done filtered

/-- Restriction retains the complete bounded liquid execution, including both stopping forms. -/
theorem liquid_sizes_pull [DecidableEq Source] [DecidableEq Target] [DecidableEq Symbol]
    (encode : Source → Target) (injective : Function.Injective encode)
    (source : Source → List (Row Source Symbol Payload)) (target : Target → List (Row Target Symbol Payload))
    (same : ∀ state, target (encode state) = (source state).map (renameRow encode))
    (evaluates : Payload × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (states : List Source) (bound : Nat) (result work)
    (run : SizesRun (SourceSizedLiquidExecution.ClassRun target evaluates) (states.map encode) bound result work) :
    SizesRun (SourceSizedLiquidExecution.ClassRun source evaluates) states bound (result.map (pull encode)) work :=
  sizes_pull encode injective _ _ (liquid_class_pull encode source target same evaluates) states bound result work run

open SourceDenseRows SourceSizedPreprocessing SourceSizedDecidedPublic Std
attribute [local instance] lexOrd

/-- Raw-state source traces transfer to the exact finite public input after dense canonical sorting. -/
theorem native_public [DecidableEq State] [Ord State] [DecidableEq Symbol] [Ord Symbol]
    [TransOrd Symbol] [LawfulEqOrd Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted table (fun _ _ => true)))
    (evaluates : Payload × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (bound : Nat) (result work)
    (run : SizesRun (SourceSizedLiquidExecution.ClassRun (SourceSizedFiniteKeys.nativeSorted table root valid) evaluates)
      ((reached (SourceSizedFiniteKeys.input table root valid)).map Subtype.val) bound result work) :
    SizesRun (SourceSizedLiquidExecution.ClassRun (sortedRows (SourceSizedFiniteKeys.input table root valid)) evaluates)
      (reached (SourceSizedFiniteKeys.input table root valid)) bound (result.map (pull Subtype.val)) work :=
  liquid_sizes_pull Subtype.val (fun _ _ same => Subtype.ext same) _ _
    (fun state => (SourceSizedFiniteKeys.sorted_readback table root valid state).symm) evaluates _ bound result work run

end MicroCFTA.SourceSizedFiniteKeysOperational
