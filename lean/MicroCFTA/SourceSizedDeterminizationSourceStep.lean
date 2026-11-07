import MicroCFTA.SourceSizedDeterminizationPositionTuples
import MicroCFTA.SourceSizedDeterminizationTableInput

/-!
# Literal source step entries

The source reads each ordered token bucket, generates positional tuples,
sorts the tuple set, and computes each target with the zip predicate.
The entry list below retains that schedule. Its exact readback supplies
the choices and found keys used by the proved source loop.
Native map storage and total work remain separate.
-/
namespace MicroCFTA.SourceSizedDeterminizationSourceStep
open Language SourceSizedDeterminizationKernel Std
attribute [local instance] lexOrd

/-- Token-bucket children retain exactly the original seed sequence. -/
theorem members_seeds {State Symbol : Type} [DecidableEq Symbol]
    (states : List State) (rows : Automaton State Symbol) (wanted : Symbol × Nat) :
    (SourceSizedDeterminizationZipTarget.members states rows wanted).map
        (fun entry => entry.2.children) =
      SourceSizedDeterminizationStep.seeds states rows wanted := by
  simp [SourceSizedDeterminizationZipTarget.members, SourceSizedDeterminizationStep.seeds,
    List.map_flatMap, List.map_map, Function.comp_def]

variable {State Symbol Payload : Type} [DecidableEq State] [DecidableEq Symbol] [Ord State]

/-- Read the source set of positional tuples for one original token bucket. -/
def tupleSet (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (fresh : List (List State)) (holding : State → List (List State))
    (known : List (List State)) (wanted : Symbol × Nat) : List (List (List State)) :=
  CanonicalClasses.sortedSet
    (((SourceSizedDeterminizationZipTarget.members (SourceDenseRows.keys table)
      (SourceSizedDeterminizationTableInput.rows table) wanted).map
        (fun entry => entry.2.children)).flatMap
          (SourceSizedDeterminizationPositionTuples.tuples fresh holding known))

/-- Literal source positional tuples give exactly the ordered controller's tuple set. -/
theorem tupleSet_readback [TransOrd State] [LawfulEqOrd State]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (fresh : List (List State)) (holding : State → List (List State))
    (known : List (List State)) (wanted : Symbol × Nat) :
    tupleSet table fresh holding known wanted =
      SourceSizedDeterminizationOrderedStep.tupleSet (SourceDenseRows.keys table)
        (SourceSizedDeterminizationTableInput.rows table) fresh holding known wanted := by
  unfold tupleSet
  rw [members_seeds, SourceSizedDeterminizationPositionTuples.sorted_seeds_eq]
  rfl

variable [Ord Symbol]

/-- Emit each source target and transition in token order and tuple-set order. -/
def entries (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State)) :
    List (List State × Choice State Symbol) :=
  (SourceSizedDeterminizationOrderedStep.tokens (SourceDenseRows.keys table)
    (SourceSizedDeterminizationTableInput.rows table)).flatMap fun wanted =>
      (tupleSet table fresh holding known wanted).map fun keys =>
        (SourceSizedDeterminizationZipTarget.sourceTarget (SourceDenseRows.keys table)
          (SourceSizedDeterminizationTableInput.rows table) wanted keys, (wanted.1, keys))

/-- Literal source entries retain every ordered choice and its exact computed target. -/
theorem entries_readback [TransOrd State] [LawfulEqOrd State]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State)) :
    entries table fresh holding known =
      (SourceSizedDeterminizationOrderedStep.round (SourceDenseRows.keys table)
        (SourceSizedDeterminizationTableInput.rows table) fresh holding known).map fun choice =>
          (target (SourceDenseRows.keys table) (SourceSizedDeterminizationTableInput.rows table)
            choice.1 choice.2, choice) := by
  simp only [entries, SourceSizedDeterminizationOrderedStep.round, List.map_flatMap,
    List.map_map, Function.comp_def]
  apply congrArg (fun generate : (Symbol × Nat) → List (List State × Choice State Symbol) =>
    (SourceSizedDeterminizationOrderedStep.tokens (SourceDenseRows.keys table)
      (SourceSizedDeterminizationTableInput.rows table)).flatMap generate)
  funext wanted
  rw [tupleSet_readback]
  apply List.map_congr_left
  intro keys present
  rw [SourceSizedDeterminizationTableInput.generated_source_target_eq table fresh holding known wanted keys present]

/-- Literal source step entries supply exactly the loop's ascending found-key sequence. -/
theorem foundKeys_readback [TransOrd State] [LawfulEqOrd State]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State)) :
    CanonicalClasses.sortedSet ((entries table fresh holding known).map Prod.fst) =
      SourceSizedDeterminizationOrderedRun.foundKeys (SourceDenseRows.keys table)
        (SourceSizedDeterminizationTableInput.rows table)
        (SourceSizedDeterminizationOrderedStep.round (SourceDenseRows.keys table)
          (SourceSizedDeterminizationTableInput.rows table) fresh holding known) := by
  rw [entries_readback]
  simp only [List.map_map, Function.comp_def, SourceSizedDeterminizationOrderedRun.foundKeys,
    SourceSizedDeterminizationRun.targets]

end MicroCFTA.SourceSizedDeterminizationSourceStep
