import MicroCFTA.SourcePruningEnumerationAssimilation
import MicroCFTA.EnumerationValidity

/-!
# Canonical suspended tries through native pending assimilation

The proof uses the actual stored source and target buckets.
Canonicality does not imply Safe and also permits a logical Empty slot.
-/
namespace MicroCFTA.SourcePruningEnumerationAssimilation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics EnumerationValidity
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {EnumGuard : Type}

/-- The actual two writes concatenate canonical buckets and eliminate the source. -/
theorem assimilated_canonical
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat)
    (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended)
    (canonical : Canonical before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs)) :
    Canonical (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) := by
  have sourceValid : ValidSuspended sourceScs :=
    canonical (.unenumerated sourceNode sourceScs) (List.mem_of_getElem? sourceStored)
  have targetValid : ValidSuspended targetScs :=
    canonical (.unenumerated targetNode targetScs) (List.mem_of_getElem? targetStored)
  have mergedValid : ValidSuspended
      (references (.unenumerated merged (sourceScs ++ targetScs) : UVarValue Symbol)) := by
    intro sc member
    rcases List.mem_append.mp member with fromSource | fromTarget
    · exact sourceValid sc fromSource
    · exact targetValid sc fromTarget
  have targetWritten := set_canonical target (.unenumerated merged (sourceScs ++ targetScs))
    before canonical mergedValid
  have sourceWritten := set_canonical source .eliminated
    {before with values := before.values.set target (.unenumerated merged (sourceScs ++ targetScs))}
    targetWritten (by simp [references, ValidSuspended])
  exact sourceWritten

/-- Every actual successful nonempty finish preserves canonical suspended tries. -/
theorem finish_canonical
    (before after : EnumerationState.State Symbol EnumGuard) (source target resultHandle : Nat)
    (sourceNode targetNode : Option Nat) (sourceScs targetScs : List Suspended)
    (result : InternedConstructorTemplates.Value Symbol Constraint)
    (canonical : Canonical before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (success : Success (finish source target resultHandle sourceScs targetScs result) before () after) :
    Canonical after := by
  cases result <;> first
    | exact (reject_unsuccessful before after () success).elim
    | have endpoint : after = assimilated before target source
          (.unenumerated (some resultHandle) (sourceScs ++ targetScs)) := by
        change Except.ok ((), after) ∈ [Except.ok ((), assimilated before target source
          (.unenumerated (some resultHandle) (sourceScs ++ targetScs)))] at success
        simpa only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq, true_and] using success
      rw [endpoint]
      exact assimilated_canonical before source target sourceNode targetNode (some resultHandle)
        sourceScs targetScs canonical sourceStored targetStored

end MicroCFTA.SourcePruningEnumerationAssimilation
