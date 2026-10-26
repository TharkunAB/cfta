import MicroCFTA.SourcePruningCallbackExact
import MicroCFTA.SourcePruningEnumerationAfterCallback

namespace MicroCFTA.SourcePruningAfterCallbackExact
open EnumerationState EnumerationCorrectness SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {Typing : Type}

/-- The same actual callback receipt determines exact pruning, stuck rejection or restart.
This theorem does not replace a fuel error by rejection. -/
theorem run_exact (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment) (before : Cached)
    (result : Bool × Metadata Typing) (after : EnumerationState.State Symbol Constraint)
    (callback : Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before.core result after) :
    ExceptT.run (SourcePruningEnumerationAfterCallback.run graph templates stop order fuel metadata uv fragment
      before before.core) =
      if result.1 = true then []
      else if SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame after before) = some .stuck then []
      else [.ok ((result.2, SourcePruningEnumerationRestart.decision stop order result.2
        (EnumerationExpandableIndex.frame after before)), after)] := by
  have exactCallback := SourcePruningCallbackExact.recordTypes_exact graph templates fuel metadata uv
    (.inl fragment) before.core after result callback
  unfold SourcePruningEnumerationAfterCallback.run
  rw [bind_single _ _ _ _ _ exactCallback]
  obtain ⟨pruned, updated⟩ := result
  cases pruned <;> rfl

end MicroCFTA.SourcePruningAfterCallbackExact
