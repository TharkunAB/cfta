import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryShared
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputStored

/-!
# Causal profiles in actual class-local target slots

The class fixes a row, arity, and height bound for every stored target.
Fresh slots derive this obligation without a returned-value assumption.
A store needs the certificate produced for its actual new target.
Checked advancement retains immutable slot profiles and the Merge table.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfiles
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedSharedTargetState (State)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "MergeProfiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
variable {width rows arity bound : Nat}

/-- Completed native, Merge, and class slots retain their own output certificates. -/
structure Stored (rows arity bound : Nat) (state : State width) : Prop where
  native : NativeStored state.checked.native
  output : OutputStored state.checked.native
  merge : MergeProfiles state.memo
  slots : ∀ path value, state.targets path = some value → NodeShape rows arity value ∧ height value ≤ bound

/-- A fresh class keeps warm native and Merge tables and has no stored target to certify. -/
theorem initial_stored (checked : Checked width) (memo : Memo)
    (native : NativeStored checked.native) (output : OutputStored checked.native) (merged : MergeProfiles memo) :
    Stored rows arity bound (SourceCurrentAllocatedSharedTargetState.initial checked memo) :=
  ⟨native, output, merged, by intro path value absent; cases absent⟩

/-- Checked execution changes native certificates while retaining every immutable slot. -/
theorem advance_stored (state : State width) (checked : Checked width) (stored : Stored rows arity bound state)
    (native : NativeStored checked.native) (output : OutputStored checked.native) :
    Stored rows arity bound (SourceCurrentAllocatedSharedTargetState.advance state checked) :=
  ⟨native, output, stored.merge, stored.slots⟩

/-- Constructor and equality-operation advancement retains the actual native result tables. -/
theorem physical_stored (state : State width) (after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula)
    (stored : Stored rows arity bound state) :
    Stored rows arity bound (SourceCurrentAllocatedSharedTargetState.advance state
      (SourceCurrentAllocatedQueryMemo.advancePhysical state.checked after)) :=
  advance_stored state _ stored
    (SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ stored.native)
    (SourceCurrentAllocatedFiniteOrdinaryOutputStored.advance_stored _ _ stored.output)

/-- The exact new target certificate is stored beside all earlier slot certificates. -/
theorem store_stored (state : State width) (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (checked : Checked width) (memo : Memo) (stored : Stored rows arity bound state)
    (native : NativeStored checked.native) (output : OutputStored checked.native) (merged : MergeProfiles memo)
    (profile : NodeShape rows arity value) (heightBound : height value ≤ bound) :
    Stored rows arity bound (SourceCurrentAllocatedSharedTargetState.store state path value checked memo) := by
  refine ⟨native, output, merged, ?_⟩
  intro other result found
  by_cases same : other = path
  · subst other
    have resultSame : value = result := Option.some.inj (by
      simpa only [SourceCurrentAllocatedSharedTargetState.store, put, ite_true] using found)
    exact resultSame ▸ ⟨profile, heightBound⟩
  · exact stored.slots other result (by
      simpa only [SourceCurrentAllocatedSharedTargetState.store, put, same, ite_false] using found)

/-- Profile certificates imply the existing structural native, Merge, and slot invariant. -/
theorem Stored.domain {state : State width} (stored : Stored rows arity bound state) :
    SourceCurrentAllocatedFiniteOrdinaryShared.Stored state :=
  ⟨stored.native, stored.merge.domain, fun path value found => NodeShape.domain value (stored.slots path value found).1⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfiles
