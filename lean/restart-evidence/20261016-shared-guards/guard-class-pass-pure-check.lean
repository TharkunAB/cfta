import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardIteration
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardOwn

/-!
# Hereditary guards through actual class and pass reads

Each class captures its literal entry forest and clears only its slots.
One class envelope bounds all callback results from immutable source positions.
The pass executes its tail first. The head captures that actual tail return.
No future guard profile, range plan, or completed body is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardClassPass
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads)
open SourceCurrentAllocatedFiniteOrdinaryGuardIteration
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits (Le)
open SourceCurrentAllocatedFiniteOrdinaryGuardTarget (foldLimit)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "NativeGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeGuards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Profile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children

/-- A class uses one common envelope for its captured forest and original inputs. -/
def classLimit (limits : Limits) (record : SourceEqualityClassOrder.Record) : Limits :=
  foldLimit limits (record.paths.length + 1)

/-- A right fold uses the actual tail envelope before the head class. -/
def passLimit (limits : Limits) : List SourceEqualityClassOrder.Record → Limits
  | [] => limits
  | record :: rest => classLimit (passLimit limits rest) record

/-- The ordered pass envelope is the initial vector iterated by the literal class step sum. -/
theorem passLimit_eq (limits : Limits) (records : List SourceEqualityClassOrder.Record) :
    passLimit limits records = foldLimit limits (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.classSteps records) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [passLimit, classLimit, SourceCurrentAllocatedFiniteOrdinaryGuardOwn.classSteps,
        List.map_cons, List.sum_cons] at *
      rw [ih, ← foldLimit_add, Nat.add_comm]

/-- An initial bound on the own class step sum bounds the complete pass envelope. -/
theorem passLimit_le_count (limits : Limits) (records : List SourceEqualityClassOrder.Record) (count : Nat)
    (enough : SourceCurrentAllocatedFiniteOrdinaryGuardOwn.classSteps records ≤ count) :
    Le (passLimit limits records) (foldLimit limits count) := by
  rw [passLimit_eq]
  exact foldLimit_count_mono limits enough

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardClassPass
