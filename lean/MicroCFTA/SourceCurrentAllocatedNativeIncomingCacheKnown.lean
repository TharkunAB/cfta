import MicroCFTA.SourceCurrentAllocatedNativeIncomingOldKnown
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

/-!
# Actual incoming cache preserves whole ordinary-value bounds

The empty raw branch writes the actual Empty target.
The local incoming domain and height gates are explicit current input facts.
The actual worker source-builder certification remains separate.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceCurrentAllocatedNativeIncomingCacheKnown
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))

private theorem adapt_known (bound : Nat) (heap : State Symbol Constraint)
    (indexFuel target : Nat) (incomingScs : List EnumerationState.Suspended)
    (before : Cached) (read : Core) (raw : Raw)
    (oldKnown : KnownOrdinary bound heap before) (sameValues : read.values = before.core.values)
    (rowsKnown : ∀ returned : Core, Except.ok ((), returned) ∈ raw →
      KnownOrdinary bound heap {before with core := returned})
    (after : Cached)
    (adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt heap indexFuel target incomingScs before read raw = some after) :
    KnownOrdinary bound heap after := by
  cases raw with
  | nil =>
      simp only [SourcePruningEnumerationIncomingCacheAdapter.adapt] at adapted
      cases slot : read.values[target]? with
      | none => simp only [slot] at adapted; cases adapted
      | some value =>
          cases value with
          | enumerated _fragment => simp only [slot] at adapted; cases adapted
          | eliminated => simp only [slot] at adapted; cases adapted
          | unenumerated _node oldScs =>
              simp only [slot, Option.map_eq_some_iff] at adapted
              obtain ⟨cached, _written, same⟩ := adapted
              subst after
              intro handle scs member
              change EnumerationState.UVarValue.unenumerated (some handle) scs ∈
                read.values.set target (.unenumerated (some 0) (incomingScs ++ oldScs)) at member
              rcases List.mem_or_eq_of_mem_set member with old | replacement
              · rw [sameValues] at old
                exact oldKnown handle scs old
              · have handleSame : handle = 0 :=
                  Option.some.inj (EnumerationState.UVarValue.unenumerated.inj replacement).1
                subst handle
                exact ⟨.empty, rfl, .empty, by simp [MergedOrdinaryHeight.height]⟩
  | cons first tail =>
      cases first with
      | error _fault => simp only [SourcePruningEnumerationIncomingCacheAdapter.adapt] at adapted; cases adapted
      | ok pair =>
          rcases pair with ⟨valueUnit, returned⟩
          cases valueUnit
          cases tail with
          | cons _second _remaining =>
              simp only [SourcePruningEnumerationIncomingCacheAdapter.adapt] at adapted
              cases adapted
          | nil =>
              have coreSame := SourcePruningEnumerationIncomingCacheAdapter.adapt_singleton_core
                heap indexFuel target incomingScs before after read returned adapted
              intro handle scs member
              change EnumerationState.UVarValue.unenumerated (some handle) scs ∈ after.core.values at member
              rw [coreSame] at member
              exact rowsKnown returned (by simp) handle scs member

variable [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- The literal incoming read keeps the original values on every outcome. -/
theorem read_values (width : Nat) (checkEmpty : Bool) (r n p h uv : Nat)
    (beforeCaller : Caller width) (before : Core) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (queries : SourceEndpointMemo.Memos) :
    (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h beforeCaller before uv incoming incomingScs queries).2.2.2.values =
      before.values := by
  unfold SourcePruningEnumerationIncomingNode.run
  repeat' (first | rfl | (split <;> try dsimp only))

open scoped Classical in
/-- Actual incoming raw rows and returned caches keep the same whole ordinary cap. -/
theorem run_known (bits bound : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h indexFuel uv : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos) (queries : SourceEndpointMemo.Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingDomain : NodeDomain incoming) (incomingHeight : MergedOrdinaryHeight.height incoming ≤ bound)
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before)
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : Stored beforeCaller.checked.native) :
    let actual := SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h indexFuel
      beforeCaller before uv incoming incomingScs queries
    (match actual.1.1 with
      | .ok (some rows) => ∀ after : Core, Except.ok ((), after) ∈ rows →
          KnownOrdinary bound actual.1.2.1.checked.native.machine.heap {before with core := after}
      | _ => True) ∧
    (match actual.2 with
      | some after => KnownOrdinary bound actual.1.2.1.checked.native.machine.heap after
      | none => True) := by
  classical
  have fresh := SourceCurrentAllocatedNativeIncomingKnown.run_known bits bound profile formulas solver inventory
    beforeCaller before checkEmpty r n p h uv incoming incomingScs memos queries initial realized available closed
    incomingDomain incomingHeight known fits room stored
  have old := SourceCurrentAllocatedNativeIncomingOldKnown.run_old_known_except_failed_check bits bound profile
    formulas solver inventory beforeCaller before checkEmpty r n p h uv incoming incomingScs memos queries
    initial realized available closed known fits room stored
  have readSame := read_values (bits + 2) checkEmpty r n p h uv beforeCaller before.core incoming incomingScs queries
  simp only [SourcePruningEnumerationIncomingCacheAdapter.run]
  generalize observed : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    beforeCaller before.core uv incoming incomingScs queries = result
  rcases result with ⟨tag, reachedCaller, savedQueries, read⟩
  cases tag with
  | error _fault => exact ⟨trivial, trivial⟩
  | ok possible =>
      cases possible with
      | none => exact ⟨trivial, trivial⟩
      | some rows =>
          have oldKnown : KnownOrdinary bound reachedCaller.checked.native.machine.heap before := by
            simpa only [observed] using old.2
          have rowsKnown : ∀ returned : Core, Except.ok ((), returned) ∈ rows →
              KnownOrdinary bound reachedCaller.checked.native.machine.heap {before with core := returned} := by
            simpa only [observed] using fresh.2
          have valuesSame : read.values = before.core.values := by
            simpa only [observed] using readSame
          refine ⟨rowsKnown, ?_⟩
          change (match SourcePruningEnumerationIncomingCacheAdapter.adapt
              reachedCaller.checked.native.machine.heap indexFuel uv incomingScs before read rows with
            | some after => KnownOrdinary bound reachedCaller.checked.native.machine.heap after
            | none => True)
          cases adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt
              reachedCaller.checked.native.machine.heap indexFuel uv incomingScs before read rows with
          | none => trivial
          | some after =>
              exact adapt_known bound reachedCaller.checked.native.machine.heap indexFuel uv incomingScs
                before read rows oldKnown valuesSame rowsKnown after adapted

end MicroCFTA.SourceCurrentAllocatedNativeIncomingCacheKnown
