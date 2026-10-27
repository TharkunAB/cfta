import MicroCFTA.SourcePruningEnumerationIsolatedBoundary
import MicroCFTA.SourcePruningEnumerationIsolatedPrefixOperations
import MicroCFTA.SourcePruningEnumerationParkedRestart
import MicroCFTA.SourcePruningEnumerationCachedPrepare

/-!
# Isolation created by actual parking and opaque preparation

Actual selection excludes incoming suspended references before parking.
The true recursion check clears the selected bucket and keeps its native handle.
An opaque child allocates a fresh root with no incoming suspended reference.
An arbitrary clear does not remove references stored in other slots.
-/
namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

/-- A true actual recursion check creates isolation when its selected root has no incoming reference. -/
theorem checkRepeated_created_isolated
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard)
    (ready : EnumerationDriver.Ready uv before)
    (incoming : EnumerationReferences.IncomingAvoid uv before)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before true after) : IsolatedPending uv handle after := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        obtain ⟨same, resolvedSafe, counter, protectedRoot⟩ := EnumerationDriver.representative_root fuel uv root
          before resolved ready.safe ready.inside ready.root resolution
        subst root
        have frame := representative_frame fuel uv uv before resolved ready.safe.1.total resolution
        have resolvedIncoming := EnumerationPendingReplacement.frame_incoming uv before resolved frame incoming
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        subst current currentState
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
        · simp only [seen, ↓reduceIte] at continued
          obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_same, afterSame⟩ := (success_pure true true cleared after).mp returned
          subst after
          have shape := (EnumerationDriver.modify_success _ resolved cleared).mp written
          have inside : uv < resolved.values.length := by
            rw [← resolvedSafe.1.aligned, counter]
            exact ready.inside
          refine ⟨?_, ?_, EnumerationPendingReplacement.setValue_clear_incoming uv uv (some handle)
            resolved cleared resolvedIncoming written⟩
          · simpa only [shape] using protectedRoot.root
          · simpa only [shape] using
              (List.getElem?_set_self inside :
                (resolved.values.set uv (.unenumerated (some handle) []))[uv]? =
                  some (.unenumerated (some handle) []))
        · have impossible : Success (pure false) resolved true after := by
            simpa only [seen, ↓reduceIte] using continued
          obtain ⟨impossible, _same⟩ := (success_pure false true resolved after).mp impossible
          cases impossible
      · have impossible : Success (pure false) before true after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
            Bool.false_eq_true, ↓reduceIte] using observed
        obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
        cases impossible

/-- An external stored reference obstructs isolation after an arbitrary actual clear. -/
theorem referenced_clear_not_isolated
    (target handle source : Nat) (node : Option Nat) (bucket : List Suspended) (sc : Suspended)
    (before after : EnumerationState.State Symbol EnumGuard)
    (different : source ≠ target)
    (stored : before.values[source]? = some (.unenumerated node bucket))
    (listed : sc ∈ bucket) (same : UnionFind.SameClass before.representatives target sc.var)
    (written : Success (setValue target (.unenumerated (some handle) [])) before () after) :
    ¬IsolatedPending target handle after := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  have retained : after.values[source]? = some (.unenumerated node bucket) := by
    simpa only [shape, List.getElem?_set_ne (Ne.symm different)] using stored
  intro isolated
  exact isolated.incoming _ (List.mem_of_getElem? retained) sc listed
    (by simpa only [shape] using same)

section Packet
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The original restart selection creates isolation at its actual attached parked cache. -/
theorem packet_parked_created_isolated
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (before after : Cached)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (readFuel checkFuel indexFuel uv handle : Nat) (scs : List Suspended)
    (readAfter checked : Core)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (reading : Success (getValue readFuel uv) before.core (.unenumerated (some handle) scs) readAfter)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv handle scs) readAfter true checked)
    (adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
      indexFuel uv handle scs before checked = some after) : IsolatedPending uv handle after.core := by
  obtain ⟨ready, incoming, _actualValue⟩ := SourcePruningEnumerationRestart.selected stop order metadata
    caller before uv packet.valid packet.safe chosen
  have frame := (getValue_frame readFuel uv before.core readAfter _ ready.safe.1.total reading).1
  have readReady := (EnumerationDriver.getValue_ready readFuel uv before.core readAfter _ ready reading).1
  have isolated := checkRepeated_created_isolated caller.checked.native.machine.heap checkFuel uv handle scs
    readAfter checked readReady
    (EnumerationPendingReplacement.frame_incoming uv before.core readAfter frame incoming) checking
  rw [SourcePruningEnumerationParkedRestart.adapt_core caller.checked.native.machine.heap
    indexFuel uv handle scs before after checked adapted]
  exact isolated

/-- Actual opaque preparation creates a disabled isolated fresh root from the original packet. -/
theorem packet_boundary_prepare_created_isolated
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (before after : Cached)
    (value : Value Symbol Constraint) (scs : List Suspended) (fuel : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (observed : SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap
      fuel scs value before = some [(.hole before.core.counter, after)]) :
    ∃ handle, encodeNode value = some handle ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      IsolatedPending before.core.counter handle after.core ∧ after.expandable before.core.counter = false := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨handle, action, canonical, encoded, decoded, _prepared, running, _raw, shape, _stored,
    _growth, _aligned, _forest, _paths, _storage, _realized, _counts, _waiting, _sameFlags,
    returnedFlags, _holeBound⟩ := SourcePruningEnumerationCachedPrepare.boundary_complete
      caller.checked.native.machine.heap before value scs roots
      packet.context.ready.semantic.ready.semantic.1.normal.facts.coherent available closed boundary nonterminal
      storage realized paths counts flags
  have rowsSame := Option.some.inj ((running fuel).symm.trans observed)
  have afterSame : canonical = after := (Prod.mk.inj (List.cons.inj rowsSame).1).2
  rw [← afterSame]
  have isolated : IsolatedPending before.core.counter handle canonical.core := by
    rw [shape]
    exact allocated_isolated before.core handle packet.safe
  exact ⟨handle, encoded, decoded, isolated,
    isolated.disabled caller.checked.native.machine.heap canonical before.core.counter handle value
      decoded boundary returnedFlags⟩

end Packet
end MicroCFTA.EnumerationDischargeHistory
