import MicroCFTA.SourcePruningEnumerationSelectedStep
import MicroCFTA.SourcePruningNarrowSlotTransport

/-!
# Slot control from an actual selected-prefix observation

The narrowed tag retains its checked core and returned cache.
A difference between those observed cores excludes the unchanged action.
Intermediate equations follow from the literal prefix, not a future trace.

-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourcePruningNativeView SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

local instance prefixObservationMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem prepare_equal_handle_success_core
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel uv handle : Nat)
    (scs : List Suspended) (value result : Node)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (checked observed : Core) (action : EnumerateM Symbol Constraint Unit)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv handle scs value heap = .done (result, some action) nextHeap)
    (encoded : encodeNode result = some handle) (succeeded : Success action checked () observed) :
    observed = checked := by
  cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv value heap with
  | failed =>
      simp only [SourcePruningEnumerationAction.prepare, narrowed] at prepared
      cases prepared
  | done candidate reached =>
      simp only [SourcePruningEnumerationAction.prepare, narrowed] at prepared
      have paired := MergedSourceComparison.Result.done.inj prepared
      have sameValue : candidate = result := congrArg Prod.fst paired.1
      subst candidate
      have sameAction := congrArg Prod.snd paired.1
      cases result with
      | empty =>
          have rejected : action = (reject : EnumerateM Symbol Constraint Unit) := (Option.some.inj sameAction).symm
          rw [rejected] at succeeded
          simp [Success, reject, ExceptT.run] at succeeded
      | reference => simp only [encodeNode] at encoded; cases encoded
      | node | union | mu =>
          have same : some (pure () : EnumerateM Symbol Constraint Unit) = some action := by
            simpa only [encoded, ite_true] using sameAction
          rw [← Option.some.inj same] at succeeded
          exact ((success_pure () () checked observed).mp succeeded).2

/-- The retained changed-core narrowed/Right tag derives every actual filter-stage observation. -/
theorem prefix_changed_stages
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata updated : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller reached : Caller width) (before after : Cached) (queries receivedQueries : Queries)
    (checked observed callbackCore : Core) (result : Node)
    (nextHeap : InternedConstructorTemplates.State Symbol Constraint) (action : EnumerateM Symbol Constraint Unit)
    (prefixObserved : runPrefix holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel uv caller before queries =
      .narrowed checked (.done (result, some action) nextHeap) reached receivedQueries
        (some [.ok ((), observed)]) (some after) (some [.ok ((false, updated), callbackCore)]) none)
    (changedCore : after.core ≠ checked) :
    ∃ (oldHandle newHandle : Nat) (scs : List Suspended) (oldValue : Node) (readAfter : Core),
      ExceptT.run (getValue readFuel uv before.core) = [.ok (.unenumerated (some oldHandle) scs, readAfter)] ∧
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)] ∧
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
        uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (result, some action) nextHeap ∧
      encodeNode result = some newHandle ∧ newHandle ≠ oldHandle ∧
      ExceptT.run (action checked) = [.ok ((), observed)] ∧
      SourcePruningEnumerationNarrowAdapter.adapt nextHeap indexFuel uv oldHandle newHandle scs before observed = some after ∧
      after.core = observed ∧ callbackCore = observed ∧ updated = metadata ∧
      reached.checked.native.machine.heap = nextHeap := by
  unfold runPrefix at prefixObserved
  dsimp only at prefixObserved
  generalize readEq : ExceptT.run (getValue readFuel uv before.core) = read at prefixObserved
  cases read with
  | nil => cases prefixObserved
  | cons first rest =>
      cases rest with
      | cons _ _ =>
          cases first with
          | error _ => cases prefixObserved
          | ok pair =>
              obtain ⟨value, _readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => cases prefixObserved
              | unenumerated handle _ => cases handle <;> cases prefixObserved
      | nil =>
          cases first with
          | error _ => cases prefixObserved
          | ok pair =>
              obtain ⟨value, readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => cases prefixObserved
              | unenumerated handle scs =>
                  cases handle with
                  | none => cases prefixObserved
                  | some oldHandle =>
                      dsimp only at prefixObserved
                      generalize checkEq : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
                        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = check at prefixObserved
                      cases check with
                      | nil => cases prefixObserved
                      | cons first rest =>
                          cases rest with
                          | cons _ _ =>
                              cases first with
                              | error _ => cases prefixObserved
                              | ok pair =>
                                  obtain ⟨repeated, _checked⟩ := pair
                                  cases repeated <;> cases prefixObserved
                          | nil =>
                              cases first with
                              | error _ => cases prefixObserved
                              | ok pair =>
                                  obtain ⟨repeated, actualChecked⟩ := pair
                                  cases repeated with
                                  | true => cases prefixObserved
                                  | false =>
                                      generalize decodedEq : lookupNode caller.checked.native.machine.heap oldHandle = decoded at prefixObserved
                                      cases decoded with
                                      | none => cases prefixObserved
                                      | some oldValue =>
                                          dsimp only at prefixObserved
                                          generalize preparedEq : SourcePruningEnumerationAction.prepare holeKey fits admits metadata
                                            nativeFuel representativeFuel uv oldHandle scs oldValue
                                            caller.checked.native.machine.heap = prepared at prefixObserved
                                          cases prepared with
                                          | failed _ _ => cases prefixObserved
                                          | done pair nativeAfter =>
                                              obtain ⟨nativeResult, possibleAction⟩ := pair
                                              cases possibleAction with
                                              | none => cases prefixObserved
                                              | some actualAction =>
                                                  dsimp only at prefixObserved
                                                  generalize actionEq : ExceptT.run (actualAction actualChecked) = raw at prefixObserved
                                                  cases raw with
                                                  | nil => cases prefixObserved
                                                  | cons first rest =>
                                                      cases rest with
                                                      | cons _ _ =>
                                                          cases first with
                                                          | error _ => cases prefixObserved
                                                          | ok pair =>
                                                              obtain ⟨token, _observed⟩ := pair
                                                              cases token
                                                              cases prefixObserved
                                                      | nil =>
                                                          cases first with
                                                          | error _ => cases prefixObserved
                                                          | ok pair =>
                                                              obtain ⟨token, actualObserved⟩ := pair
                                                              cases token
                                                              dsimp only at prefixObserved
                                                              generalize encodedEq : encodeNode nativeResult = encoded at prefixObserved
                                                              cases encoded with
                                                              | none => cases prefixObserved
                                                              | some newHandle =>
                                                                  dsimp only at prefixObserved
                                                                  generalize adaptedEq : SourcePruningEnumerationNarrowAdapter.adapt nativeAfter
                                                                    indexFuel uv oldHandle newHandle scs before actualObserved = adapted at prefixObserved
                                                                  cases adapted with
                                                                  | none => cases prefixObserved
                                                                  | some attached =>
                                                                      rw [SourcePruningRecordTypes.recordTypes_inr] at prefixObserved
                                                                      have same := Result.narrowed.inj prefixObserved
                                                                      have checkedSame := same.1
                                                                      have preparedSame := MergedSourceComparison.Result.done.inj same.2.1
                                                                      have resultSame : nativeResult = result := congrArg Prod.fst preparedSame.1
                                                                      have actionSame := Option.some.inj (congrArg Prod.snd preparedSame.1)
                                                                      have heapSame := preparedSame.2
                                                                      have observedSame : actualObserved = observed := congrArg Prod.snd
                                                                        (Except.ok.inj (List.cons.inj (Option.some.inj same.2.2.2.2.1)).1)
                                                                      have attachedSame := Option.some.inj same.2.2.2.2.2.1
                                                                      have rightSame := Except.ok.inj
                                                                        (List.cons.inj (Option.some.inj same.2.2.2.2.2.2.1)).1
                                                                      have callbackSame : attached.core = callbackCore := congrArg Prod.snd rightSame
                                                                      have updatedSame : metadata = updated := congrArg Prod.snd (congrArg Prod.fst rightSame)
                                                                      subst actualChecked
                                                                      subst nativeResult
                                                                      subst actualAction
                                                                      subst nativeAfter
                                                                      subst actualObserved
                                                                      have attachedEq : attached = after := attachedSame
                                                                      subst attached
                                                                      have core := SourcePruningEnumerationNarrowAdapter.adapt_core nextHeap indexFuel
                                                                        uv oldHandle newHandle scs before after observed adaptedEq
                                                                      have actionSuccess : Success action checked () observed := by
                                                                        rw [Success, actionEq]
                                                                        exact List.mem_singleton_self _
                                                                      have changed : newHandle ≠ oldHandle := by
                                                                        intro equalHandle
                                                                        have equalCore := prepare_equal_handle_success_core holeKey fits admits metadata
                                                                          nativeFuel representativeFuel uv oldHandle scs oldValue result
                                                                          caller.checked.native.machine.heap nextHeap checked observed action preparedEq
                                                                          (by simpa only [equalHandle] using encodedEq) actionSuccess
                                                                        exact changedCore (core.trans equalCore)
                                                                      have callerHeap : reached.checked.native.machine.heap = nextHeap := by
                                                                        rw [← same.2.2.1]
                                                                        rfl
                                                                      exact ⟨oldHandle, newHandle, scs, oldValue, readAfter, rfl, checkEq,
                                                                        decodedEq, preparedEq, encodedEq, changed, actionEq, adaptedEq, core,
                                                                        callbackSame.symm.trans core, updatedSame.symm, callerHeap⟩

/-- An actual changed-core prefix result derives the stored normal value without separate stage suppliers. -/
theorem prefix_changed_stores_normal
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata updated : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller reached : Caller width) (before after : Cached) (queries receivedQueries : Queries)
    (checked observed callbackCore : Core) (result : Node)
    (nextHeap : InternedConstructorTemplates.State Symbol Constraint) (action : EnumerateM Symbol Constraint Unit)
    (ready : SourceEqualityRequiredCache.Ready caller.checked.native.machine.heap)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (total : UnionFind.Total before.core.representatives)
    (prefixObserved : runPrefix holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel uv caller before queries =
      .narrowed checked (.done (result, some action) nextHeap) reached receivedQueries
        (some [.ok ((), observed)]) (some after) (some [.ok ((false, updated), callbackCore)]) none)
    (changedCore : after.core ≠ checked) :
    reached.checked.native.machine.heap = nextHeap ∧
    ∃ (oldHandle newHandle : Nat) (scs : List Suspended) (oldValue : Node),
      encodeNode result = some newHandle ∧ newHandle ≠ oldHandle ∧
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap nextHeap ∧
      Available nextHeap result ∧ result.free = [] ∧ SourceEqualityRequiredCache.Ordinary result ∧
      EqualityOrdinaryReadback.Normal nextHeap result ∧ lookupNode nextHeap newHandle = some result ∧
      (∀ edge ∈ nodeEdges result, keeps fits admits (holeKey metadata.typing uv) edge = true) ∧
      (SourceEqualityRequiredCache.Ordinary oldValue → ∀ edge ∈ nodeEdges result, edge ∈ nodeEdges oldValue) ∧
      PendingRealized nextHeap after.core ∧
      ∃ (root : Nat) (middle : Core),
        Success (representative representativeFuel uv) checked root middle ∧ Frame checked middle ∧
        middle.values[root]? = some (.unenumerated (some oldHandle) scs) ∧
        Success (setValue root (.unenumerated (some newHandle) scs)) middle () after.core ∧
        after.core = {middle with values := middle.values.set root (.unenumerated (some newHandle) scs)} ∧
        after.core.values[root]? = some (.unenumerated (some newHandle) scs) := by
  obtain ⟨oldHandle, newHandle, scs, oldValue, readAfter, readEq, checkEq, decoded, prepared,
      newEncoded, changed, actionEq, _adapted, core, _callback, _updated, callerHeap⟩ :=
    prefix_changed_stages holeKey fits admits graph templates stop order metadata updated readFuel checkFuel
      nativeFuel representativeFuel indexFuel callbackFuel uv caller reached before after queries receivedQueries
      checked observed callbackCore result nextHeap action prefixObserved changedCore
  refine ⟨callerHeap, ?_⟩
  have readSuccess : Success (getValue readFuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter := by
    rw [Success, readEq]
    exact List.mem_singleton_self _
  have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv oldHandle scs) readAfter false checked := by
    rw [Success, checkEq]
    exact List.mem_singleton_self _
  have actionSuccess : Success action checked () observed := by
    rw [Success, actionEq]
    exact List.mem_singleton_self _
  refine ⟨oldHandle, newHandle, scs, oldValue, newEncoded, changed, decoded, ?_⟩
  have stored := SourcePruningEnumerationAction.prepare_changed_success_stores_normal
    holeKey fits admits metadata readFuel checkFuel nativeFuel representativeFuel uv oldHandle newHandle scs
    oldValue result caller.checked.native.machine.heap nextHeap before.core readAfter checked observed action
    ready realized total readSuccess checkSuccess decoded prepared newEncoded changed actionSuccess
  simpa only [core] using stored

end MicroCFTA.SourcePruningEnumerationSelectedStep
