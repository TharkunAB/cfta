import MicroCFTA.SourcePruningEnumerationRawGuardNarrowing
import MicroCFTA.SourcePruningEnumerationSelectedStep

/-!
# Actual selected-prefix caller annotation heaps

The raw stored-value read derives availability and closure from PendingRealized.
No returned native query or future recursive worker is assumed.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}

/-- Every reached caller in the actual selected prefix retains the original annotation heap. -/
theorem runPrefix_heap (P : Constraint → Prop) [DecidableEq (EdgeKey Symbol Constraint)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good caller.checked)
    (realized : SourcePruningEnumerationObservation.PendingRealized
      caller.checked.native.machine.heap before.core)
    (initialHeap : Heap P caller.checked.native.machine.heap) :
    match runPrefix holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel uv caller before queries with
    | .narrowed _ _ reached _ _ _ _ _ => Heap P reached.checked.native.machine.heap
    | _ => True := by
  unfold runPrefix
  dsimp only
  generalize readEq : ExceptT.run (getValue readFuel uv before.core) = read
  cases read with
  | nil => trivial
  | cons first rest =>
      cases rest with
      | cons _ _ =>
          cases first with
          | error _ => trivial
          | ok pair =>
              obtain ⟨value, _readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => trivial
              | unenumerated handle _ => cases handle <;> trivial
      | nil =>
          cases first with
          | error _ => trivial
          | ok pair =>
              obtain ⟨value, readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => trivial
              | unenumerated handle scs =>
                  cases handle with
                  | none => trivial
                  | some oldHandle =>
                      have observedRead : EnumerationCorrectness.Success (getValue readFuel uv)
                          before.core (.unenumerated (some oldHandle) scs) readAfter := by
                        change Except.ok (.unenumerated (some oldHandle) scs, readAfter) ∈
                          ExceptT.run (getValue readFuel uv before.core)
                        rw [readEq]
                        exact List.mem_singleton_self _
                      obtain ⟨found, _lookup, stored, _readState⟩ :=
                        (EnumerationCorrectness.getValue_success readFuel uv before.core readAfter
                          (.unenumerated (some oldHandle) scs)).mp observedRead
                      obtain ⟨resident, decoded, available, closed⟩ :=
                        realized found.representative oldHandle scs stored
                      dsimp only
                      generalize ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
                        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = check
                      cases check with
                      | nil => trivial
                      | cons first rest =>
                          cases rest with
                          | cons _ _ =>
                              cases first with
                              | error _ => trivial
                              | ok pair =>
                                  obtain ⟨repeated, _checked⟩ := pair
                                  cases repeated <;> trivial
                          | nil =>
                              cases first with
                              | error _ => trivial
                              | ok pair =>
                                  obtain ⟨repeated, checked⟩ := pair
                                  cases repeated with
                                  | true => trivial
                                  | false =>
                                      cases actualLookup : lookupNode caller.checked.native.machine.heap oldHandle with
                                      | none => trivial
                                      | some oldValue =>
                                          have same : resident = oldValue :=
                                            Option.some.inj (decoded.symm.trans actualLookup)
                                          subst resident
                                          dsimp only
                                          generalize preparedEq : SourcePruningEnumerationAction.prepare holeKey fits admits metadata
                                            nativeFuel representativeFuel uv oldHandle scs oldValue
                                            caller.checked.native.machine.heap = prepared
                                          have reachedHeap : Heap P
                                              (SourceCurrentAllocatedPartialState.advance caller
                                                (advancePhysical caller.checked
                                                  ⟨prepared.state, caller.checked.operations⟩)
                                                caller.fourth caller.merge).checked.native.machine.heap := by
                                            change Heap P prepared.state
                                            rw [← preparedEq]
                                            exact SourcePruningEnumerationAction.prepare_heap P holeKey fits admits
                                              metadata nativeFuel representativeFuel uv oldHandle scs oldValue
                                              caller.checked.native.machine.heap good.heap.semantic good.heap.covered
                                              initialHeap available closed
                                          cases prepared with
                                          | failed _ _ => exact reachedHeap
                                          | done pair heap =>
                                              obtain ⟨value, action⟩ := pair
                                              cases action with
                                              | none => exact reachedHeap
                                              | some action =>
                                                  dsimp only
                                                  generalize ExceptT.run (action checked) = raw
                                                  cases raw with
                                                  | nil => exact reachedHeap
                                                  | cons first rest =>
                                                      cases rest with
                                                      | cons _ _ =>
                                                          cases first with
                                                          | error _ => exact reachedHeap
                                                          | ok pair =>
                                                              obtain ⟨token, _observed⟩ := pair
                                                              cases token
                                                              exact reachedHeap
                                                      | nil =>
                                                          cases first with
                                                          | error _ => exact reachedHeap
                                                          | ok pair =>
                                                              obtain ⟨token, observed⟩ := pair
                                                              cases token
                                                              dsimp only
                                                              cases encodeNode value with
                                                              | none => exact reachedHeap
                                                              | some newHandle =>
                                                                  dsimp only
                                                                  cases SourcePruningEnumerationNarrowAdapter.adapt heap
                                                                    indexFuel uv oldHandle newHandle scs before observed with
                                                                  | none => exact reachedHeap
                                                                  | some attached =>
                                                                      rw [SourcePruningRecordTypes.recordTypes_inr]
                                                                      exact reachedHeap

end MicroCFTA.SourcePruningEnumerationSelectedStep
