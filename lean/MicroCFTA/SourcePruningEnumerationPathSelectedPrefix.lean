import MicroCFTA.SourcePruningEnumerationPathSelectedRaw

/-!
# Paths in all selected-prefix observations

Every retained core and every successful raw row keeps the supplied path
predicate. It does not assume a singleton result,
native completion, a model, a resource packet or a future continuation.
-/
namespace MicroCFTA.SourcePruningEnumerationPathSelectedPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationPathTransport SourcePruningEnumerationPathSelectedRaw
local notation "Symbol" => SourcePruningTemplates.Symbol

/-- Every actual selected prefix preserves paths in all retained cores and raw rows. -/
theorem runPrefix_paths {Typing Key : Type} {width : Nat}
    [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {P : EqualityTrie.Path → Prop}
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula) → Bool)
    (graph : Graph Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (templates : List (Template.Pattern Symbol))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : SourceCurrentAllocatedPartialState.State width)
    (before : EnumerationExpandableIndex.Cached Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (queries : SourceEndpointMemo.Memos) (paths : StatePaths P before.core) :
    SelectedPrefixPaths P (SourcePruningEnumerationSelectedStep.runPrefix
      holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel uv caller before queries) := by
  unfold SourcePruningEnumerationSelectedStep.runPrefix
  generalize readEq : ExceptT.run (getValue readFuel uv before.core) = read
  have readPaths : RawPaths P read := by
    intro value after member
    exact (getValue_paths readFuel uv before.core after value paths (by
      change Except.ok (value, after) ∈ ExceptT.run (getValue readFuel uv before.core)
      simpa only [readEq] using member)).1
  cases read with
  | nil => simpa [SelectedPrefixPaths] using readPaths
  | cons first rest =>
      cases first with
      | error error => simpa [SelectedPrefixPaths] using readPaths
      | ok pair =>
          rcases pair with ⟨value, readAfter⟩
          cases value with
          | eliminated => simpa [SelectedPrefixPaths] using readPaths
          | enumerated fragment => simpa [SelectedPrefixPaths] using readPaths
          | unenumerated handle scs =>
              cases handle with
              | none => simpa [SelectedPrefixPaths] using readPaths
              | some oldHandle =>
                  cases rest with
                  | cons second tail => simpa [SelectedPrefixPaths] using readPaths
                  | nil =>
                      have reading : Success (getValue readFuel uv) before.core
                          (.unenumerated (some oldHandle) scs) readAfter := by
                        change Except.ok _ ∈ ExceptT.run (getValue readFuel uv before.core)
                        rw [readEq]
                        exact List.mem_cons_self
                      have readFacts := getValue_paths readFuel uv before.core readAfter _ paths reading
                      dsimp only
                      generalize checkEq : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
                        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = check
                      have checkPaths : RawPaths P check := by
                        intro result after member
                        apply checkRepeated_paths caller.checked.native.machine.heap checkFuel uv oldHandle scs
                          readAfter after result readFacts.1
                        change Except.ok (result, after) ∈ ExceptT.run
                          (SourcePruningEnumerationRecursion.checkRepeated
                            caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter)
                        simpa only [checkEq] using member
                      cases check with
                      | nil => simpa [SelectedPrefixPaths] using And.intro readPaths checkPaths
                      | cons first rest =>
                          cases first with
                          | error error => simpa [SelectedPrefixPaths] using And.intro readPaths checkPaths
                          | ok pair =>
                              rcases pair with ⟨repeated, checked⟩
                              cases rest with
                              | cons second tail =>
                                  cases repeated <;>
                                    simpa [SelectedPrefixPaths] using And.intro readPaths checkPaths
                              | nil =>
                                  have checkedPaths : StatePaths P checked :=
                                    checkPaths repeated checked List.mem_cons_self
                                  cases repeated with
                                  | true =>
                                      dsimp only
                                      generalize candidateEq : SourcePruningEnumerationParkedRestart.adapt
                                        caller.checked.native.machine.heap indexFuel uv oldHandle scs before checked = candidate
                                      have candidates : ∀ after, candidate = some after → StatePaths P after.core := by
                                        intro after selected
                                        rw [SourcePruningEnumerationParkedRestart.adapt_core
                                          caller.checked.native.machine.heap indexFuel uv oldHandle scs before after checked
                                          (candidateEq.trans selected)]
                                        exact checkedPaths
                                      cases candidate with
                                      | none => simpa [SelectedPrefixPaths] using checkedPaths
                                      | some parked =>
                                          have parkedPaths := candidates parked rfl
                                          have restartPaths := restart_paths stop order metadata parked checked checkedPaths
                                          simpa [SelectedPrefixPaths] using
                                            And.intro checkedPaths (And.intro parkedPaths restartPaths)
                                  | false =>
                                      cases oldDecoded : lookupNode caller.checked.native.machine.heap oldHandle with
                                      | none => simpa [SelectedPrefixPaths] using And.intro readPaths checkPaths
                                      | some oldValue =>
                                          dsimp only
                                          generalize preparedEq : SourcePruningEnumerationAction.prepare
                                            holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue
                                            caller.checked.native.machine.heap = prepared
                                          have actions := prepare_actions_paths (EnumGuard := SourceSymbolicIndex.Constraint FullSyntax.Formula) holeKey fits admits metadata nativeFuel
                                            representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap readFacts.2
                                          rw [preparedEq] at actions
                                          cases prepared with
                                          | failed fault heap => simpa [SelectedPrefixPaths] using checkedPaths
                                          | done pair heap =>
                                              rcases pair with ⟨value, action⟩
                                              cases action with
                                              | none => simpa [SelectedPrefixPaths] using checkedPaths
                                              | some action =>
                                                  dsimp only
                                                  generalize actionEq : ExceptT.run (action checked) = raw
                                                  have actionPaths : RawPaths P raw := by
                                                    intro result after member
                                                    cases result
                                                    apply actions action rfl checked after checkedPaths
                                                    change Except.ok ((), after) ∈ ExceptT.run (action checked)
                                                    simpa only [actionEq] using member
                                                  cases raw with
                                                  | nil => simpa [SelectedPrefixPaths] using And.intro checkedPaths actionPaths
                                                  | cons first rest =>
                                                      cases first with
                                                      | error error =>
                                                          simpa [SelectedPrefixPaths] using And.intro checkedPaths actionPaths
                                                      | ok pair =>
                                                          rcases pair with ⟨⟨⟩, observed⟩
                                                          cases rest with
                                                          | cons second tail =>
                                                              simpa [SelectedPrefixPaths] using And.intro checkedPaths actionPaths
                                                          | nil =>
                                                              have observedPaths : StatePaths P observed :=
                                                                actionPaths () observed List.mem_cons_self
                                                              cases encoded : encodeNode value with
                                                              | none =>
                                                                  simpa [SelectedPrefixPaths] using
                                                                    And.intro checkedPaths actionPaths
                                                              | some newHandle =>
                                                                  dsimp only
                                                                  generalize candidateEq : SourcePruningEnumerationNarrowAdapter.adapt
                                                                    heap indexFuel uv oldHandle newHandle scs before observed = candidate
                                                                  have candidates : ∀ after, candidate = some after → StatePaths P after.core := by
                                                                    intro after selected
                                                                    rw [SourcePruningEnumerationNarrowAdapter.adapt_core
                                                                      heap indexFuel uv oldHandle newHandle scs before after observed
                                                                      (candidateEq.trans selected)]
                                                                    exact observedPaths
                                                                  cases candidate with
                                                                  | none =>
                                                                      simpa [SelectedPrefixPaths] using And.intro checkedPaths actionPaths
                                                                  | some attached =>
                                                                      have attachedPaths := candidates attached rfl
                                                                      dsimp only
                                                                      generalize rightEq : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                                                        graph templates callbackFuel metadata uv (.inr newHandle) attached.core) = right
                                                                      have rightPaths : RawPaths P right := by
                                                                        intro result after member
                                                                        apply SourcePruningEnumerationPathRecordingValues.recordTypes_paths
                                                                          graph templates callbackFuel metadata uv (.inr newHandle)
                                                                          attached.core after result attachedPaths
                                                                        change Except.ok (result, after) ∈ ExceptT.run
                                                                          (SourcePruningRecordTypes.recordTypes graph templates callbackFuel
                                                                            metadata uv (.inr newHandle) attached.core)
                                                                        simpa only [rightEq] using member
                                                                      cases right with
                                                                      | nil =>
                                                                          simpa [SelectedPrefixPaths] using
                                                                            And.intro checkedPaths (And.intro actionPaths
                                                                              (And.intro attachedPaths rightPaths))
                                                                      | cons first rest =>
                                                                          cases first with
                                                                          | error error =>
                                                                              simpa [SelectedPrefixPaths] using
                                                                                And.intro checkedPaths (And.intro actionPaths
                                                                                  (And.intro attachedPaths rightPaths))
                                                                          | ok pair =>
                                                                              rcases pair with ⟨⟨accepted, updated⟩, callbackCore⟩
                                                                              cases accepted with
                                                                              | true =>
                                                                                  simpa [SelectedPrefixPaths] using
                                                                                    And.intro checkedPaths (And.intro actionPaths
                                                                                      (And.intro attachedPaths rightPaths))
                                                                              | false =>
                                                                                  cases rest with
                                                                                  | cons second tail =>
                                                                                      simpa [SelectedPrefixPaths] using
                                                                                        And.intro checkedPaths (And.intro actionPaths
                                                                                          (And.intro attachedPaths rightPaths))
                                                                                  | nil =>
                                                                                      have callbackPaths :=
                                                                                        rightPaths (false, updated) callbackCore List.mem_cons_self
                                                                                      simpa [SelectedPrefixPaths,
                                                                                        EnumerationExpandableIndex.frame] using
                                                                                        And.intro checkedPaths (And.intro actionPaths
                                                                                          (And.intro callbackPaths rightPaths))

end MicroCFTA.SourcePruningEnumerationPathSelectedPrefix
