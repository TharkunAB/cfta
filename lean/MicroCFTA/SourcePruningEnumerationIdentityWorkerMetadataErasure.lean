import MicroCFTA.SourcePruningEnumerationIdentityChildMetadataErasure

set_option autoImplicit false

/-!
# Exact metadata erasure for the existing identity eager worker

The statements retain every complete and stopped result.
They retain list order, repeated outputs, native endpoints, and failure observations.
The worker uses identity narrowing and no templates.
It has no stop callback or selection preference.
-/
namespace MicroCFTA.SourcePruningEnumerationIdentityResultMetadataErasure
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish continueWith)
open SourcePruningEnumerationIdentityPrefixMetadataErasure
  (erasePrefix runPrefix_identity_metadata_erasure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Prefix" => SourcePruningEnumerationSelectedStep.Result
local notation "Hook" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "HookFor" => fun (T : Type) => Hook (Output width T) (Failure width T) width

/-- The actual recursive worker retains the same erased result at every decision and fuel. -/
theorem resume_identity_metadata_erasure {Typing : Type}
    (graph : Graph Symbol Constraint) (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (unitMetadata : Metadata Unit)
    (caller : Caller width) (queries : Queries) (before : Cached) (decision : Option Next) :
    eraseResult (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
      none (fun _ _ => none) workFuel recursiveFuel metadata caller queries before decision) =
    eraseResult (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
      none (fun _ _ => none) workFuel recursiveFuel unitMetadata caller queries before decision) := by
  induction recursiveFuel generalizing metadata unitMetadata caller queries before decision with
  | zero =>
      cases decision with
      | none => rfl
      | some next => cases next <;> rfl
  | succ fuel ih =>
      cases decision with
      | none => rfl
      | some next =>
          cases next with
          | done => rfl
          | stuck => rfl
          | expand uv =>
              have selectedSame (left : Prefix width Typing) (right : Prefix width Unit)
                  (reached : Caller width) (saved : Queries)
                  (same : erasePrefix left = erasePrefix right) :
                  eraseResult (.stopped [] (.selected uv left) (some (reached, saved))) =
                    eraseResult (.stopped [] (.selected uv right) (some (reached, saved))) := by
                simp only [eraseResult, eraseFailure, same, List.map_nil]
              have preparedSame (updated : Metadata Typing) (unitUpdated : Metadata Unit)
                  (reached : Caller width) (saved : Queries) (after : Cached) :
                  let left := SourcePruningEnumerationSharedPreparedChildPolicy.runEager
                    (continueWith
                      (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                        (SourcePruningEnumerationSharedEagerChildren.eagerChild
                          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                        (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
                        none (fun _ _ => none) workFuel fuel)
                      graph [] none (fun _ _ => none) workFuel updated uv)
                    checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                    edgesOf reached after saved
                  let right := SourcePruningEnumerationSharedPreparedChildPolicy.runEager
                    (continueWith
                      (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                        (SourcePruningEnumerationSharedEagerChildren.eagerChild
                          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                        (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
                        none (fun _ _ => none) workFuel fuel)
                      graph [] none (fun _ _ => none) workFuel unitUpdated uv)
                    checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                    edgesOf reached after saved
                  eraseResult (match left.2 with
                    | none => .stopped [] (.preparation uv left.1)
                        (some (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint
                          reached saved left.1))
                    | some folded => finish uv folded) =
                  eraseResult (match right.2 with
                    | none => .stopped [] (.preparation uv right.1)
                        (some (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint
                          reached saved right.1))
                    | some folded => finish uv folded) := by
                let leftHook : Fragment → Caller width → Queries → Cached → HookFor Typing :=
                  continueWith
                    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                      (SourcePruningEnumerationSharedEagerChildren.eagerChild
                        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                      (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
                      none (fun _ _ => none) workFuel fuel)
                    graph [] none (fun _ _ => none) workFuel updated uv
                let rightHook : Fragment → Caller width → Queries → Cached → HookFor Unit :=
                  continueWith
                    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                      (SourcePruningEnumerationSharedEagerChildren.eagerChild
                        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                      (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
                      none (fun _ _ => none) workFuel fuel)
                    graph [] none (fun _ _ => none) workFuel unitUpdated uv
                have hooksSame :
                    (fun fragment current memos cache => eraseResult (leftHook fragment current memos cache)) =
                      (fun fragment current memos cache => eraseResult (rightHook fragment current memos cache)) := by
                  funext fragment current memos cache
                  dsimp only [leftHook, rightHook]
                  rw [continue_empty_exact, continue_empty_exact]
                  exact ih _ _ current memos _ _
                let leftPrepared := SourcePruningEnumerationSharedPreparedChildPolicy.runEager leftHook
                  checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                  edgesOf reached after saved
                let rightPrepared := SourcePruningEnumerationSharedPreparedChildPolicy.runEager rightHook
                  checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                  edgesOf reached after saved
                have samePrepared :
                    (leftPrepared.1, leftPrepared.2.map eraseFold) =
                      (rightPrepared.1, rightPrepared.2.map eraseFold) := by
                  dsimp only [leftPrepared, rightPrepared]
                  rw [prepared_erasure, prepared_erasure, hooksSame]
                change eraseResult (match leftPrepared.2 with
                    | none => .stopped [] (.preparation uv leftPrepared.1)
                        (some (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint
                          reached saved leftPrepared.1))
                    | some folded => finish uv folded) =
                  eraseResult (match rightPrepared.2 with
                    | none => .stopped [] (.preparation uv rightPrepared.1)
                        (some (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint
                          reached saved rightPrepared.1))
                    | some folded => finish uv folded)
                generalize leftPrepared = actualLeft at samePrepared ⊢
                generalize rightPrepared = actualRight at samePrepared ⊢
                rcases actualLeft with ⟨rawLeft, foldedLeft⟩
                rcases actualRight with ⟨rawRight, foldedRight⟩
                dsimp only at samePrepared ⊢
                injection samePrepared with rawSame foldedSame
                cases rawSame
                cases foldedLeft with
                | none =>
                    cases foldedRight with
                    | none => rfl
                    | some folded => cases foldedSame
                | some leftFold =>
                    cases foldedRight with
                    | none => cases foldedSame
                    | some rightFold =>
                        dsimp only
                        have sameFolds : eraseFold leftFold = eraseFold rightFold :=
                          Option.some.inj foldedSame
                        rw [finish_erasure, finish_erasure, sameFolds]
              have samePrefix :
                  erasePrefix (SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                    (fun _ _ _ value heap => .done value heap) graph [] none (fun _ _ => none) metadata
                    workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries) =
                  erasePrefix (SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                    (fun _ _ _ value heap => .done value heap) graph [] none (fun _ _ => none) unitMetadata
                    workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries) :=
                runPrefix_identity_metadata_erasure graph [] (fun _ => none) metadata unitMetadata
                  workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries
              conv =>
                lhs
                arg 1
                rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow]
              conv =>
                rhs
                arg 1
                rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow]
              generalize SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                (fun _ _ _ value heap => .done value heap) graph [] none (fun _ _ => none) metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
                observedLeft at samePrefix ⊢
              generalize SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                (fun _ _ _ value heap => .done value heap) graph [] none (fun _ _ => none) unitMetadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
                observedRight at samePrefix ⊢
              dsimp only
              cases observedLeft with
              | stopped read checked =>
                  cases observedRight with
                  | stopped otherRead otherChecked => exact selectedSame _ _ caller queries samePrefix
                  | parked _ _ _ | narrowed _ _ _ _ _ _ _ _ =>
                      simp only [erasePrefix] at samePrefix
                      cases samePrefix
              | parked checked candidate rawLeft =>
                  cases observedRight with
                  | stopped _ _ | narrowed _ _ _ _ _ _ _ _ =>
                      simp only [erasePrefix] at samePrefix
                      cases samePrefix
                  | parked otherChecked otherCandidate rawRight =>
                      have keptSame := samePrefix
                      simp only [erasePrefix] at samePrefix
                      injection samePrefix with checkedSame candidateSame rawSame
                      cases checkedSame
                      cases candidateSame
                      cases candidate with
                      | none => exact selectedSame _ _ caller queries keptSame
                      | some parked =>
                          cases rawLeft with
                          | none =>
                              cases rawRight with
                              | none => exact selectedSame _ _ caller queries keptSame
                              | some rows => cases rawSame
                          | some leftRows =>
                              cases rawRight with
                              | none => cases rawSame
                              | some rightRows =>
                                  have rowsSame := Option.some.inj rawSame
                                  cases leftRows with
                                  | nil =>
                                      cases rightRows with
                                      | nil => rfl
                                      | cons _ _ => cases rowsSame
                                  | cons leftHead leftTail =>
                                      cases rightRows with
                                      | nil => cases rowsSame
                                      | cons rightHead rightTail =>
                                          injection rowsSame with headsSame tailsSame
                                          cases leftTail with
                                          | nil =>
                                              cases rightTail with
                                              | cons _ _ => cases tailsSame
                                              | nil =>
                                                  cases leftHead with
                                                  | error fault =>
                                                      cases rightHead with
                                                      | error otherFault => exact selectedSame _ _ caller queries keptSame
                                                      | ok pair => cases headsSame
                                                  | ok leftPair =>
                                                      cases rightHead with
                                                      | error fault => cases headsSame
                                                      | ok rightPair =>
                                                          rcases leftPair with ⟨⟨updated, next⟩, core⟩
                                                          rcases rightPair with ⟨⟨unitUpdated, unitNext⟩, unitCore⟩
                                                          dsimp only at headsSame
                                                          have dataSame := Except.ok.inj headsSame
                                                          have nextSame : next = unitNext :=
                                                            congrArg (fun row => row.1.2) dataSame
                                                          have coreSame : core = unitCore := congrArg Prod.snd dataSame
                                                          cases nextSame
                                                          cases coreSame
                                                          exact ih updated unitUpdated caller queries
                                                            (EnumerationExpandableIndex.frame core parked) next
                                          | cons second tail =>
                                              cases rightTail with
                                              | nil => cases tailsSame
                                              | cons otherSecond otherTail =>
                                                  cases leftHead <;> cases rightHead <;>
                                                    exact selectedSame _ _ caller queries keptSame
              | narrowed checked prepared reached saved action candidate rightLeft ordinary =>
                  cases observedRight with
                  | stopped _ _ | parked _ _ _ =>
                      simp only [erasePrefix] at samePrefix
                      cases samePrefix
                  | narrowed otherChecked otherPrepared otherReached otherSaved otherAction otherCandidate rightRight otherOrdinary =>
                      have keptSame := samePrefix
                      simp only [erasePrefix] at samePrefix
                      injection samePrefix with checkedSame preparedSameValue reachedSame savedSame actionSame candidateSame rightSame ordinarySame
                      cases checkedSame
                      cases preparedSameValue
                      cases reachedSame
                      cases savedSame
                      cases actionSame
                      cases candidateSame
                      cases ordinarySame
                      cases action
                      case' some rows => cases rows
                      case some.nil => rfl
                      all_goals
                        cases rightLeft with
                        | none =>
                            cases rightRight with
                            | none => exact selectedSame _ _ reached saved keptSame
                            | some rows => cases rightSame
                        | some leftRows =>
                            cases rightRight with
                            | none => cases rightSame
                            | some rightRows =>
                                have rowsSame := Option.some.inj rightSame
                                cases leftRows with
                                | nil =>
                                    cases rightRows with
                                    | nil => exact selectedSame _ _ reached saved keptSame
                                    | cons _ _ => cases rowsSame
                                | cons leftHead leftTail =>
                                    cases rightRows with
                                    | nil => cases rowsSame
                                    | cons rightHead rightTail =>
                                        injection rowsSame with headsSame tailsSame
                                        cases leftTail with
                                        | nil =>
                                            cases rightTail with
                                            | cons _ _ => cases tailsSame
                                            | nil =>
                                                cases leftHead with
                                                | error fault =>
                                                    cases rightHead with
                                                    | error otherFault => exact selectedSame _ _ reached saved keptSame
                                                    | ok pair => cases headsSame
                                                | ok leftPair =>
                                                    cases rightHead with
                                                    | error fault => cases headsSame
                                                    | ok rightPair =>
                                                        rcases leftPair with ⟨⟨flag, updated⟩, core⟩
                                                        rcases rightPair with ⟨⟨unitFlag, unitUpdated⟩, unitCore⟩
                                                        dsimp only at headsSame
                                                        have dataSame := Except.ok.inj headsSame
                                                        have flagSame : flag = unitFlag :=
                                                          congrArg (fun row => row.1.1) dataSame
                                                        have coreSame : core = unitCore := congrArg Prod.snd dataSame
                                                        cases flagSame
                                                        cases coreSame
                                                        cases flag with
                                                        | true => rfl
                                                        | false =>
                                                            cases candidate with
                                                            | none => exact selectedSame _ _ reached saved keptSame
                                                            | some after =>
                                                                cases ordinary with
                                                                | some recorded => exact selectedSame _ _ reached saved keptSame
                                                                | none =>
                                                                    dsimp only
                                                                    have observed := preparedSame updated unitUpdated reached saved after
                                                                    simp only [SourcePruningEnumerationSharedPreparedChildPolicy.runEager] at observed
                                                                    generalize
                                                                      (SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
                                                                        (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                                          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                                        (continueWith
                                                                          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                                                                            (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                                              checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                                            (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
                                                                            none (fun _ _ => none) workFuel fuel)
                                                                          graph [] none (fun _ _ => none) workFuel updated uv)
                                                                        checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                                                                        edgesOf reached after saved).2 = leftFolded at observed ⊢
                                                                    generalize
                                                                      (SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
                                                                        (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                                          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                                        (continueWith
                                                                          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                                                                            (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                                              checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                                            (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
                                                                            none (fun _ _ => none) workFuel fuel)
                                                                          graph [] none (fun _ _ => none) workFuel unitUpdated uv)
                                                                        checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                                                                        edgesOf reached after saved).2 = rightFolded at observed ⊢
                                                                    cases leftFolded <;> cases rightFolded <;>
                                                                      (dsimp! only at observed ⊢ <;> exact observed)
                                        | cons second tail =>
                                            cases rightTail with
                                            | nil => cases tailsSame
                                            | cons otherSecond otherTail =>
                                                cases leftHead
                                                case' ok pair =>
                                                  rcases pair with ⟨⟨leftFlag, leftMetadata⟩, leftCore⟩
                                                  cases leftFlag
                                                all_goals
                                                  cases rightHead
                                                  case' ok pair =>
                                                    rcases pair with ⟨⟨rightFlag, rightMetadata⟩, rightCore⟩
                                                    cases rightFlag
                                                  all_goals
                                                    dsimp only
                                                    exact selectedSame _ _ reached saved keptSame

/-- The actual eager entry retains the same erased observation for arbitrary metadata. -/
theorem runEager_identity_metadata_erasure {Typing : Type}
    (graph : Graph Symbol Constraint) (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (unitMetadata : Metadata Unit)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    eraseResult (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
      none (fun _ _ => none) workFuel recursiveFuel metadata caller queries before) =
    eraseResult (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (fun _ _ _ value heap => .done value heap) graph [] checkEmpty edgesOf
      none (fun _ _ => none) workFuel recursiveFuel unitMetadata caller queries before) := by
  unfold SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runWithNarrow
  simp only [SourcePruningEnumerationRestart.decision]
  exact resume_identity_metadata_erasure graph checkEmpty edgesOf workFuel recursiveFuel
    metadata unitMetadata caller queries before _

end MicroCFTA.SourcePruningEnumerationIdentityResultMetadataErasure
