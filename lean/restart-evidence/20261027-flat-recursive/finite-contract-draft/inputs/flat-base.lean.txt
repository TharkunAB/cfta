import MicroCFTA.SourceFlatPruningRecursive

/-!
# Actual base observations of flat recursion

Related receipts retain their actual native endpoints.
Zero recursive depth compares every decision without executing a selected step.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "OldCached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Receipt" => SourceFlatPruningSelectedEdge.Result
local notation "OldReceipt" => SourcePruningEnumerationSelectedEdge.Result
variable {Typing Key : Type} {width : Nat}
local notation "Stop" => SourceFlatPruningNativeContinuations.Stop (Failure width Typing) width
local notation "OldStop" => SourcePruningEnumerationNativeContinuations.Stop
  (SourcePruningEnumerationRecursive.Failure width Typing) width
local notation "Fold" => SourceFlatPruningNativeContinuations.Result
  (Output width Typing) (Failure width Typing) width
local notation "OldFold" => SourcePruningEnumerationNativeContinuations.Result
  (SourcePruningEnumerationRecursive.Output width Typing)
  (SourcePruningEnumerationRecursive.Failure width Typing) width

/-- Related edge receipts supply the same optional native endpoint. -/
theorem advance_related (flat : Receipt width) (earlier : OldReceipt width)
    (related : SourceFlatPruningSelectedEdge.ResultRelated flat earlier) :
    SourceFlatPruningNativeBranches.advance flat = SourcePruningEnumerationNativeBranches.advance earlier := by
  cases flat <;> cases earlier <;>
    simp only [SourceFlatPruningSelectedEdge.ResultRelated] at related <;> try contradiction
  case unhandled.unhandled => rfl
  case rejected.rejected caller queries after oldCaller oldQueries oldAfter =>
    obtain ⟨rfl, rfl, _caches⟩ := related
    rfl
  case complete.complete fragment caller queries after oldFragment oldCaller oldQueries oldAfter =>
    obtain ⟨rfl, rfl, rfl, _caches⟩ := related
    rfl
  case stopped.stopped fragments observation candidate oldFragments oldObservation oldCandidate =>
    obtain ⟨outcome, caller, queries, outer, waiting⟩ := observation
    obtain ⟨oldOutcome, oldCaller, oldQueries, oldOuter, oldWaiting⟩ := oldObservation
    obtain ⟨_fragmentsSame,
      ⟨callerSame, queriesSame, _outerRelated, _waitingSame, rows⟩, caches⟩ := related
    dsimp only at callerSame queriesSame rows caches
    subst oldCaller oldQueries
    cases candidate with
    | none =>
      cases oldCandidate with
      | some oldAfter => cases caches
      | none =>
        have left : SourceFlatPruningNativeBranches.advance
            (.stopped fragments (outcome, caller, queries, outer, waiting) none) = none := by
          cases outcome with
          | error _ => rfl
          | ok value =>
            cases value with
            | none => rfl
            | some raw => cases raw <;> rfl
        have right : SourcePruningEnumerationNativeBranches.advance
            (.stopped oldFragments (oldOutcome, caller, queries, oldOuter, oldWaiting) none) = none := by
          cases oldOutcome with
          | error _ => rfl
          | ok value =>
            cases value with
            | none => rfl
            | some raw => cases raw <;> rfl
        exact left.trans right.symm
    | some after =>
      cases oldCandidate with
      | none => cases caches
      | some oldAfter =>
        cases outcome with
        | error fault =>
          cases oldOutcome with
          | error _ => rfl
          | ok oldValue =>
            cases fault with
            | inl _ => cases oldValue <;> cases rows
            | inr remaining => cases remaining <;> cases oldValue <;> cases rows
        | ok value =>
          cases oldOutcome with
          | error fault =>
            cases fault with
            | inl _ => cases value <;> cases rows
            | inr remaining => cases remaining <;> cases value <;> cases rows
          | ok oldValue =>
            cases value with
            | none =>
              cases oldValue with
              | none => rfl
              | some _ => cases rows
            | some raw =>
              cases oldValue with
              | none => cases rows
              | some oldRaw =>
                cases rows with
                | nil => rfl
                | cons _ _ => rfl

/-- Related stopping contexts retain the same actual optional native endpoint. -/
theorem endpoint_related (flat : Stop) (earlier : OldStop)
    (related : SourceFlatPruningNativeContinuations.StopRelated FailureRelated flat earlier) :
    endpoint flat = SourcePruningEnumerationRecursive.endpoint earlier := by
  cases flat with
  | edge current =>
    cases earlier with
    | continuation _ _ _ => cases related
    | edge oldCurrent =>
      cases current with
      | none =>
        cases oldCurrent with
        | none => rfl
        | some _ => cases related
      | some current =>
        cases oldCurrent with
        | none => cases related
        | some oldCurrent => exact advance_related current oldCurrent related
  | continuation current reason reached =>
    cases earlier with
    | edge _ => cases related
    | continuation oldCurrent oldReason oldReached => exact related.2.2

/-- Related processed receipts and stops retain the full recursive alternative failure. -/
theorem alternatives_related (uv : Nat) {processed : List (Receipt width)}
    {oldProcessed : List (OldReceipt width)} (flat : Stop) (earlier : OldStop)
    (processedRelated : SourceFlatPruningNativeBranches.ReceiptsRelated processed oldProcessed)
    (related : SourceFlatPruningNativeContinuations.StopRelated FailureRelated flat earlier) :
    FailureRelated (.alternatives uv processed flat)
      (.alternatives uv oldProcessed earlier) := by
  cases flat with
  | edge current =>
    cases earlier with
    | continuation _ _ _ => cases related
    | edge oldCurrent =>
      cases current with
      | none =>
        cases oldCurrent with
        | none => exact .alternatives_none uv processedRelated
        | some _ => cases related
      | some current =>
        cases oldCurrent with
        | none => cases related
        | some oldCurrent => exact .alternatives_edge uv processedRelated related
  | continuation current reason reached =>
    cases earlier with
    | edge _ => cases related
    | continuation oldCurrent oldReason oldReached =>
      obtain ⟨currentRelated, reasonRelated, reachedSame⟩ := related
      subst oldReached
      exact .alternatives_continuation uv reached processedRelated currentRelated reasonRelated

/-- Finishing related folds retains ordered outputs and the complete actual stopping context. -/
theorem finish_related (uv : Nat) (flat : Fold) (earlier : OldFold)
    (related : SourceFlatPruningNativeContinuations.ResultRelated
      OutputRelated FailureRelated flat earlier) :
    ResultRelated (finish uv flat) (SourcePruningEnumerationRecursive.finish uv earlier) := by
  cases flat with
  | complete processed outputs caller queries =>
    cases earlier with
    | stopped _ _ _ => cases related
    | complete oldProcessed oldOutputs oldCaller oldQueries =>
      obtain ⟨_processedRelated, outputsRelated, callerSame, queriesSame⟩ := related
      exact ⟨outputsRelated, callerSame, queriesSame⟩
  | stopped processed outputs current =>
    cases earlier with
    | complete _ _ _ _ => cases related
    | stopped oldProcessed oldOutputs oldCurrent =>
      obtain ⟨processedRelated, outputsRelated, currentRelated⟩ := related
      exact ⟨outputsRelated, alternatives_related uv current oldCurrent processedRelated currentRelated,
        endpoint_related current oldCurrent currentRelated⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat)
variable (metadata : Metadata Typing) (caller : Caller width) (queries : Queries)
variable (flat : Cached) (earlier : OldCached) (related : EnumerationFlatCached.Related flat earlier)

/-- Zero recursive depth relates every decision without running a selected step. -/
theorem resume_zero_related (next : Option Next) :
    ResultRelated
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
        metadata caller queries flat next)
      (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
        stop order workFuel 0 metadata caller queries earlier next) := by
  cases next with
  | none => exact ⟨.cons ⟨rfl, related, rfl, rfl⟩ .nil, rfl, rfl⟩
  | some next =>
    cases next with
    | done => exact ⟨.cons ⟨rfl, related, rfl, rfl⟩ .nil, rfl, rfl⟩
    | stuck => exact ⟨.nil, rfl, rfl⟩
    | expand uv => exact ⟨.nil, .exhausted uv metadata related, rfl⟩

/-- The actual initial restart decision derives zero-depth correspondence from related caches. -/
theorem run_zero_related :
    ResultRelated
      (run holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
        metadata caller queries flat)
      (SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf
        stop order workFuel 0 metadata caller queries earlier) := by
  unfold run SourcePruningEnumerationRecursive.run
  rw [SourceFlatPruningRestart.decision_related related stop order metadata]
  exact resume_zero_related holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
    metadata caller queries flat earlier related _

/-- A nonexpanding decision retains correspondence at every recursive depth. -/
theorem resume_nonexpanding_related (recursiveFuel : Nat) (next : Option Next)
    (nonexpanding : ∀ uv, next ≠ some (.expand uv)) :
    ResultRelated
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        metadata caller queries flat next)
      (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
        stop order workFuel recursiveFuel metadata caller queries earlier next) := by
  cases next with
  | none =>
    cases recursiveFuel <;> exact ⟨.cons ⟨rfl, related, rfl, rfl⟩ .nil, rfl, rfl⟩
  | some next =>
    cases next with
    | done =>
      cases recursiveFuel <;> exact ⟨.cons ⟨rfl, related, rfl, rfl⟩ .nil, rfl, rfl⟩
    | stuck => cases recursiveFuel <;> exact ⟨.nil, rfl, rfl⟩
    | expand uv => exact (nonexpanding uv rfl).elim

end MicroCFTA.SourceFlatPruningRecursive
