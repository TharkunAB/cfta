import MicroCFTA.EnumerationFlatNativeIncoming
import MicroCFTA.EnumerationFlatNativeIndex
import MicroCFTA.EnumerationFlatNativeCachedFold
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

/-!
# Native incoming cache recovery with direct-parent count reads

Raw rows, the outer read core and recovered caches remain separate. Rejected
incoming writes retain the synthetic Empty slot and its gained occurrences.
-/
namespace MicroCFTA.EnumerationFlatNativeIncomingCache
open EnumerationFlatCached
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error
  (Unit × EnumerationFlatState.State Symbol Constraint))
variable {width : Nat}

/-- Recover a cache candidate from one original Incoming observation. -/
def adapt
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (target : Nat) (incomingScs : List EnumerationState.Suspended)
    (before : EnumerationFlatCached.Cached Symbol Constraint)
    (read : EnumerationFlatState.State Symbol Constraint) (raw : Raw) :
    Option (EnumerationFlatCached.Cached Symbol Constraint) :=
  match raw with
  | [] =>
      match read.values[target]? with
      | some (.unenumerated _oldNode oldScs) =>
        let value : EnumerationState.UVarValue Symbol :=
          .unenumerated (some 0) (incomingScs ++ oldScs)
        let core : EnumerationFlatState.State Symbol Constraint :=
          {read with
            values := read.values.set target value
            recursionAncestry := fun other => if other = target then
              (read.expansionAncestry ++ read.recursionAncestry target).eraseDups
              else read.recursionAncestry other}
        (EnumerationFlatNativeIndex.write heap target value incomingScs []
          (EnumerationFlatCached.frame read before)).map (EnumerationFlatCached.frame core)
      | _ => none
  | [.ok ((), returned)] =>
      (returned.values[target]?).bind fun slotValue =>
        (EnumerationFlatNativeIndex.write heap target slotValue incomingScs []
          (EnumerationFlatCached.frame read before)).map (EnumerationFlatCached.frame returned)
  | _ => none

/-- Retain one original observation and attach its optional cache candidate. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationFlatCached.Cached Symbol Constraint)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width) (Option Raw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint) ×
      Option (EnumerationFlatCached.Cached Symbol Constraint) :=
  let observed : (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width) (Option Raw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint :=
    EnumerationFlatNativeIncoming.run checkEmpty nativeFuel p h
      beforeCaller before.core target incoming incomingScs queries
  (observed, match observed with
    | (.ok (some raw), reachedCaller, _savedQueries, read) =>
        adapt reachedCaller.checked.native.machine.heap target incomingScs before read raw
    | _ => none)

private theorem write_frame_related
    (related : Related flat earlier)
    (cores : EnumerationFlatState.Related nextFlat nextEarlier)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (indexFuel target : Nat) (value : EnumerationState.UVarValue Symbol)
    (incomingScs : List EnumerationState.Suspended)
    (counted : ∀ waiting, SourcePruningEnumerationNativeIndex.count indexFuel
      earlier.core.representatives 1 incomingScs waiting =
        some (EnumerationFlatNativeIndex.count flat.core.representatives 1 incomingScs waiting)) :
    EnumerationFlatNativeIndex.WritesRelated
      ((EnumerationFlatNativeIndex.write heap target value incomingScs [] flat).map (frame nextFlat))
      ((SourcePruningEnumerationNativeIndex.write heap indexFuel target value incomingScs [] earlier).map
        (EnumerationExpandableIndex.frame nextEarlier)) := by
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp only [EnumerationFlatNativeIndex.write, SourcePruningEnumerationNativeIndex.write,
      classified, Option.map_none, Option.bind_none, EnumerationFlatNativeIndex.WritesRelated]
  | some flag =>
    simp only [EnumerationFlatNativeIndex.write, SourcePruningEnumerationNativeIndex.write,
      classified, Option.map_some, Option.bind_some, SourcePruningEnumerationNativeIndex.count,
      counted earlier.waiting]
    change Related _ _
    refine ⟨cores, ?_, ?_⟩
    · change (fun other => if other = target then flag else flat.expandable other) = _
      rw [related.expandable]
      rfl
    · change EnumerationFlatNativeIndex.count flat.core.representatives 1 incomingScs
        (EnumerationFlatNativeIndex.count flat.core.representatives (-1) [] flat.waiting) = _
      rw [related.waiting]
      rfl

/-- Completed old count reads preserve recovery from all related ordered raw rows. -/
theorem adapt_related (related : Related flat earlier)
    (reads : EnumerationFlatState.Related readFlat readEarlier)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (indexFuel target : Nat)
    (incomingScs : List EnumerationState.Suspended)
    (counted : ∀ waiting, SourcePruningEnumerationNativeIndex.count indexFuel
      readEarlier.representatives 1 incomingScs waiting =
        some (EnumerationFlatNativeIndex.count readFlat.representatives 1 incomingScs waiting))
    (rows : EnumerationResultRelation.Results EnumerationFlatState.Related flatRows oldRows) :
    EnumerationFlatNativeIndex.WritesRelated (adapt heap target incomingScs flat readFlat flatRows)
      (SourcePruningEnumerationIncomingCacheAdapter.adapt heap indexFuel target incomingScs
        earlier readEarlier oldRows) := by
  cases rows with
  | nil =>
    have same : readFlat.values[target]? = readEarlier.values[target]? := congrArg (fun values => values[target]?) reads.values
    cases stored : readFlat.values[target]? with
    | none =>
      have oldStored : readEarlier.values[target]? = none := same.symm.trans stored
      simp only [adapt, SourcePruningEnumerationIncomingCacheAdapter.adapt, stored, oldStored,
        EnumerationFlatNativeIndex.WritesRelated]
    | some value =>
      have oldStored : readEarlier.values[target]? = some value := same.symm.trans stored
      simp only [adapt, SourcePruningEnumerationIncomingCacheAdapter.adapt, stored, oldStored]
      cases value with
      | eliminated => trivial
      | enumerated fragment => trivial
      | unenumerated oldNode oldScs =>
        have next : EnumerationFlatState.Related
            {readFlat with
              values := readFlat.values.set target (.unenumerated (some 0) (incomingScs ++ oldScs))
              recursionAncestry := fun other => if other = target then
                (readFlat.expansionAncestry ++ readFlat.recursionAncestry target).eraseDups
                else readFlat.recursionAncestry other}
            {readEarlier with
              values := readEarlier.values.set target (.unenumerated (some 0) (incomingScs ++ oldScs))
              recursionAncestry := fun other => if other = target then
                (readEarlier.expansionAncestry ++ readEarlier.recursionAncestry target).eraseDups
                else readEarlier.recursionAncestry other} := by
          refine ⟨reads.valid, reads.representatives, reads.counter, ?_, reads.obligations, ?_,
            reads.expansionAncestry⟩
          · exact congrArg (fun values => values.set target
              (.unenumerated (some 0) (incomingScs ++ oldScs))) reads.values
          · rw [reads.expansionAncestry, reads.recursionAncestry]
        exact write_frame_related (frame_related related reads) next heap indexFuel target
          (.unenumerated (some 0) (incomingScs ++ oldScs)) incomingScs counted
  | cons head tail =>
    cases tail with
    | cons next remaining => cases head <;> trivial
    | nil =>
      cases head with
      | error error => trivial
      | @ok returnedFlat returnedEarlier value states =>
        cases value
        simp only [adapt, SourcePruningEnumerationIncomingCacheAdapter.adapt, states.values]
        cases stored : returnedEarlier.values[target]? with
        | none => trivial
        | some value =>
          simp only [Option.bind_some]
          exact write_frame_related (frame_related related reads) states heap indexFuel target value incomingScs counted

/-- Stable old representative and count bounds retain the complete actual incoming observation. -/
theorem run_stable
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : Related flat earlier) (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (target : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ∃ representativeFuel indexFuel, ∀ extraRepresentative extraIndex,
      EnumerationFlatNativeCachedFold.ResultRelated
        (run checkEmpty nativeFuel p h beforeCaller flat target incoming incomingScs queries)
        (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty
          (representativeFuel + extraRepresentative) nativeFuel p h (indexFuel + extraIndex)
          beforeCaller earlier target incoming incomingScs queries) := by
  obtain ⟨r, found, stable, _rootSame, _sizeSame, _retained⟩ :=
    FlatUnionFind.find_stable related.core.representatives target
  have rawRelated := EnumerationFlatNativeIncoming.run_related related.core
    (stable 0) checkEmpty nativeFuel p h beforeCaller incoming incomingScs queries
  simp only [Nat.add_zero] at rawRelated
  have oldStable : ∀ extra, SourcePruningEnumerationIncomingNode.run checkEmpty
      (r + extra) nativeFuel p h beforeCaller earlier.core target incoming incomingScs queries =
      SourcePruningEnumerationIncomingNode.run checkEmpty r nativeFuel p h
        beforeCaller earlier.core target incoming incomingScs queries := by
    intro extra
    simp only [SourcePruningEnumerationIncomingNode.run, stable extra,
      show UnionFind.findRoot r earlier.core.representatives target = some found from by
        simpa only [Nat.add_zero] using stable 0]
  generalize flatRun : EnumerationFlatNativeIncoming.run checkEmpty nativeFuel p h
    beforeCaller flat.core target incoming incomingScs queries = left at rawRelated ⊢
  generalize oldRun : SourcePruningEnumerationIncomingNode.run checkEmpty r nativeFuel p h
    beforeCaller earlier.core target incoming incomingScs queries = right at rawRelated oldStable ⊢
  obtain ⟨leftResult, reachedCaller, savedQueries, readFlat⟩ := left
  obtain ⟨rightResult, oldCaller, oldQueries, readEarlier⟩ := right
  obtain ⟨callerSame, queriesSame, reads, rows⟩ := rawRelated
  dsimp only at callerSame queriesSame
  subst oldCaller oldQueries
  obtain ⟨k, counts⟩ := EnumerationFlatNativeIndex.count_stable reads.representatives incomingScs
  refine ⟨r, k, ?_⟩
  intro extraRepresentative extraIndex
  simp only [run, SourcePruningEnumerationIncomingCacheAdapter.run, flatRun, oldStable extraRepresentative]
  refine ⟨⟨rfl, rfl, reads, rows⟩, ?_⟩
  cases leftResult with
  | error first =>
    cases rightResult with
    | error second => trivial
    | ok value => cases rows
  | ok leftValue =>
    cases rightResult with
    | error fault => cases leftValue <;> cases rows
    | ok rightValue =>
      cases leftValue with
      | none =>
        cases rightValue with
        | none => trivial
        | some raw => cases rows
      | some leftRows =>
        cases rightValue with
        | none => cases rows
        | some rightRows =>
          exact adapt_related related reads _ (k + extraIndex) target incomingScs
            (counts extraIndex 1) rows

end MicroCFTA.EnumerationFlatNativeIncomingCache
