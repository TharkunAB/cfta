import MicroCFTA.SourcePruningEnumerationPrefixPacket
import MicroCFTA.SourcePruningEnumerationPendingLanguage
import MicroCFTA.SourcePruningNativeMeaning

/-!
# Assignment meaning of the actual selected prefix

The nonrepeated branch can restrict its native domain. The repeated branch
removes its stored suspended bucket. Its backward law retains each removed
restriction. An ancestry marker does not discharge these restrictions.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Retained caches have backward assignment laws at their actual native heaps.
The parked law states the exact restrictions removed from the original slot. -/
def PrefixMeaning
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (fuel uv : Nat) (caller : Caller width) (before : Cached)
    (observed : Result width Typing) : Prop :=
  match observed with
  | .stopped _ _ | .parked _ none _ => False
  | .parked _ (some after) _ =>
      ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
        before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
        ExceptT.run (getValue fuel uv before.core) =
          [.ok (.unenumerated (some oldHandle) scs, readAfter)] ∧
        ∀ ambient residualMeaning assignment,
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment before.core ↔
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment after.core ∧
          ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc
  | .narrowed _ _ reached _ _ (some after) _ _ =>
      ∀ ambient residualMeaning assignment,
        Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap)
          residualMeaning assignment after.core →
        Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          residualMeaning assignment before.core
  | .narrowed _ _ _ _ _ none _ _ => True

section Runtime
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem narrow_available
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value result : Node)
    (before after : State Symbol Constraint)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before =
      .done result after) : Available after result ∧ result.free = [] := by
  have skipped (same : result = value ∧ after = before) : Available after result ∧ result.free = [] := by
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨available, closed⟩
  by_cases typed : uv ∈ metadata.types
  · have pureDone := SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value before typed
    have same := MergedSourceComparison.Result.done.inj (pureDone.symm.trans actual)
    exact skipped ⟨same.1.symm, same.2.symm⟩
  · cases value with
    | mu =>
        have same := MergedSourceComparison.Result.done.inj actual
        exact skipped ⟨same.1.symm, same.2.symm⟩
    | empty | reference | node | union =>
        have narrowed := actual
        simp [SourcePruningOuterNarrow.narrow, typed] at narrowed
        obtain ⟨rows, middle, exposed, built, _meaning⟩ := SourcePruningNativeView.narrowAt_edges
          (fun _ _ => true) (fun _ _ => False) fits admits (holeKey metadata.typing uv) fuel _ before
          result after ready available closed narrowed
        have verified := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel _ before
          ready.semantic ready.covered available closed
        have semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap middle := by
          simpa only [exposed, MergedSourceExposure.Result.state] using verified.semantic
        have resident : InternedNestedProvenance.Edges middle
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) :=
          fun edge member => verified.edges rows middle exposed edge (List.mem_filter.mp member).1
        have children : ∀ child ∈ (rows.filter
            (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))).flatMap EdgeValue.children,
            Available middle child := by
          intro child member
          obtain ⟨edge, member, included⟩ := List.mem_flatMap.mp member
          exact semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge member) child included
        have constructed := InternedProbeProvenance.makeNode_available
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) middle
          semantic.1.normal.facts.coherent semantic.1.normal.facts.cached children
        have closedRows : MergedColdReaderClosedInputs.ClosedEdges
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) :=
          fun edge member => verified.closed rows middle exposed edge (List.mem_filter.mp member).1
        have constructedClosed := MergedColdReaderClosedInputs.makeNode_closed
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) middle
          semantic.1.normal.facts resident closedRows
        rw [built] at constructed constructedClosed
        exact ⟨constructed.2.2, constructedClosed⟩

private theorem retained_action
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (fuel uv oldHandle : Nat) (scs : List Suspended) (oldValue value : Node)
    (caller reached : Caller width) (before after : Cached) (queries : SourceEndpointMemo.Memos)
    (readAfter checked : Core) (heap : State Symbol Constraint)
    (selectedAction : EnumerateM Symbol Constraint Unit)
    (preparedField : MergedSourceComparison.Result Symbol Constraint
      (Node × Option (EnumerateM Symbol Constraint Unit)))
    (right : Option (List (Except Error ((Bool × Metadata Typing) × Core))))
    (ordinary : Option (List (Except Error ((Nat × Nat × List Suspended × Node) × Core)) ×
      Option (SourcePruningEnumerationNativeBranches.Result width)))
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel uv oldHandle
      scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before queries = .narrowed checked preparedField reached queries
        (some [.ok ((), after.core)]) (some after) right ordinary) :
    Success selectedAction checked () after.core := by
  simp only [runPrefix, reading, checking, decoded, prepared] at actual
  cases rawEq : ExceptT.run (selectedAction checked) with
  | nil => simp only [rawEq] at actual; cases actual
  | cons first rest =>
      cases first with
      | error fault => simp only [rawEq] at actual; cases actual
      | ok pair =>
          obtain ⟨token, observed⟩ := pair
          cases token
          cases rest with
          | cons _ _ => simp only [rawEq] at actual; cases actual
          | nil =>
              simp only [rawEq] at actual
              cases encoded : encodeNode value with
              | none => simp only [encoded] at actual; cases actual
              | some newHandle =>
                  simp only [encoded] at actual
                  cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
                      scs before observed with
                  | none => simp only [adapted] at actual; cases actual
                  | some attached =>
                      have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel
                          metadata uv (.inr newHandle) attached.core) = [.ok ((false, metadata), attached.core)] := by
                        rw [SourcePruningRecordTypes.recordTypes_inr]
                        rfl
                      simp only [adapted, recorded] at actual
                      have ⟨_checked, _prepared, _caller, _queries, actionSame, _candidate, _right, _ordinary⟩ :=
                        Result.narrowed.inj actual
                      have coreSame : observed = after.core := by
                        simpa only [Option.some.injEq, List.cons.injEq, Except.ok.injEq, Prod.mk.injEq,
                          true_and, and_true] using actionSame
                      rw [Success, ← coreSame, rawEq]
                      exact List.mem_singleton_self _

end Runtime

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem finish_preserves
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (uv : Nat) (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf 0 0 0 0 0 uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf 0 0 0 0 0 uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩

/-- The valid actual prefix preserves assignments backward, with the exact parked restriction. -/
theorem prefix_semantics
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query)) :
    PrefixMeaning formulas solver fuel uv caller before
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query) := by
  generalize actual : runPrefix holeKey fits admits graph templates stop order metadata
    fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed at valid ⊢
  have full := valid.2.1
  cases observed with
  | stopped read checked =>
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, impossible⟩ := full
      exact impossible
  | parked checked candidate raw =>
      obtain ⟨oldHandle, scs, readAfter, reading, checking, cached, same, core, _cacheValid,
        _safe, _pending, _counter, _ordered, _raw⟩ := full
      cases same
      have readSuccess : Success (getValue fuel uv) before.core
          (.unenumerated (some oldHandle) scs) readAfter := by
        rw [Success, reading]
        exact List.mem_singleton_self _
      have readFrame := (getValue_frame fuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
      have readStored := (EnumerationDriver.getValue_root fuel uv before.core readAfter _
        ready.safe ready.inside ready.root readSuccess).2.2.2
      have stored : before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
        simpa only [readFrame.values] using readStored
      have readReady := (EnumerationDriver.getValue_ready fuel uv before.core readAfter _ ready readSuccess).1
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter true cached.core := by
        rw [Success, core, checking]
        exact List.mem_singleton_self _
      refine ⟨oldHandle, scs, readAfter, stored, reading, ?_⟩
      intro ambient residualMeaning assignment
      exact (SourcePruningEnumerationNativeLanguage.satisfies_frame
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) residualMeaning assignment before.core readAfter readFrame).symm.trans
        (SourcePruningEnumerationRecursion.checkRepeated_true_satisfies caller.checked.native.machine.heap
          _ residualMeaning assignment fuel uv oldHandle scs readAfter cached.core readReady readStored checkSuccess)
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨next, finished⟩ := finish_preserves checkEmpty edgesOf uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap, selectedAction,
            final, decoded, narrowed, selectedPrepared, _prepared, reachedSame, queriesSame,
            post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, impossible, _right, _ordinary⟩ |
            ⟨newHandle, cached, nonempty, encoded, actionSame, cachedSame, _cacheValid, _safe,
              _pending, _ready, _stored, _waiting, _right, _rest⟩
          · cases impossible
          · have same : after = cached := Option.some.inj cachedSame
            subst cached
            have actionSuccess := retained_action holeKey fits admits graph templates stop order metadata
              fuel uv oldHandle scs oldValue value caller reached before after memos.query readAfter checked
              heap selectedAction prepared right ordinary reading checking decoded selectedPrepared
              (by simpa only [actionSame, queriesSame] using actual)
            have readSuccess : Success (getValue fuel uv) before.core
                (.unenumerated (some oldHandle) scs) readAfter := by
              rw [Success, reading]
              exact List.mem_singleton_self _
            have readFrame := (getValue_frame fuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
            have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
                caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter false checked := by
              rw [Success, checking]
              exact List.mem_singleton_self _
            have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
              caller.checked.native.machine.heap fuel uv oldHandle scs readAfter checked
              (readFrame.total ready.safe.1.total) checkSuccess
            have checkedFrame := readFrame.trans checkFrame
            have readStored := (EnumerationDriver.getValue_root fuel uv before.core readAfter _
              ready.safe ready.inside ready.root readSuccess).2.2.2
            have stored : before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
              simpa only [readFrame.values] using readStored
            obtain ⟨old, oldLookup, oldAvailable, oldClosed⟩ := realized uv oldHandle scs stored
            have oldSame : old = oldValue := Option.some.inj (oldLookup.symm.trans decoded)
            subst old
            have available := narrow_available holeKey fits admits metadata fuel uv oldValue value
              caller.checked.native.machine.heap heap initial.ready.semantic.ready oldAvailable oldClosed narrowed
            have valueAvailable : Available reached.checked.native.machine.heap value := by
              simpa only [reachedSame, SourceCurrentAllocatedPartialState.advance,
                SourceCurrentAllocatedQueryMemo.advancePhysical] using available.1
            obtain ⟨handle, encodedActual, newDecoded⟩ := available_readback reached.checked.native.machine.heap
              value post.context.ready.semantic.ready.semantic.1.normal.facts.coherent valueAvailable available.2
            have handleSame : handle = newHandle := Option.some.inj (encodedActual.symm.trans encoded)
            subst handle
            intro ambient residualMeaning assignment satisfied
            let language := SourcePruningEnumerationNativeLanguage.handles
              (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap
            have narrows : ∀ term, language newHandle term → language oldHandle term := by
              intro term accepted
              have valueAccepted := (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ newDecoded).mp accepted
              have oldAccepted := SourcePruningOuterNarrow.narrow_sound (SourceEqualityPCSGuard.holds formulas solver)
                ambient holeKey fits admits metadata fuel uv oldValue caller.checked.native.machine.heap value heap
                initial.ready.semantic.ready initial.ready.semantic.guarded oldAvailable oldClosed narrowed term valueAccepted
              exact (SourcePruningEnumerationNativeLanguage.handles_keeps _ _ _ _ _ _ _ decoded post.effects.keeps).mpr
                ⟨oldValue, decoded, oldAccepted⟩
            have actualAction := prepared_action holeKey fits admits metadata fuel fuel uv oldHandle newHandle
              scs oldValue value caller.checked.native.machine.heap heap narrowed nonempty encoded
            rw [selectedPrepared] at actualAction
            have selectedSame : selectedAction =
                (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
                  else representative fuel uv >>= fun selected =>
                    setValue selected (.unenumerated (some newHandle) scs)) :=
              Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actualAction).1).2
            rw [selectedSame] at actionSuccess
            by_cases equalHandle : newHandle = oldHandle
            · rw [ite_eq_left equalHandle] at actionSuccess
              have endpoint := (success_pure () () checked after.core).mp actionSuccess
              have checkedSatisfied : Satisfies language residualMeaning assignment checked := by
                simpa only [endpoint.2] using satisfied
              exact (SourcePruningEnumerationNativeLanguage.satisfies_keeps_frame
                (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
                reached.checked.native.machine.heap before.core checked residualMeaning assignment
                realized checkedFrame post.effects.keeps).mp checkedSatisfied
            · rw [ite_eq_right equalHandle] at actionSuccess
              obtain ⟨selected, resolved, readingRoot, written⟩ := (success_bind _ _ _ _ _).mp actionSuccess
              have resolvedFrame := representative_frame fuel uv selected checked resolved
                (checkedFrame.total ready.safe.1.total) readingRoot
              have checkedRoot : IsRoot checked.representatives uv :=
                ⟨ready.root.choose, (checkedFrame.reaches uv uv ready.root.choose).mpr ready.root.choose_spec⟩
              obtain ⟨found, foundLookup, selectedRoot, _endpoint⟩ :=
                (representative_success fuel uv checked resolved selected).mp readingRoot
              have selectedIsUv : selected = uv := by
                rw [selectedRoot]
                exact (UnionFind.reaches_unique
                  (UnionFind.findRoot_correct fuel checked.representatives uv found foundLookup).1
                  checkedRoot.choose_spec).1
              subst selected
              have wholeFrame := checkedFrame.trans resolvedFrame
              have resolvedStored : resolved.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
                simpa only [wholeFrame.values] using stored
              have writeMeaning := EnumerationSemantics.pending_write_semantics language residualMeaning assignment
                resolved after.core uv oldHandle newHandle scs resolvedStored written narrows
              have resolvedSatisfied := (writeMeaning.mp satisfied).1
              exact (SourcePruningEnumerationNativeLanguage.satisfies_keeps_frame
                (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
                reached.checked.native.machine.heap before.core resolved residualMeaning assignment
                realized wholeFrame post.effects.keeps).mp resolvedSatisfied

end MicroCFTA.SourcePruningEnumerationSelectedStep
