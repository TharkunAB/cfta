/-- Every retained cache of the valid actual prefix preserves the original isolated boundary. -/
theorem prefix_isolated
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (held heldHandle : Nat) (value : Node)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query)) :
    match runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query with
    | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
        IsolatedPending held heldHandle after.core
    | _ => True := by
  have ready := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory
    stop order metadata caller memos before uv packet chosen
  have different := packet_restart_ne formulas solver inventory caller memos metadata before
    held heldHandle uv value stop order packet isolated decoded boundary chosen
  generalize actual : runPrefix holeKey fits admits graph templates stop order metadata
    fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed at valid ⊢
  have full := valid.2.1
  cases observed with
  | stopped read checked => trivial
  | parked checked candidate raw =>
      obtain ⟨oldHandle, scs, readAfter, reading, checking, cached, same, core, _cacheValid,
        _safe, _pending, _counter, _ordered, _raw⟩ := full
      cases same
      have readSuccess : Success (getValue fuel uv) before.core
          (.unenumerated (some oldHandle) scs) readAfter := by
        rw [Success, reading]
        exact List.mem_singleton_self _
      have frame := (getValue_frame fuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
      have readReady := (EnumerationDriver.getValue_ready fuel uv before.core readAfter _ ready readSuccess).1
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter true cached.core := by
        rw [Success, core, checking]
        exact List.mem_singleton_self _
      exact (isolated.through_frame frame).through_checkRepeated caller.checked.native.machine.heap
        held heldHandle fuel uv oldHandle scs readAfter cached.core true readReady different checkSuccess
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨next, finished⟩ := finish_cache_fields checkEmpty edgesOf uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap, selectedAction,
            final, oldDecoded, narrowed, selectedPrepared, _prepared, _reachedSame, queriesSame,
            _post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, impossible, _right, _ordinary⟩ |
            ⟨newHandle, cached, nonempty, encoded, actionSame, cachedSame, _cacheValid, _safe,
              _pending, _ready, _stored, _waiting, _right, _rest⟩
          · cases impossible
          · have same : after = cached := Option.some.inj cachedSame
            subst cached
            have actionSuccess := retained_action_success holeKey fits admits graph templates stop order metadata
              fuel uv oldHandle scs oldValue value caller reached before after memos.query readAfter checked
              heap selectedAction prepared right ordinary reading checking oldDecoded selectedPrepared
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
            have wholeFrame := readFrame.trans checkFrame
            have checkedRoot : IsRoot checked.representatives uv :=
              ⟨ready.root.choose, (wholeFrame.reaches uv uv ready.root.choose).mpr ready.root.choose_spec⟩
            have readStored := (EnumerationDriver.getValue_root fuel uv before.core readAfter _
              ready.safe ready.inside ready.root readSuccess).2.2.2
            have checkedStored : checked.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
              simpa only [checkFrame.values] using readStored
            exact (isolated.through_frame wholeFrame).through_prepared_nonempty
              holeKey fits admits metadata held heldHandle fuel fuel uv oldHandle newHandle scs oldValue value
              caller.checked.native.machine.heap heap selectedAction checked after.core
              (wholeFrame.total ready.safe.1.total) checkedRoot different checkedStored narrowed nonempty encoded
              selectedPrepared actionSuccess

end MicroCFTA.SourcePruningEnumerationSelectedStep

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationDischargeHistory InternedConstructorTemplates
open SourcePruningEnumerationNodes
