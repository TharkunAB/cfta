import MicroCFTA.SourceEqualityNativeEditWorker
import MicroCFTA.SourceEqualityNativeEditRanges
import MicroCFTA.SourceEqualityRequiredWorkerSound

/-!
# Successful checked native edit workers give exact physical graphs

Word checks stay at actual completed prefixes. Native and constructor
observations retain their full states. No initial cache invariant is needed
for this function-to-graph direction.
-/
namespace MicroCFTA.SourceEqualityNativeEditWorkerSound
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityNativeScoped SourceEqualityNativeEditGraph
open SourceEqualityNativeEditWorker SourceEqualityNativeEditRanges

/-- A completed sequence has a completed first operation and its literal continuation. -/
theorem bind_done (first : Result width Symbol Guard A)
    (next : A → NativeState width Symbol Guard → Result width Symbol Guard B) (result : B) (after : NativeState width Symbol Guard) :
    first.bind next = .done result after ↔ ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro completed; exact ⟨value, state, rfl, completed⟩
      · rintro ⟨actual, middle, same, completed⟩; cases same; exact completed
  | pending | unresolved | exhausted | native => simp [Result.bind]

/-- A successful constructor worker retains its literal heap equation and the same advanced native state. -/
theorem work_done [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A)
    (before : NativeState width Symbol Guard) (result : A) (after : NativeState width Symbol Guard)
    (done : work request before = .done result after) :
    ∃ heap, run request before.machine.heap = (result, heap) ∧ after = advanceHeap before heap := by
  have parts := Result.done.inj done
  exact ⟨_, Prod.ext parts.1 rfl, parts.2.symm⟩

/-- A successful native leaf receipt retains the exact checked native execution. -/
theorem leaf_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (target value : Value Symbol Guard)
    (before : NativeState width Symbol Guard) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, value⟩ .pure) before)
    (done : leaf emptyGuard conjoin fuel target value before = .done result after) : Step emptyGuard conjoin target value before result after := by
  cases actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, value⟩ .pure) before with
  | done output final =>
      simp only [leaf, actual] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact .done fuel ranges actual
  | yielded | failed | blocked => simp only [leaf, actual] at done; cases done

/-- Successful native head wrapping retains actual constructor normalization and unchanged memo state. -/
theorem head_graph [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : NativeState width Symbol Guard) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (done : head fuel value before = .done result after) :
    ∃ heap, SourceEqualityRequiredHead.Head value before.machine.heap result heap ∧ after = advanceHeap before heap := by
  cases actual : SourceEqualityRequiredWorker.head fuel value before.machine.heap with
  | done output heap =>
      simp only [head, actual] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact ⟨heap, SourceEqualityRequiredWorkerSound.head_graph fuel value before.machine.heap _ heap actual, rfl⟩
  | pending | unresolved | exhausted => simp only [head, actual] at done; cases done

/-- Exact checked node receipts lift through the actual source child scan. -/
theorem children_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (recur : Edits (Value Symbol Guard) → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard))
    (sound : ∀ edits value before, NodeRanges emptyGuard conjoin edits value before → ∀ result after,
      recur edits value before = .done result after → EditNode emptyGuard conjoin edits value before result after)
    (entries : List (Int × Edits (Value Symbol Guard))) (index : Nat) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (ranges : ChildrenRanges emptyGuard conjoin entries index values before) (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard)
    (done : children recur entries index values before = .done results after) : EditChildren emptyGuard conjoin entries index values before results after := by
  induction values generalizing index before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2; exact .nil
  | cons value values ih =>
      cases ranges with
      | unselected index absent rest =>
          simp only [children, absent] at done
          obtain ⟨tail, final, restDone, returned⟩ := (bind_done _ _ results after).mp done
          have parts := Result.done.inj returned
          cases parts.1; cases parts.2
          exact .unselected index absent (ih _ _ rest tail after restDone)
      | selected index found first rest =>
          simp only [children, found] at done
          obtain ⟨result, middle, firstDone, later⟩ := (bind_done _ _ results after).mp done
          have firstTrace := sound _ _ _ first result middle firstDone
          obtain ⟨tail, final, restDone, returned⟩ := (bind_done _ _ results after).mp later
          have parts := Result.done.inj returned
          cases parts.1; cases parts.2
          exact .selected index found firstTrace (ih _ _ (rest result middle firstTrace) tail after restDone)

/-- Exact checked child receipts lift through every actual row reconstruction. -/
theorem rows_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (recur : Edits (Value Symbol Guard) → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard))
    (sound : ∀ edits value before, NodeRanges emptyGuard conjoin edits value before → ∀ result after,
      recur edits value before = .done result after → EditNode emptyGuard conjoin edits value before result after)
    (entries : List (Int × Edits (Value Symbol Guard))) (edges : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard)
    (ranges : RowsRanges emptyGuard conjoin entries edges before) (results : List (EdgeValue Symbol Guard)) (after : NativeState width Symbol Guard)
    (done : rows recur entries edges before = .done results after) : EditRows emptyGuard conjoin entries edges before results after := by
  induction edges generalizing before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2; exact .nil
  | cons edge edges ih =>
      cases ranges with
      | cons childRanges rest =>
          simp only [rows] at done
          obtain ⟨values, middle, childrenDone, later⟩ := (bind_done _ _ results after).mp done
          have childTrace := children_graph emptyGuard conjoin recur sound _ _ _ _ childRanges values middle childrenDone
          obtain ⟨result, edgeAfter, edgeDone, tail⟩ := (bind_done _ _ results after).mp later
          obtain ⟨heap, built, rfl⟩ := work_done _ middle result edgeAfter edgeDone
          obtain ⟨more, final, restDone, returned⟩ := (bind_done _ _ results after).mp tail
          have parts := Result.done.inj returned
          cases parts.1; cases parts.2
          have restTrace := ih _ (rest values middle childTrace) more after (by simpa only [built] using restDone)
          exact .cons childTrace built (by simpa only [built] using restTrace)

/-- Every checked successful bounded node worker supplies the actual full native edit graph. -/
theorem edit_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel readFuel nativeFuel : Nat)
    (edits : Edits (Value Symbol Guard)) (value : Value Symbol Guard) (before : NativeState width Symbol Guard)
    (ranges : NodeRanges emptyGuard conjoin edits value before) (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (done : edit emptyGuard conjoin fuel readFuel nativeFuel edits value before = .done result after) : EditNode emptyGuard conjoin edits value before result after := by
  induction fuel generalizing edits value before result after with
  | zero => cases done
  | succ fuel ih =>
      cases ranges with
      | leaf ranges => exact .leaf (leaf_graph emptyGuard conjoin nativeFuel _ _ before result after ranges done)
      | empty =>
          have parts := Result.done.inj done
          cases parts.1; cases parts.2; exact .empty
      | ordinary rowsRanges =>
          obtain ⟨rebuilt, middle, rowsDone, builtDone⟩ := (bind_done _ _ result after).mp done
          obtain ⟨heap, built, rfl⟩ := work_done _ middle result after builtDone
          exact .ordinary (rows_graph emptyGuard conjoin (edit emptyGuard conjoin fuel readFuel nativeFuel) ih _ _ _ rowsRanges rebuilt middle rowsDone) built
      | recursive recursive body =>
          rename_i entries
          have equation : edit emptyGuard conjoin (fuel + 1) readFuel nativeFuel (.editBelow entries) value before =
              (head readFuel value before).bind (fun exposed after => edit emptyGuard conjoin fuel readFuel nativeFuel (.editBelow entries) exposed after) := by
            cases value with
            | empty | reference | node => cases recursive
            | union | mu => rfl
          rw [equation] at done
          obtain ⟨exposed, middle, headDone, bodyDone⟩ := (bind_done _ _ result after).mp done
          obtain ⟨heap, headTrace, rfl⟩ := head_graph readFuel _ before exposed middle headDone
          exact .recursive recursive headTrace (ih _ _ _ (body exposed heap headTrace) result after bodyDone)

end MicroCFTA.SourceEqualityNativeEditWorkerSound
