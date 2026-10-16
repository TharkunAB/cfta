import MicroCFTA.SourceCurrentMemoSharedEditWorker
import MicroCFTA.SourceCurrentMemoSharedEditRanges
import MicroCFTA.SourceCurrentMemoSharedLeafWorkerProofs
import MicroCFTA.SourceEqualityRequiredWorkerSound

/-!
# Successful shared edit workers give actual source graphs

Target and native checks stay at actual completed prefixes. Every stored
target and full native state follow the literal source control. This
function-to-graph direction needs no initial cache invariant.
-/
namespace MicroCFTA.SourceCurrentMemoSharedEditWorkerSound
open InternedConstructorTemplates SourceEqualityEdits SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedLeafWorker SourceCurrentMemoSharedLeafWorkerProofs SourceCurrentMemoSharedEditGraph
open SourceCurrentMemoSharedEditWorker SourceCurrentMemoSharedEditRanges

/-- A successful constructor worker retains its literal heap equation and the same advanced native state. -/
theorem work_done [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A)
    (before : SharedState width Symbol Guard) (result : A) (after : SharedState width Symbol Guard)
    (done : work request before = .done result after) :
    ∃ heap, run request before.native.machine.heap = (result, heap) ∧ after = advanceHeap before heap := by
  have parts := Outcome.done.inj done
  exact ⟨_, Prod.ext parts.1 rfl, parts.2.symm⟩

/-- Successful native head wrapping retains actual constructor normalization and unchanged memo state. -/
theorem head_graph [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : SharedState width Symbol Guard) (result : Value Symbol Guard) (after : SharedState width Symbol Guard)
    (done : head fuel value before = .done result after) :
    ∃ heap, SourceEqualityRequiredHead.Head value before.native.machine.heap result heap ∧ after = advanceHeap before heap := by
  cases actual : SourceEqualityRequiredWorker.head fuel value before.native.machine.heap with
  | done output heap =>
      simp only [head, actual] at done
      have parts := Outcome.done.inj done
      cases parts.1; cases parts.2
      exact ⟨heap, SourceEqualityRequiredWorkerSound.head_graph fuel value before.native.machine.heap _ heap actual, rfl⟩
  | pending | unresolved | exhausted => simp only [head, actual] at done; cases done

/-- Exact checked node receipts lift through the actual source child scan. -/
theorem children_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Outcome width Symbol Guard (Value Symbol Guard))
    (sound : ∀ edits value before, NodeRanges emptyGuard conjoin clear top record originals edits value before → ∀ result after,
      recur edits value before = .done result after → EditNode emptyGuard conjoin clear top record originals edits value before result after)
    (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat) (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard)
    (ranges : ChildrenRanges emptyGuard conjoin clear top record originals entries index values before) (results : List (Value Symbol Guard)) (after : SharedState width Symbol Guard)
    (done : children recur entries index values before = .done results after) : EditChildren emptyGuard conjoin clear top record originals entries index values before results after := by
  induction values generalizing index before results after with
  | nil =>
      have parts := Outcome.done.inj done
      cases parts.1; cases parts.2; exact .nil
  | cons value values ih =>
      cases ranges with
      | unselected index absent rest =>
          simp only [children, absent] at done
          obtain ⟨tail, final, restDone, returned⟩ := (bind_done_iff _ _ results after).mp done
          have parts := Outcome.done.inj returned
          cases parts.1; cases parts.2
          exact .unselected index absent (ih _ _ rest tail after restDone)
      | selected index found first rest =>
          simp only [children, found] at done
          obtain ⟨result, middle, firstDone, later⟩ := (bind_done_iff _ _ results after).mp done
          have firstTrace := sound _ _ _ first result middle firstDone
          obtain ⟨tail, final, restDone, returned⟩ := (bind_done_iff _ _ results after).mp later
          have parts := Outcome.done.inj returned
          cases parts.1; cases parts.2
          exact .selected index found firstTrace (ih _ _ (rest result middle firstTrace) tail after restDone)

/-- Exact checked child receipts lift through every actual row reconstruction. -/
theorem rows_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Outcome width Symbol Guard (Value Symbol Guard))
    (sound : ∀ edits value before, NodeRanges emptyGuard conjoin clear top record originals edits value before → ∀ result after,
      recur edits value before = .done result after → EditNode emptyGuard conjoin clear top record originals edits value before result after)
    (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard)) (before : SharedState width Symbol Guard)
    (ranges : RowsRanges emptyGuard conjoin clear top record originals entries edges before) (results : List (EdgeValue Symbol Guard)) (after : SharedState width Symbol Guard)
    (done : rows recur entries edges before = .done results after) : EditRows emptyGuard conjoin clear top record originals entries edges before results after := by
  induction edges generalizing before results after with
  | nil =>
      have parts := Outcome.done.inj done
      cases parts.1; cases parts.2; exact .nil
  | cons edge edges ih =>
      cases ranges with
      | cons childRanges rest =>
          simp only [rows] at done
          obtain ⟨values, middle, childrenDone, later⟩ := (bind_done_iff _ _ results after).mp done
          have childTrace := children_graph emptyGuard conjoin clear top record originals recur sound _ _ _ _ childRanges values middle childrenDone
          obtain ⟨result, edgeAfter, edgeDone, tail⟩ := (bind_done_iff _ _ results after).mp later
          obtain ⟨heap, built, rfl⟩ := work_done _ middle result edgeAfter edgeDone
          obtain ⟨more, final, restDone, returned⟩ := (bind_done_iff _ _ results after).mp tail
          have parts := Outcome.done.inj returned
          cases parts.1; cases parts.2
          have restTrace := ih _ (rest values middle childTrace) more after (by simpa only [built] using restDone)
          exact .cons childTrace built (by simpa only [built] using restTrace)

/-- Every checked successful bounded node worker supplies the actual full native edit graph. -/
theorem edit_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (fuel p h w c n : Nat)
    (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard) (before : SharedState width Symbol Guard)
    (ranges : NodeRanges emptyGuard conjoin clear top record originals edits value before) (result : Value Symbol Guard) (after : SharedState width Symbol Guard)
    (done : edit emptyGuard conjoin clear top record originals fuel p h w c n edits value before = .done result after) : EditNode emptyGuard conjoin clear top record originals edits value before result after := by
  induction fuel generalizing edits value before result after with
  | zero => cases done
  | succ fuel ih =>
      cases ranges with
      | leaf ranges => exact .leaf (leaf_graph emptyGuard conjoin clear top record originals p h w c n _ _ before result after ranges done)
      | empty =>
          have parts := Outcome.done.inj done
          cases parts.1; cases parts.2; exact .empty
      | ordinary rowsRanges =>
          obtain ⟨rebuilt, middle, rowsDone, builtDone⟩ := (bind_done_iff _ _ result after).mp done
          obtain ⟨heap, built, rfl⟩ := work_done _ middle result after builtDone
          exact .ordinary (rows_graph emptyGuard conjoin clear top record originals (edit emptyGuard conjoin clear top record originals fuel p h w c n) ih _ _ _ rowsRanges rebuilt middle rowsDone) built
      | recursive recursive body =>
          rename_i entries
          have equation : edit emptyGuard conjoin clear top record originals (fuel + 1) p h w c n (.editBelow entries) value before =
              (head h value before).bind (fun exposed after => edit emptyGuard conjoin clear top record originals fuel p h w c n (.editBelow entries) exposed after) := by
            cases value with
            | empty | reference | node => cases recursive
            | union | mu => rfl
          rw [equation] at done
          obtain ⟨exposed, middle, headDone, bodyDone⟩ := (bind_done_iff _ _ result after).mp done
          obtain ⟨heap, headTrace, rfl⟩ := head_graph h _ before exposed middle headDone
          exact .recursive recursive headTrace (ih _ _ _ (body exposed heap headTrace) result after bodyDone)

/-- Successful checked list execution retains the actual memo-aware list graph. -/
theorem list_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (e p h w c n : Nat) (edits : Edits EqualityNormalize.Path) (values : List (Value Symbol Guard))
    (before : SharedState width Symbol Guard)
    (ranges : ListRanges emptyGuard conjoin clear top record originals edits values before)
    (results : List (Value Symbol Guard)) (after : SharedState width Symbol Guard)
    (done : editList (edit emptyGuard conjoin clear top record originals e p h w c n) edits values before = .done results after) :
    EditList emptyGuard conjoin clear top record originals edits values before results after := by
  cases edits with
  | editAt target =>
      have parts := Outcome.done.inj done
      cases parts.1; cases parts.2; exact .leaf
  | editBelow entries =>
      exact .children (children_graph emptyGuard conjoin clear top record originals
        (edit emptyGuard conjoin clear top record originals e p h w c n)
        (edit_graph emptyGuard conjoin clear top record originals e p h w c n)
        entries 0 values before ranges results after done)

end MicroCFTA.SourceCurrentMemoSharedEditWorkerSound
