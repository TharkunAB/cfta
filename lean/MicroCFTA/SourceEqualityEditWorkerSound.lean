import MicroCFTA.SourceEqualityEditWorker

/-!
# Successful edit execution supplies its exact call graph

The proof retains actual callback equations, constructor requests, and every
intermediate cache. Pending, unresolved, and exhausted results cannot supply
a successful graph. No ready-cache or callback completion premise is needed.
-/
namespace MicroCFTA.SourceEqualityEditWorkerSound
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityEditGraph SourceEqualityEditWorker
open SourceEqualityRequiredWorker (Result)
open SourceEqualityRequiredWorkerSound (bind_done work_done head_graph)

/-- Exact node callback receipts lift through the finite original-position child scan. -/
theorem children_graph [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (recur : Edits Action → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (sound : ∀ edits value before result after, recur edits value before = .done result after → EditNode call edits value before result after)
    (entries : List (Int × Edits Action)) (index : Nat) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : children recur entries index values before = .done results after) :
    EditChildren call entries index values before results after := by
  induction values generalizing index before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1
      cases parts.2
      exact .nil
  | cons value values ih =>
      cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
      | none =>
          simp only [children, found] at done
          obtain ⟨tail, final, tailDone, returned⟩ := (bind_done _ _ results after).mp done
          have parts := Result.done.inj returned
          cases parts.1
          cases parts.2
          exact .unselected index found (ih (index + 1) before tail after tailDone)
      | some edits =>
          simp only [children, found] at done
          obtain ⟨result, middle, firstDone, later⟩ := (bind_done _ _ results after).mp done
          obtain ⟨tail, final, tailDone, returned⟩ := (bind_done _ _ results after).mp later
          have parts := Result.done.inj returned
          cases parts.1
          cases parts.2
          exact .selected index found (sound edits value before result middle firstDone)
            (ih (index + 1) middle tail after tailDone)

/-- Every successful row scan retains all actual edge and child receipts in source order. -/
theorem rows_graph [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (recur : Edits Action → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (sound : ∀ edits value before result after, recur edits value before = .done result after → EditNode call edits value before result after)
    (entries : List (Int × Edits Action)) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : rows recur entries edges before = .done results after) : EditRows call entries edges before results after := by
  induction edges generalizing before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1
      cases parts.2
      exact .nil
  | cons edge edges ih =>
      simp only [rows] at done
      obtain ⟨values, middle, childDone, later⟩ := (bind_done _ _ results after).mp done
      obtain ⟨result, afterEdge, edgeDone, later⟩ := (bind_done _ _ results after).mp later
      obtain ⟨tail, final, tailDone, returned⟩ := (bind_done _ _ results after).mp later
      have parts := Result.done.inj returned
      cases parts.1
      cases parts.2
      exact .cons (children_graph call recur sound entries 0 edge.children before values middle childDone)
        (work_done _ middle result afterEdge edgeDone) (ih afterEdge tail after tailDone)

/-- Every completed instrumented node edit follows the physical source graph. -/
theorem edit_graph [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) (fuel readFuel : Nat)
    (edits : Edits Action) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : edit call fuel readFuel edits value before = .done result after) : EditNode call edits value before result after := by
  induction fuel generalizing edits value before result after with
  | zero => cases done
  | succ fuel ih =>
      cases edits with
      | editAt action => exact .leaf done
      | editBelow entries =>
          cases value with
          | empty =>
              have parts := Result.done.inj done
              cases parts.1
              cases parts.2
              exact .empty
          | reference => cases done
          | node entry edges depth free =>
              obtain ⟨rebuilt, middle, rowsDone, nodeDone⟩ := (bind_done _ _ result after).mp done
              exact .ordinary (rows_graph call (edit call fuel readFuel) ih entries edges before rebuilt middle rowsDone)
                (work_done _ middle result after nodeDone)
          | union entry members depth free =>
              obtain ⟨exposed, middle, headDone, bodyDone⟩ := (bind_done _ _ result after).mp done
              exact .recursive trivial (head_graph readFuel _ before exposed middle headDone)
                (ih (.editBelow entries) exposed middle result after bodyDone)
          | mu entry body depth ordinary =>
              obtain ⟨exposed, middle, headDone, bodyDone⟩ := (bind_done _ _ result after).mp done
              exact .recursive trivial (head_graph readFuel _ before exposed middle headDone)
                (ih (.editBelow entries) exposed middle result after bodyDone)

/-- Actual compiled list execution retains the ignored-root-leaf branch or its exact child graph. -/
theorem editAll_graph [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) (fuel readFuel : Nat)
    (edits : List (Path × Action)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : editAll call fuel readFuel edits values before = .done results after) :
    EditList call (build edits) values before results after := by
  cases compiled : build edits with
  | editAt action =>
      simp only [editAll, editList, compiled] at done
      have parts := Result.done.inj done
      cases parts.1
      cases parts.2
      exact .leaf
  | editBelow entries =>
      exact .children (children_graph call (edit call fuel readFuel) (edit_graph call fuel readFuel) entries 0 values before results after
        (by simpa only [editAll, editList, compiled] using done))

end MicroCFTA.SourceEqualityEditWorkerSound
