import MicroCFTA.SourceEqualityRequiredWorker

/-!
# Successful worker execution supplies the exact physical call graph

The proof keeps all actual constructor equations and intermediate caches.
Failure and exhausted-bound outcomes cannot become successful receipts.
No initial cache invariant or successful whole-worker premise is supplied.
-/
namespace MicroCFTA.SourceEqualityRequiredWorkerSound
open InternedConstructorTemplates SourceEqualityNeeded
open SourceEqualityRequiredGraph SourceEqualityRequiredHead SourceEqualityRequiredWorker

/-- A completed sequence has a completed first result and its exact continuation. -/
theorem bind_done (first : Result Symbol Guard A) (next : A → State Symbol Guard → Result Symbol Guard B)
    (result : B) (after : State Symbol Guard) :
    first.bind next = .done result after ↔
      ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value before =>
      constructor
      · intro completed; exact ⟨value, before, rfl, completed⟩
      · rintro ⟨actual, middle, same, completed⟩
        cases same
        exact completed
  | pending | unresolved | exhausted => simp [Result.bind]

/-- A successful ordinary constructor receipt retains its literal source request equation. -/
theorem work_done [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A)
    (before : State Symbol Guard) (result : A) (after : State Symbol Guard)
    (done : work request before = .done result after) : run request before = (result, after) := by
  have parts := Result.done.inj done
  exact Prod.ext parts.1 parts.2

/-- Completed instrumented head exposure gives the exact two-operation graph. -/
theorem head_graph [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : head fuel value before = .done result after) : Head value before result after := by
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done edges middle =>
      simp only [head, exposed] at done
      exact .read fuel edges middle exposed (work_done _ middle result after done)
  | pending | unresolved | exhausted => simp only [head, exposed] at done; cases done

/-- Exact completed callbacks lift through the source finite child scan. -/
theorem children_graph [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (sound : ∀ needed value before result after, recur needed value before = .done result after →
      RequireNode needed value before result after)
    (entries : List (Int × Needed)) (index : Nat) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : children recur entries index values before = .done results after) :
    RequireChildren entries index values before results after := by
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
      | some needed =>
          simp only [children, found] at done
          obtain ⟨result, middle, firstDone, later⟩ := (bind_done _ _ results after).mp done
          obtain ⟨tail, final, tailDone, returned⟩ := (bind_done _ _ results after).mp later
          have parts := Result.done.inj returned
          cases parts.1
          cases parts.2
          exact .selected index found (sound needed value before result middle firstDone)
            (ih (index + 1) middle tail after tailDone)

/-- Successful row scans reject or rebuild exactly the source rows, in order. -/
theorem rows_graph [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (sound : ∀ needed value before result after, recur needed value before = .done result after →
      RequireNode needed value before result after)
    (entries : List (Int × Needed)) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : rows recur entries edges before = .done results after) : RequireRows entries edges before results after := by
  induction edges generalizing before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1
      cases parts.2
      exact .nil
  | cons edge edges ih =>
      cases fit : fits (.node entries) edge.children.length with
      | false =>
          simp only [rows, fit, Bool.false_eq_true, ite_false] at done
          exact .rejected fit (ih before results after done)
      | true =>
          simp only [rows, fit, ite_true] at done
          obtain ⟨values, middle, childDone, later⟩ := (bind_done _ _ results after).mp done
          obtain ⟨result, afterEdge, edgeDone, tail⟩ := (bind_done _ _ results after).mp later
          obtain ⟨tailResults, final, tailDone, returned⟩ := (bind_done _ _ results after).mp tail
          have parts := Result.done.inj returned
          cases parts.1
          cases parts.2
          exact .kept fit (children_graph recur sound entries 0 edge.children before values middle childDone)
            (work_done _ middle result afterEdge edgeDone) (ih afterEdge tailResults after tailDone)

/-- Every successful instrumented node run supplies its full exact physical call graph. -/
theorem require_graph [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (needed : Needed) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : require fuel readFuel needed value before = .done result after) : RequireNode needed value before result after := by
  induction fuel generalizing needed value before result after with
  | zero => cases done
  | succ fuel ih =>
      cases needed with
      | node entries =>
          by_cases nonempty : entries = []
          · subst entries
            have parts := Result.done.inj done
            cases parts.1
            cases parts.2
            exact .identity
          · simp only [require, List.isEmpty_iff, nonempty, ite_false] at done
            cases value with
            | empty =>
                have parts := Result.done.inj done
                cases parts.1
                cases parts.2
                exact .empty nonempty
            | reference => cases done
            | node entry edges depth free =>
                obtain ⟨rebuilt, middle, rowsDone, nodeDone⟩ := (bind_done _ _ result after).mp done
                exact .ordinary nonempty (rows_graph (require fuel readFuel) ih entries edges before rebuilt middle rowsDone)
                  (work_done _ middle result after nodeDone)
            | union entry members depth free =>
                obtain ⟨exposed, middle, headDone, bodyDone⟩ := (bind_done _ _ result after).mp done
                exact .recursive nonempty True.intro (head_graph readFuel _ before exposed middle headDone)
                  (ih (.node entries) exposed middle result after bodyDone)
            | mu entry body depth ordinary =>
                obtain ⟨exposed, middle, headDone, bodyDone⟩ := (bind_done _ _ result after).mp done
                exact .recursive nonempty True.intro (head_graph readFuel _ before exposed middle headDone)
                  (ih (.node entries) exposed middle result after bodyDone)

end MicroCFTA.SourceEqualityRequiredWorkerSound
