import MicroCFTA.SourceEqualityProjectionWorker
import MicroCFTA.SourceEqualityRequiredWorkerSound

/-!
# Successful general path workers give exact source graphs

The proof retains all row reads, source list order, head normalization,
and constructor equations. Failure outcomes cannot become completed graphs.
-/
namespace MicroCFTA.SourceEqualityProjectionWorkerSound
open InternedConstructorTemplates SourceEqualityProjectionGraph SourceEqualityProjectionWorker
open SourceEqualityRequiredWorker (Result)
open SourceEqualityRequiredWorkerSound (bind_done work_done head_graph)

/-- Every successful closed-union row scan gives the complete ordered read graph. -/
theorem readAll_graph [DecidableEq (EdgeKey Symbol Guard)] (readFuel : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : readAll readFuel values before = .done edges after) :
    SourceEqualityProjectionUnion.ReadAll values before edges after := by
  induction values generalizing before edges after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact .nil
  | cons value values ih =>
      cases read : MergedFreshOrdinaryExposure.nodeEdges readFuel value before with
      | done rows middle =>
          simp only [readAll, read] at done
          obtain ⟨more, final, rest, returned⟩ := (bind_done _ _ edges after).mp done
          have parts := Result.done.inj returned
          cases parts.1; cases parts.2
          exact .cons (.done readFuel read) (ih middle more after rest)
      | pending | unresolved | exhausted => simp only [readAll, read] at done; cases done

/-- Successful source union execution retains the exact final node request. -/
theorem union_graph [DecidableEq (EdgeKey Symbol Guard)] (readFuel : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : union readFuel values before = .done result after) :
    SourceEqualityProjectionUnion.Union values before result after := by
  obtain ⟨edges, middle, read, built⟩ := (bind_done _ _ result after).mp done
  exact .node (readAll_graph readFuel values before edges middle read) (work_done _ middle result after built)

/-- Exact child callback receipts lift through the source mapMaybe scan. -/
theorem rows_graph [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (path : List Int) (sound : ∀ value before result after, recur value before = .done result after → Project path value before result after)
    (index : Int) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : rows recur index edges before = .done results after) : ProjectRows path index edges before results after := by
  induction edges generalizing before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact .nil
  | cons edge edges ih =>
      cases found : select edge.children index with
      | none =>
          simp only [rows, found] at done
          exact .missing found (ih before results after done)
      | some child =>
          simp only [rows, found] at done
          obtain ⟨result, middle, first, later⟩ := (bind_done _ _ results after).mp done
          obtain ⟨more, final, rest, returned⟩ := (bind_done _ _ results after).mp later
          have parts := Result.done.inj returned
          cases parts.1; cases parts.2
          exact .selected found (sound child before result middle first) (ih middle more after rest)

/-- Every successful bounded node projection supplies its exact physical source graph. -/
theorem project_graph [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (path : List Int) (value : Value Symbol Guard) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : project fuel readFuel path value before = .done result after) : Project path value before result after := by
  induction fuel generalizing path value before result after with
  | zero => cases done
  | succ fuel ih =>
      cases path with
      | nil =>
          have parts := Result.done.inj done
          cases parts.1; cases parts.2
          exact .root
      | cons index path =>
          cases value with
          | empty =>
              have parts := Result.done.inj done
              cases parts.1; cases parts.2
              exact .empty
          | reference => cases done
          | node entry edges depth free =>
              obtain ⟨values, middle, scanned, united⟩ := (bind_done _ _ result after).mp done
              exact .ordinary (rows_graph (project fuel readFuel path) path (ih path) index edges before values middle scanned)
                (union_graph readFuel values middle result after united)
          | union entry members depth free =>
              obtain ⟨exposed, middle, headDone, body⟩ := (bind_done _ _ result after).mp done
              exact .recursive True.intro (head_graph readFuel _ before exposed middle headDone)
                (ih (index :: path) exposed middle result after body)
          | mu entry body probe ordinary =>
              obtain ⟨exposed, middle, headDone, body⟩ := (bind_done _ _ result after).mp done
              exact .recursive True.intro (head_graph readFuel _ before exposed middle headDone)
                (ih (index :: path) exposed middle result after body)

/-- Every successful forest projection supplies the distinct source forest graph. -/
theorem forest_graph [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (path : List Int) (values : List (Value Symbol Guard)) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : forest fuel readFuel path values before = .done result after) : Forest path values before result after := by
  cases path with
  | nil => exact .root (union_graph readFuel values before result after done)
  | cons index path =>
      cases found : select values index with
      | none =>
          simp only [forest, found] at done
          have parts := Result.done.inj done
          cases parts.1; cases parts.2
          exact .missing found
      | some value =>
          simp only [forest, found] at done
          exact .selected found (project_graph fuel readFuel path value before result after done)

end MicroCFTA.SourceEqualityProjectionWorkerSound
