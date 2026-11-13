import MicroCFTA.SourcePruningEnumerationSharedBranching

namespace MicroCFTA.SourcePruningEnumerationSharedBranching
open InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- An actual completed prefix supplies the suffix endpoint; a stopped prefix retains its full result. -/
theorem scan_append
    (visit : Edge → Caller width → Queries → Cached → Result Output Reason width)
    (before : Cached) (earlierRows suffix : List Edge) (caller : Caller width) (queries : Queries) :
    scan visit before (earlierRows ++ suffix) caller queries =
      match scan visit before earlierRows caller queries with
      | .stopped processed outputs current => .stopped processed outputs current
      | .complete processed outputs reached saved =>
          match scan visit before suffix reached saved with
          | .complete later more finalCaller finalQueries =>
              .complete (processed ++ later) (outputs ++ more) finalCaller finalQueries
          | .stopped later more current =>
              .stopped (processed ++ later) (outputs ++ more) current
 := by
  induction earlierRows generalizing caller queries with
  | nil =>
      simp only [List.nil_append, scan]
      cases scan visit before suffix caller queries <;> rfl
  | cons edge earlierRows ih =>
      rw [List.cons_append]
      cases head : visit edge caller queries before with
      | stopped processed outputs current =>
          simp only [scan, head]
      | complete processed outputs reached saved =>
          simp only [scan, head]
          rw [ih]
          cases scan visit before earlierRows reached saved with
          | stopped later more current => rfl
          | complete later more middleCaller middleQueries =>
              dsimp only
              cases scan visit before suffix middleCaller middleQueries <;>
                simp only [List.append_assoc]

end MicroCFTA.SourcePruningEnumerationSharedBranching
