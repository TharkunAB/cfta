import MicroCFTA.RecursiveRuntimeDispatch
import MicroCFTA.CheckedRankQueries

/-!
# Inverse queries after bounding a recursive generator

`boundedStatic` constructs a finite outcome callback even when recursive
terms are absent. Its candidate list is then empty. The recursive query
instead reports unavailable terms. Public term selection retains its
separate missing-term error in both cases.
-/
namespace MicroCFTA.BoundedRecursiveDispatch
open CheckedRankQueries

/-- A successful bound installs a finite callback; absent recursive terms produce no candidates. -/
def source (result : Except Cause (Option (TermValue → List Candidate))) : Source Cause TermValue :=
  .finite (result.map (fun callback => callback.getD (fun _ => [])))

/-- A bounded construction failure remains the original failure before rank filtering. -/
theorem source_error (cause : Cause) (wanted : TermValue) :
    candidates (source (.error cause)) wanted = .error (.source cause) := rfl

/-- The finite wrapper reads an empty candidate list when the recursive term field is absent. -/
theorem absent_candidates (wanted : TermValue) :
    candidates (source (Cause := Cause) (.ok none)) wanted = .ok [] := rfl

/-- Missing bounded terms give no inverse ranks, regardless of term selection errors. -/
theorem absent_ranks [DecidableEq TermValue] (decode : Int → Except Failure TermValue) (wanted : TermValue) :
    ranksOf decode (source (Cause := Cause) (.ok none)) wanted = .ok [] := rfl

/-- The public least-rank query reports nonmembership after reading that empty list. -/
theorem absent_rank [DecidableEq TermValue] (decode : Int → Except Failure TermValue) (wanted : TermValue) :
    rankOf decode (source (Cause := Cause) (.ok none)) wanted = .error .termNotInLanguage := rfl

/-- With a term callback, finite wrapping preserves the complete public checked-candidate filter. -/
theorem present_ranks [DecidableEq TermValue] (decode : Int → Except Failure TermValue)
    (callback : TermValue → List Candidate) (wanted : TermValue) :
    ranksOf decode (source (Cause := Cause) (.ok (some callback))) wanted =
      ranksOf decode (.recursive (.ok (some callback)) : Source Cause TermValue) wanted := rfl

/-- The same callback laws establish both rank inverses after finite wrapping. -/
theorem present_rank_exact [DecidableEq TermValue] (decode : Int → Except Failure TermValue)
    (callback : TermValue → List Candidate) (wanted : TermValue)
    (sound : CheckedSound decode wanted (callback wanted))
    (complete : Complete decode wanted (callback wanted))
    (ordered : ((callback wanted).map Candidate.rank).Pairwise (· ≤ ·)) (rank : Int) :
    rankOf decode (source (Cause := Cause) (.ok (some callback))) wanted = .ok rank ↔
      decode rank = .ok wanted ∧ ∀ other, decode other = .ok wanted → rank ≤ other :=
  rankOf_exact decode _ wanted _ rfl sound complete ordered rank

/-- The complete family inverse uses the finite wrapper's absent-term branch. -/
def familyRanks [DecidableEq (KeyedNaryAlignment.EngineTerm Symbol)] (code : Key → Nat)
    (program : Key → RecursiveJoinBodyFields.CheckedBody Key Root Symbol Root)
    (key : Key) (metadata : RecursiveJoinRuntime.Metadata) (limit : Nat) (view : IntegerTermViews.View)
    (wanted : List (KeyedNaryAlignment.EngineTerm Symbol)) : Except (Error Cause) (List Nat) :=
  .ok (if metadata.terms then RecursiveJoinQuery.boundedQuery code program key limit view wanted else [])

/-- Finite family wrapping keeps exactly the available term preimages. Missing terms give no preimages. -/
theorem family_exact [DecidableEq (KeyedNaryAlignment.EngineTerm Symbol)]
    (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → RecursiveJoinGuards.Body Key Root Symbol Root)
    (accepted : ∀ key, OccurrenceGuard.isUnguarded token
      ((program key).shape token (KeyedSource.minima keys complete
        (RecursiveJoinFamily.valueProgram (RecursiveJoinGuards.lower program)))) = false)
    (key : Key) (metadata : RecursiveJoinRuntime.Metadata) (limit : Nat) (view : IntegerTermViews.View)
    (wanted : List (KeyedNaryAlignment.EngineTerm Symbol)) (rank : Nat) :
    (∃ ranks, familyRanks (Cause := Cause) code (fun key => (program key).checked) key metadata limit view wanted = .ok ranks ∧ rank ∈ ranks) ↔
      ∃ term, RecursiveRuntimeDispatch.familyOutcome (Cause := Cause) code
        (fun key => (program key).checked) key metadata limit (Int.ofNat rank) = .ok term ∧
        IntegerTermViews.project view term = wanted := by
  by_cases tracks : metadata.terms = true
  · simpa [familyRanks, tracks, RecursiveRuntimeDispatch.familyOutcome_exact] using
      RecursiveJoinQuery.public_bounded_query_exact token keys complete code program accepted key limit view wanted rank
  · simp [familyRanks, tracks, RecursiveRuntimeDispatch.familyOutcome_exact]

end MicroCFTA.BoundedRecursiveDispatch
