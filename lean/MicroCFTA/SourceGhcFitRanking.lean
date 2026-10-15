import MicroCFTA.SourceListSort
import MicroCFTA.SourceGhcFitNormalForms

/-!
# Finite fit ranking and the score-vector boundary

This module follows Decision.ranked and GHC.Rank.rankedFits at main 4101746a.
The installed source sorter preserves occurrences for every comparator.
The fit pool is the signed splitAt prefix after the comesLast partition.
A completed answer records success, failure, or timeout. A small pool asks
no question. The recorded question is the intended pool, not an IO receipt.
The external request and timeout IO remain separate adapters.

Complete score vectors preserve all fits. Short vectors lose the unscored
pool suffix through source zip. No comparator law is needed for these facts.
Descending order, tie stability, and Double comparison laws are not proved here.
-/
namespace MicroCFTA.SourceGhcFitRanking
variable {Fit Score Message : Type}

/-- Decision.ranked zips scores with fits, then sorts by the descending score comparison. -/
def ranked (compare : Score → Score → Ordering) (fits : List Fit) (scores : List Score) : List (Fit × Score) :=
  SourceListSort.sortBy (fun first second => compare first.2 second.2) (fits.zip scores)

/-- Source zip retains exactly the prefix that has a score. -/
theorem zip_fits (fits : List Fit) (scores : List Score) :
    (fits.zip scores).map Prod.fst = fits.take scores.length := by
  induction fits generalizing scores with
  | nil => simp
  | cons fit fits ih =>
      cases scores with
      | nil => simp
      | cons score scores => simp [ih]

/-- The ranked output is a permutation of exactly the scored input prefix. -/
theorem ranked_prefix (compare : Score → Score → Ordering) (fits : List Fit) (scores : List Score) :
    ((ranked compare fits scores).map Prod.fst).Perm (fits.take scores.length) := by
  have actual := (SourceListSort.sortBy_perm
    (fun first second : Fit × Score => compare first.2 second.2) (fits.zip scores)).map Prod.fst
  simpa only [ranked, zip_fits] using actual

/-- A score for every fit makes the source ranking a permutation of the complete input. -/
theorem ranked_perm (compare : Score → Score → Ordering) (fits : List Fit) (scores : List Score)
    (complete : fits.length ≤ scores.length) : ((ranked compare fits scores).map Prod.fst).Perm fits := by
  simpa only [List.take_of_length_le complete] using ranked_prefix compare fits scores

/-- Malformed score vectors cannot introduce a new fit. -/
theorem ranked_member (compare : Score → Score → Ordering) (fits : List Fit) (scores : List Score)
    (fit : Fit) (member : fit ∈ (ranked compare fits scores).map Prod.fst) : fit ∈ fits :=
  List.mem_of_mem_take ((ranked_prefix compare fits scores).mem_iff.mp member)

/-- Source length is the smaller of the number of fits and returned scores. -/
theorem ranked_length (compare : Score → Score → Ordering) (fits : List Fit) (scores : List Score) :
    ((ranked compare fits scores).map Prod.fst).length = min scores.length fits.length := by
  rw [(ranked_prefix compare fits scores).length_eq, List.length_take]

/-- The three completed source timeout branches. -/
inductive Answer (Score Message : Type) where
  | success (scores : List Score)
  | failure (message : Message)
  | timeout

/-- A finite answer retains the intended question pool and optional source diagnostic. -/
structure Result (Fit Message : Type) where
  fits : List Fit
  problem : Option Message
  question : Option (List Fit)

/-- Source partition puts every comesLast fit after the using fits. -/
def usingFits (comesLast : Fit → Bool) (fits : List Fit) : List Fit :=
  fits.filter fun fit => !(comesLast fit)

/-- The delayed fits retain their original order. -/
def laterFits (comesLast : Fit → Bool) (fits : List Fit) : List Fit :=
  fits.filter comesLast

/-- The source partition preserves every occurrence, including failure and timeout branches. -/
theorem partition_perm (comesLast : Fit → Bool) (fits : List Fit) :
    (usingFits comesLast fits ++ laterFits comesLast fits).Perm fits := by
  simpa [usingFits, laterFits] using List.filter_append_perm (fun fit => !(comesLast fit)) fits

/-- Execute the finite branch logic after the external timeout returns. -/
def rankedFits (compare : Score → Score → Ordering) (comesLast : Fit → Bool)
    (pool : Int) (timeoutMessage : Message) (fits : List Fit) (answer : Answer Score Message) : Result Fit Message :=
  let eligible := usingFits comesLast fits
  let later := laterFits comesLast fits
  let pooled := eligible.take pool.toNat
  let rest := eligible.drop pool.toNat
  if pooled.length < 2 then ⟨eligible ++ later, none, none⟩
  else match answer with
    | .success scores => ⟨(ranked compare pooled scores).map Prod.fst ++ rest ++ later, none, some pooled⟩
    | .failure message => ⟨eligible ++ later, some message, some pooled⟩
    | .timeout => ⟨eligible ++ later, some timeoutMessage, some pooled⟩

/-- Pools below two fits bypass the model and diagnostics. -/
theorem small_pool (compare : Score → Score → Ordering) (comesLast : Fit → Bool)
    (pool : Int) (timeoutMessage : Message) (fits : List Fit) (answer : Answer Score Message)
    (small : ((usingFits comesLast fits).take pool.toNat).length < 2) :
    rankedFits compare comesLast pool timeoutMessage fits answer =
      ⟨usingFits comesLast fits ++ laterFits comesLast fits, none, none⟩ := by
  simp only [rankedFits, small, ↓reduceIte]

/-- Nonpositive signed pools have the source splitAt-zero behavior and ask no question. -/
theorem nonpositive_pool (compare : Score → Score → Ordering) (comesLast : Fit → Bool)
    (pool : Int) (timeoutMessage : Message) (fits : List Fit) (answer : Answer Score Message)
    (nonpositive : pool ≤ 0) :
    rankedFits compare comesLast pool timeoutMessage fits answer =
      ⟨usingFits comesLast fits ++ laterFits comesLast fits, none, none⟩ := by
  apply small_pool
  have zero : pool.toNat = 0 := by omega
  simp [zero]

/-- Successful complete scores preserve every fit; failures and timeouts need no score contract. -/
theorem result_perm (compare : Score → Score → Ordering) (comesLast : Fit → Bool)
    (pool : Int) (timeoutMessage : Message) (fits : List Fit) (answer : Answer Score Message)
    (complete : ∀ scores, answer = .success scores →
      ((usingFits comesLast fits).take pool.toNat).length ≤ scores.length) :
    (rankedFits compare comesLast pool timeoutMessage fits answer).fits.Perm fits := by
  by_cases small : ((usingFits comesLast fits).take pool.toNat).length < 2
  · rw [small_pool compare comesLast pool timeoutMessage fits answer small]
    exact partition_perm comesLast fits
  · cases answer with
    | success scores =>
        simp only [rankedFits, small, ↓reduceIte]
        have scoredPerm := ranked_perm compare ((usingFits comesLast fits).take pool.toNat) scores (complete scores rfl)
        have all := (scoredPerm.append_right ((usingFits comesLast fits).drop pool.toNat)).append_right (laterFits comesLast fits)
        rw [List.take_append_drop] at all
        exact all.trans (partition_perm comesLast fits)
    | failure message => simpa only [rankedFits, small, ↓reduceIte] using partition_perm comesLast fits
    | timeout => simpa only [rankedFits, small, ↓reduceIte] using partition_perm comesLast fits

/-- Every branch returns only original fits, even with incomplete scores. -/
theorem result_member (compare : Score → Score → Ordering) (comesLast : Fit → Bool)
    (pool : Int) (timeoutMessage : Message) (fits : List Fit) (answer : Answer Score Message)
    (fit : Fit) (member : fit ∈ (rankedFits compare comesLast pool timeoutMessage fits answer).fits) : fit ∈ fits := by
  by_cases small : ((usingFits comesLast fits).take pool.toNat).length < 2
  · rw [small_pool compare comesLast pool timeoutMessage fits answer small] at member
    exact (partition_perm comesLast fits).mem_iff.mp member
  · cases answer with
    | success scores =>
        simp only [rankedFits, small, ↓reduceIte, List.mem_append] at member
        rcases member with (member | member) | member
        · exact (List.mem_filter.mp (List.mem_of_mem_take (ranked_member compare _ scores fit member))).1
        · exact (List.mem_filter.mp (List.mem_of_mem_drop member)).1
        · exact (List.mem_filter.mp member).1
    | failure message =>
        simp only [rankedFits, small, ↓reduceIte] at member
        exact (partition_perm comesLast fits).mem_iff.mp member
    | timeout =>
        simp only [rankedFits, small, ↓reduceIte] at member
        exact (partition_perm comesLast fits).mem_iff.mp member

/-- An intended question uses exactly the eligible prefix, with at least two fits. -/
theorem question_pool (compare : Score → Score → Ordering) (comesLast : Fit → Bool)
    (pool : Int) (timeoutMessage : Message) (fits : List Fit) (answer : Answer Score Message) (asked : List Fit)
    (question : (rankedFits compare comesLast pool timeoutMessage fits answer).question = some asked) :
    asked = (usingFits comesLast fits).take pool.toNat ∧ 2 ≤ asked.length := by
  by_cases small : ((usingFits comesLast fits).take pool.toNat).length < 2
  · rw [small_pool compare comesLast pool timeoutMessage fits answer small] at question
    cases question
  · cases answer <;> simp only [rankedFits, small, ↓reduceIte, Option.some.injEq] at question <;>
      subst asked <;> exact ⟨rfl, by omega⟩

/-- A zero-length successful answer drops a nonempty pool through zip. -/
example : (rankedFits (fun _ _ : Nat => Ordering.eq) (fun _ : Nat => false)
    2 "timeout" [10, 20, 30] (.success [])).fits = [30] := by decide

/-- Failure retains the source partition order, which can differ from the original interleaving. -/
example : (rankedFits (fun _ _ : Nat => Ordering.eq) (· == 99)
    2 "timeout" [10, 99, 20, 30] (.failure "failed")).fits = [10, 20, 30, 99] := by decide

end MicroCFTA.SourceGhcFitRanking
