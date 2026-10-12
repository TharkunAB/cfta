import MicroCFTA.RecursiveJoinRuntime
import MicroCFTA.RecursiveJoinGuards
import MicroCFTA.RecursiveJoinQuery

/-!
# Public recursion and absent-term dispatch

The public grouped recursion preserves probe errors before it constructs a
cyclic result. Inside that result, sampling-body errors precede guard and
empty-family checks. Missing term fields remain absent; they become query
errors only when a caller requests terms.
-/
namespace MicroCFTA.RecursiveRuntimeDispatch
open RecursiveJoinRuntime

/-- Query and construction errors retain the original source failure payload. -/
inductive Error (Cause : Type) where
  | source (cause : Cause)
  | unguarded | empty | cannotInspectRecursive | internalMissingTerm
  | negativeRank (rank : Int)
  | outOfRange (rank : Int) (count : Nat)
  deriving DecidableEq, Repr

/-- Only occurrence metadata is read during public recursion dispatch. -/
structure Probe (Key : Type) where
  key : Key
  used : Bool
  unguarded : Bool
  deriving DecidableEq, Repr

/-- Read a completed typed body's original flags without evaluating counts or samplers. -/
def probe (key : Key) (token : Nat) (known : GroupedProbe.Table Key)
    (body : RecursiveJoinGuards.Body Key Root Symbol Root) : Probe Key :=
  ⟨key, decide (token ∈ (OccurrenceGuard.summary (body.shape token known)).used),
    OccurrenceGuard.isUnguarded token (body.shape token known)⟩

/-- The source finite shortcut reads the original used flag through composite joins. -/
theorem probe_used (key : Key) (token : Nat) (known : GroupedProbe.Table Key)
    (body : RecursiveJoinGuards.Body Key Root Symbol Root) :
    (probe key token known body).used = KeyedGuards.used body.checked.body.value := by
  apply Bool.eq_iff_iff.mpr
  simp only [probe, decide_eq_true_eq]
  exact (RecursiveJoinGuards.used_exact body token known).symm

/-- An accepted original probe supplies the semantic family guard at that key. -/
theorem probe_guard (key : Key) (token : Nat) (known : GroupedProbe.Table Key)
    (body : RecursiveJoinGuards.Body Key Root Symbol Root)
    (accepted : (probe key token known body).unguarded = false) :
    KeyedSource.guarded body.checked.body.value known = true :=
  ((RecursiveJoinGuards.public_guard_exact body token known).mp accepted).1

/-- Output keys must have both a rebuilt body and a discovered finite minimum.
Weight flags still read every rebuilt body. Term availability remains per key. -/
def members [DecidableEq Key] (keys : List Key) (minimum : Key → Option Nat)
    (bodies : List (Key × Metadata)) (terms : Key → Bool) : List (Key × Metadata) :=
  keys.filterMap fun key =>
    if (bodies.any fun entry => decide (entry.1 = key)) && (minimum key).isSome
    then some (key, familyMetadata (bodies.map Prod.snd) (terms key)) else none

/-- The finite output filter neither adds an undiscovered key nor drops a live rebuilt key. -/
theorem member_exact [DecidableEq Key] (keys : List Key) (minimum : Key → Option Nat)
    (bodies : List (Key × Metadata)) (terms : Key → Bool) (key : Key) (metadata : Metadata) :
    (key, metadata) ∈ members keys minimum bodies terms ↔
      key ∈ keys ∧ (∃ fields, (key, fields) ∈ bodies) ∧ (minimum key).isSome = true ∧
        metadata = familyMetadata (bodies.map Prod.snd) (terms key) := by
  simp only [members, List.mem_filterMap]
  constructor
  · rintro ⟨found, present, result⟩
    split at result
    · next live =>
        cases result
        obtain ⟨available, minimum⟩ := Bool.and_eq_true_iff.mp live
        obtain ⟨⟨other, fields⟩, member, same⟩ := List.any_eq_true.mp available
        have equal : other = key := of_decide_eq_true same
        subst other
        exact ⟨present, ⟨fields, member⟩, minimum, rfl⟩
    · cases result
  · rintro ⟨present, ⟨fields, built⟩, minimum, rfl⟩
    refine ⟨key, present, ?_⟩
    have available : bodies.any (fun entry => decide (entry.1 = key)) = true :=
      List.any_eq_true.mpr ⟨(key, fields), built, by simp⟩
    simp [available, minimum]

/-- The cyclic grouped result evaluates sampling construction before validation. -/
def finish [DecidableEq Key] (keys : List Key) (minimum : Key → Option Nat)
    (bodies : Except Cause (List (Key × Metadata))) (probed : Except Cause (List (Probe Key)))
    (terms : Key → Bool) : Except (Error Cause) (List (Key × Metadata)) :=
  match bodies with
  | .error cause => .error (.source cause)
  | .ok bodies => match probed with
    | .error cause => .error (.source cause)
    | .ok probes =>
        if probes.any Probe.unguarded then .error .unguarded
        else if !(keys.any fun key => (minimum key).isSome) then .error .empty
        else .ok (members keys minimum bodies terms)

/-- The outer result distinguishes unchanged finite bodies from cyclic results. -/
inductive Result (Cause Original Key : Type) where
  | original (body : Original)
  | finiteError (cause : Cause)
  | cyclic (result : Except (Error Cause) (List (Key × Metadata)))

/-- Exact source grouped routing keeps the probe's own construction error. -/
def dispatch [DecidableEq Key] (original : Original) (keys : List Key) (minimum : Key → Option Nat)
    (bodies : Except Cause (List (Key × Metadata))) (probed : Except Cause (List (Probe Key)))
    (terms : Key → Bool) : Result Cause Original Key :=
  match probed with
  | .error cause => .finiteError cause
  | .ok probes => if !(probes.any Probe.used) then .original original
      else .cyclic (finish keys minimum bodies probed terms)

/-- Probe failure has priority over failures from an unused sampling rebuild. -/
theorem probe_error_first [DecidableEq Key] (original : Original) (keys : List Key)
    (minimum : Key → Option Nat) (bodies : Except Cause (List (Key × Metadata)))
    (cause : Cause) (terms : Key → Bool) :
    dispatch original keys minimum bodies (.error cause) terms = .finiteError cause := rfl

/-- An unused occurrence preserves the original body even when recursive validation would fail. -/
theorem unused_original [DecidableEq Key] (original : Original) (keys : List Key)
    (minimum : Key → Option Nat) (bodies : Except Cause (List (Key × Metadata)))
    (probes : List (Probe Key)) (unused : probes.any Probe.used = false) (terms : Key → Bool) :
    dispatch original keys minimum bodies (.ok probes) terms = .original original := by
  simp [dispatch, unused]

/-- Sampling construction failure precedes unguarded and empty-family errors. -/
theorem sampling_error_first [DecidableEq Key] (keys : List Key) (minimum : Key → Option Nat)
    (cause : Cause) (probed : Except Cause (List (Probe Key))) (terms : Key → Bool) :
    finish keys minimum (.error cause) probed terms = .error (.source cause) := rfl

/-- Unguarded recursion takes precedence over the lack of a finite key. -/
theorem unguarded_before_empty [DecidableEq Key] (keys : List Key) (minimum : Key → Option Nat)
    (bodies : List (Key × Metadata)) (probes : List (Probe Key))
    (unguarded : probes.any Probe.unguarded = true) (terms : Key → Bool) :
    finish (Cause := Cause) keys minimum (.ok bodies) (.ok probes) terms = .error .unguarded := by
  simp [finish, unguarded]

/-- Successful cyclic construction returns exactly the filtered source key map. -/
theorem finish_exact [DecidableEq Key] (keys : List Key) (minimum : Key → Option Nat)
    (bodies : List (Key × Metadata)) (probes : List (Probe Key)) (terms : Key → Bool)
    (output : List (Key × Metadata)) :
    finish (Cause := Cause) keys minimum (.ok bodies) (.ok probes) terms = .ok output ↔
      probes.any Probe.unguarded = false ∧ keys.any (fun key => (minimum key).isSome) = true ∧
        output = members keys minimum bodies terms := by
  cases guarded : probes.any Probe.unguarded <;> cases live : keys.any (fun key => (minimum key).isSome) <;>
    simp [finish, guarded, live, eq_comm]

/-- Public term lookup preserves signed-rank and missing-field error precedence.
The supplied selection worker is the source's size-major `classMember`. -/
def termAt (result : Except Cause (Option (Nat → Except (Error Cause) TermValue)))
    (rank : Int) : Except (Error Cause) TermValue :=
  if rank < 0 then .error (.negativeRank rank)
  else match result with
    | .error cause => .error (.source cause)
    | .ok none => .error .cannotInspectRecursive
    | .ok (some select) => select rank.toNat

/-- Negative rank is reported before construction failure or a missing term field. -/
theorem negative_first (result : Except Cause (Option (Nat → Except (Error Cause) TermValue)))
    (rank : Int) (negative : rank < 0) : termAt result rank = .error (.negativeRank rank) := by
  simp [termAt, negative]

/-- An absent term field is an inspection error, never an empty term language. -/
theorem absent_terms (rank : Int) (nonnegative : 0 ≤ rank) :
    termAt (Cause := Cause) (TermValue := TermValue) (.ok none) rank = .error .cannotInspectRecursive := by
  simp [termAt, show ¬rank < 0 by omega]

/-- Internal bounded outcome selection checks term availability before its range check. -/
def boundedOutcome (count : Nat) (terms : Option (Nat → Option TermValue))
    (rank : Int) : Except (Error Cause) TermValue :=
  match terms with
  | none => .error .cannotInspectRecursive
  | some select =>
      if rank < 0 then .error (.negativeRank rank)
      else if rank.toNat < count then
        match select rank.toNat with
        | some term => .ok term
        | none => .error .internalMissingTerm
      else .error (.outOfRange rank count)

/-- Bounded inspection still reports the missing term field for an invalid rank. -/
theorem bounded_missing_first (count : Nat) (rank : Int) :
    boundedOutcome (Cause := Cause) (TermValue := TermValue) count none rank = .error .cannotInspectRecursive := rfl

/-- With terms available, successful bounded selection is exact rank-indexed decoding. -/
theorem boundedOutcome_exact (count : Nat) (select : Nat → Option TermValue) (rank : Int) (term : TermValue) :
    boundedOutcome (Cause := Cause) count (some select) rank = .ok term ↔
      0 ≤ rank ∧ rank.toNat < count ∧ select rank.toNat = some term := by
  by_cases negative : rank < 0
  · simp [boundedOutcome, negative, show ¬0 ≤ rank by omega]
  · by_cases within : rank.toNat < count
    · cases found : select rank.toNat <;>
        simp [boundedOutcome, negative, within, found, show 0 ≤ rank by omega]
    · simp [boundedOutcome, negative, within]

/-- A missing field suppresses inverse candidates without synthesizing a term field. -/
def positions {View TermValue Candidate : Type} (terms : Option (View → List TermValue → List Candidate))
    (view : View) (wanted : List TermValue) : Option (List Candidate) :=
  terms.map (fun callback => callback view wanted)

/-- The absent callback remains absent, while a present callback retains every row and flag. -/
theorem positions_exact (callback : View → List TermValue → List Candidate) (view : View) (wanted : List TermValue) :
    positions (some callback) view wanted = some (callback view wanted) ∧
    positions (TermValue := TermValue) (Candidate := Candidate) none view wanted = none := ⟨rfl, rfl⟩

/-- Bounding first rejects an empty value index. It does not require terms to
construct a nonempty finite sampler. Inspection can fail later. -/
def bound (count : Nat) (metadata : Metadata) : Except (Error Cause) Metadata :=
  if count = 0 then .error .empty else .ok metadata

/-- Missing terms do not prevent construction of a nonempty bounded sampler. -/
theorem bound_missing_terms (count : Nat) (positive : 0 < count) (weighted massWeighted : Bool) :
    bound (Cause := Cause) count ⟨weighted, massWeighted, false⟩ = .ok ⟨weighted, massWeighted, false⟩ := by
  simp [bound, show count ≠ 0 by omega]

/-- Coherent decoder plans cannot take the internal missing-member-term error branch. -/
theorem decoder_no_internal_error (plan : Decoder.Plan TermValue) (rank : Int) :
    boundedOutcome (Cause := Cause) (Decoder.count plan) (some (Decoder.decode plan)) rank ≠
      .error .internalMissingTerm := by
  by_cases negative : rank < 0
  · simp [boundedOutcome, negative]
  · by_cases within : rank.toNat < Decoder.count plan
    · obtain ⟨term, selected⟩ := Decoder.decode_exists plan rank.toNat within
      simp [boundedOutcome, negative, within, selected]
    · simp [boundedOutcome, negative, within]

/-- The public bounded term view uses the already compiled family term plan. -/
def familyOutcome (code : Key → Nat)
    (program : Key → RecursiveJoinBodyFields.CheckedBody Key Root Symbol Root)
    (key : Key) (metadata : Metadata) (limit : Nat) (rank : Int) :
    Except (Error Cause) (KeyedNaryAlignment.EngineTerm Symbol) :=
  let plan := (GroupedRecord.bounded (fun size => KeyedSource.family
    (RecursiveJoinFamily.termProgram code (RecursiveJoinInverse.lower program)) size key) limit).plan
  boundedOutcome (Decoder.count plan)
    (if metadata.terms then some (Decoder.decode plan) else none) rank

/-- Runtime absence and successful bounded-family decoding have separate exact cases. -/
theorem familyOutcome_exact (code : Key → Nat)
    (program : Key → RecursiveJoinBodyFields.CheckedBody Key Root Symbol Root)
    (key : Key) (metadata : Metadata) (limit : Nat) (rank : Int) (term : KeyedNaryAlignment.EngineTerm Symbol) :
    familyOutcome (Cause := Cause) code program key metadata limit rank = .ok term ↔
      metadata.terms = true ∧ 0 ≤ rank ∧
      RecursiveJoinQuery.boundedDecode code program key limit rank.toNat = some term := by
  unfold familyOutcome
  by_cases tracks : metadata.terms = true
  · simp only [tracks, ↓reduceIte, boundedOutcome_exact, true_and]
    constructor
    · intro found
      exact ⟨found.1, found.2.2⟩
    · rintro ⟨nonnegative, selected⟩
      refine ⟨nonnegative, ?_, selected⟩
      by_cases within : rank.toNat < Decoder.count (GroupedRecord.bounded (fun size => KeyedSource.family
          (RecursiveJoinFamily.termProgram code (RecursiveJoinInverse.lower program)) size key) limit).plan
      · exact within
      · have absent := (Decoder.decode_none_iff (GroupedRecord.bounded (fun size => KeyedSource.family
            (RecursiveJoinFamily.termProgram code (RecursiveJoinInverse.lower program)) size key) limit).plan rank.toNat).mpr (by omega)
        change RecursiveJoinQuery.boundedDecode code program key limit rank.toNat = none at absent
        rw [selected] at absent
        cases absent
  · simp [tracks, boundedOutcome]

/-- Present runtime term fields expose the existing complete bounded inverse;
absent fields return the source inspection error. -/
def familyRanks [DecidableEq (KeyedNaryAlignment.EngineTerm Symbol)] (code : Key → Nat)
    (program : Key → RecursiveJoinBodyFields.CheckedBody Key Root Symbol Root)
    (key : Key) (metadata : Metadata) (limit : Nat) (view : IntegerTermViews.View)
    (wanted : List (KeyedNaryAlignment.EngineTerm Symbol)) : Except (Error Cause) (List Nat) :=
  if metadata.terms then .ok (RecursiveJoinQuery.boundedQuery code program key limit view wanted)
  else .error .cannotInspectRecursive

/-- Successful public occurrence checks and runtime term availability give
every and only bounded term preimage, with no assumed global inverse law. -/
theorem familyRanks_exact [DecidableEq (KeyedNaryAlignment.EngineTerm Symbol)]
    (token : Nat) (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → RecursiveJoinGuards.Body Key Root Symbol Root)
    (accepted : ∀ key, OccurrenceGuard.isUnguarded token
      ((program key).shape token (KeyedSource.minima keys complete
        (RecursiveJoinFamily.valueProgram (RecursiveJoinGuards.lower program)))) = false)
    (key : Key) (metadata : Metadata) (limit : Nat) (view : IntegerTermViews.View)
    (wanted : List (KeyedNaryAlignment.EngineTerm Symbol)) (rank : Nat) :
    (∃ ranks, familyRanks (Cause := Cause) code (fun key => (program key).checked) key metadata limit view wanted = .ok ranks ∧ rank ∈ ranks) ↔
      metadata.terms = true ∧ ∃ term,
        familyOutcome (Cause := Cause) code (fun key => (program key).checked) key metadata limit (Int.ofNat rank) = .ok term ∧
        IntegerTermViews.project view term = wanted := by
  by_cases tracks : metadata.terms = true
  · simpa [familyRanks, tracks, familyOutcome_exact] using
      (RecursiveJoinQuery.public_bounded_query_exact token keys complete code program accepted key limit view wanted rank)
  · simp [familyRanks, tracks]

end MicroCFTA.RecursiveRuntimeDispatch
