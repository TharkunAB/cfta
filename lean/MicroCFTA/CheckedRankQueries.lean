import MicroCFTA.PublicResult

/-!
# Public rank queries and checked-symbol flags

The source accepts a certified candidate directly. It decodes and compares
an uncertified candidate. Errors from obtaining candidates remain errors.
The first retained candidate is the public least rank when callbacks are ordered.
-/
namespace MicroCFTA.CheckedRankQueries

/-- A source candidate contains its signed rank and the checked-symbol flag. -/
structure Candidate where
  rank : Int
  checked : Bool
  deriving DecidableEq, Repr

/-- Query failures retain a construction cause and distinguish unavailable views. -/
inductive Error (Cause : Type) where
  | source (cause : Cause)
  | opaque
  | recursiveTermsUnavailable
  | termNotInLanguage
  deriving DecidableEq, Repr

/-- Finite and recursive candidates use their respective source callbacks. -/
inductive Source (Cause Term : Type) where
  | finite (result : Except Cause (Term → List Candidate))
  | recursive (result : Except Cause (Option (Term → List Candidate)))
  | opaque

/-- Read the actual candidate callback with source error precedence. -/
def candidates (source : Source Cause Term) (term : Term) : Except (Error Cause) (List Candidate) :=
  match source with
  | .finite (.ok callback) | .recursive (.ok (some callback)) => .ok (callback term)
  | .finite (.error cause) | .recursive (.error cause) => .error (.source cause)
  | .recursive (.ok none) => .error .recursiveTermsUnavailable
  | .opaque => .error .opaque

/-- Execute the source's checked-flag short circuit and fallback comparison. -/
def keep [DecidableEq Term]
    (decode : Int → Except Failure Term) (term : Term) (candidate : Candidate) : Bool :=
  candidate.checked || decide ((decode candidate.rank).toOption = some term)

/-- The exact finite list filter performed after candidate retrieval. -/
def retained [DecidableEq Term]
    (decode : Int → Except Failure Term) (term : Term) (rows : List Candidate) : List Int :=
  (rows.filter (keep decode term)).map Candidate.rank

/-- Public ranks preserve candidate errors and otherwise run the checked filter. -/
def ranksOf [DecidableEq Term]
    (decode : Int → Except Failure Term) (source : Source Cause Term) (term : Term) :
    Except (Error Cause) (List Int) :=
  (candidates source term).map (retained decode term)

/-- Public inverse ranking returns the first retained rank or the membership error. -/
def rankOf [DecidableEq Term]
    (decode : Int → Except Failure Term) (source : Source Cause Term) (term : Term) :
    Except (Error Cause) Int := do
  let ranks ← ranksOf decode source term
  match ranks with
  | [] => .error .termNotInLanguage
  | first :: _ => .ok first

/-- A true checked flag requires successful exact term replay at that rank. -/
def CheckedSound (decode : Int → Except Failure Term) (term : Term) (rows : List Candidate) : Prop :=
  ∀ candidate ∈ rows, candidate.checked = true → decode candidate.rank = .ok term

/-- Every actual inverse rank is offered by the underlying callback. -/
def Complete (decode : Int → Except Failure Term) (term : Term) (rows : List Candidate) : Prop :=
  ∀ rank, decode rank = .ok term → ∃ candidate ∈ rows, candidate.rank = rank

/-- The fallback check is exact; only a true flag relies on its producer certificate. -/
theorem keep_exact [DecidableEq Term]
    (decode : Int → Except Failure Term) (term : Term) (rows : List Candidate)
    (sound : CheckedSound decode term rows) (candidate : Candidate) (present : candidate ∈ rows) :
    keep decode term candidate = true ↔ decode candidate.rank = .ok term := by
  have replay : (decode candidate.rank).toOption = some term ↔ decode candidate.rank = .ok term := by
    cases decode candidate.rank <;> simp [Except.toOption]
  simp only [keep, Bool.or_eq_true, decide_eq_true_eq, replay]
  exact ⟨fun accepted => accepted.elim (sound candidate present) id, Or.inr⟩

/-- The optimized filter keeps exactly every rank that replays the requested term. -/
theorem retained_exact [DecidableEq Term]
    (decode : Int → Except Failure Term) (term : Term) (rows : List Candidate)
    (sound : CheckedSound decode term rows) (complete : Complete decode term rows) (rank : Int) :
    rank ∈ retained decode term rows ↔ decode rank = .ok term := by
  simp only [retained, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨candidate, ⟨present, kept⟩, rfl⟩
    exact (keep_exact decode term rows sound candidate present).mp kept
  · intro selected
    obtain ⟨candidate, present, same⟩ := complete rank selected
    exact ⟨candidate, ⟨present, (keep_exact decode term rows sound candidate present).mpr (same ▸ selected)⟩, same⟩

/-- Filtering retains source candidate order and cannot duplicate ranks. -/
theorem retained_sublist [DecidableEq Term]
    (decode : Int → Except Failure Term) (term : Term) (rows : List Candidate) :
    (retained decode term rows).Sublist (rows.map Candidate.rank) :=
  List.Sublist.map Candidate.rank List.filter_sublist

/-- The source ascending callback contract implies ascending public results. -/
theorem retained_ordered [DecidableEq Term]
    (decode : Int → Except Failure Term) (term : Term) (rows : List Candidate)
    (ordered : (rows.map Candidate.rank).Pairwise (· ≤ ·)) :
    (retained decode term rows).Pairwise (· ≤ ·) :=
  ordered.sublist (retained_sublist decode term rows)

/-- Successful public inversion is exact and returns the least matching signed rank. -/
theorem rankOf_exact [DecidableEq Term]
    (decode : Int → Except Failure Term) (source : Source Cause Term) (term : Term)
    (rows : List Candidate) (read : candidates source term = .ok rows)
    (sound : CheckedSound decode term rows) (complete : Complete decode term rows)
    (ordered : (rows.map Candidate.rank).Pairwise (· ≤ ·)) (rank : Int) :
    rankOf decode source term = .ok rank ↔
      decode rank = .ok term ∧ ∀ other, decode other = .ok term → rank ≤ other := by
  have exact := retained_exact decode term rows sound complete
  have order := retained_ordered decode term rows ordered
  simp only [rankOf, ranksOf, read, Except.map, Bind.bind, Except.bind]
  cases ranks : retained decode term rows with
  | nil =>
      simp only [ranks, List.not_mem_nil] at exact
      constructor
      · intro impossible; cases impossible
      · rintro ⟨selected, _⟩
        exact False.elim ((exact rank).mpr selected)
  | cons first rest =>
      simp only [ranks, List.pairwise_cons] at order
      have firstSelected := (exact first).mp (by simp [ranks])
      have firstLeast : ∀ other, decode other = .ok term → first ≤ other := by
        intro other selected
        have member := (exact other).mpr selected
        rw [ranks, List.mem_cons] at member
        exact member.elim (fun same => by omega) (order.1 other)
      constructor
      · intro equal
        have same : first = rank := Except.ok.inj equal
        exact same ▸ ⟨firstSelected, firstLeast⟩
      · rintro ⟨selected, least⟩
        have same : first = rank := by have := firstLeast rank selected; have := least first firstSelected; omega
        exact congrArg Except.ok same

/-- An empty successful candidate result means no term match when discovery is complete. -/
theorem rankOf_rejected [DecidableEq Term]
    (decode : Int → Except Failure Term) (source : Source Cause Term) (term : Term)
    (rows : List Candidate) (read : candidates source term = .ok rows)
    (sound : CheckedSound decode term rows) (complete : Complete decode term rows) :
    rankOf decode source term = .error .termNotInLanguage ↔ ∀ rank, decode rank ≠ .ok term := by
  have exact := retained_exact decode term rows sound complete
  simp only [rankOf, ranksOf, read, Except.map, Bind.bind, Except.bind]
  cases ranks : retained decode term rows with
  | nil =>
      constructor
      · intro _ rank selected
        have member := (exact rank).mpr selected
        simp [ranks] at member
      · intro _; rfl
  | cons first rest =>
      constructor
      · intro impossible; cases impossible
      · intro absent
        exact False.elim (absent first ((exact first).mp (by simp [ranks])))

/-- Construction failures are not converted into term rejection. -/
theorem source_error [DecidableEq Term]
    (decode : Int → Except Failure Term) (cause : Cause) (term : Term) :
    rankOf decode (.finite (.error cause)) term = .error (.source cause) ∧
      rankOf decode (.recursive (.error cause)) term = .error (.source cause) := by
  constructor <;> rfl

/-- A false certification flag forces replay; a failing replay cannot be retained. -/
theorem unchecked_error [DecidableEq Term]
    (decode : Int → Except Failure Term) (term : Term) (rank : Int) (failure : Failure)
    (failed : decode rank = .error failure) : keep decode term ⟨rank, false⟩ = false := by
  simp [keep, failed, Except.toOption]

/-- A malformed true flag can bypass replay. The producer contract is necessary. -/
theorem unchecked_contract_necessary :
    retained (fun _ : Int => (Except.ok 0 : Except Unit Nat)) 1 [⟨-1, true⟩] = [-1] := rfl

end MicroCFTA.CheckedRankQueries
