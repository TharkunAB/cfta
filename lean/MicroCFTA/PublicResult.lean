import MicroCFTA.Guards
import MicroCFTA.DistinctRank

/-!
# Public query results and candidate filtering

This module models observable finite/recursive/opaque dispatch and the
complete-candidate filtering worker of `validOutcomes`. Source failures retain
their original payload. Negative rank rejection precedes finite-source errors.
Unknown witness decisions remain errors. The model does not implement recipe
construction or solver IO.
-/

namespace MicroCFTA.PublicResult

open Guards

attribute [local simp] Except.map Except.bind Except.pure

/-- Query-generated errors and an unchanged underlying construction error. -/
inductive Error (Cause : Type) where
  | source (cause : Cause)
  | opaque
  | unbounded
  | negativeRank (rank : Int)
  | outOfRange (rank : Int) (count : Nat)
  | solverUnknown
  deriving DecidableEq, Repr

/-- The three observable language forms, each inspectable form retaining errors. -/
inductive Language (Cause α Recursive : Type) where
  | finite (result : Except Cause (List α))
  | recursive (result : Except Cause Recursive)
  | opaque

/-- Read finite members, preserving failure and distinguishing unavailable views. -/
def staticView : Language Cause α Recursive → Except (Error Cause) (List α)
  | .finite (.ok values) => .ok values
  | .finite (.error cause) | .recursive (.error cause) => .error (.source cause)
  | .recursive (.ok _) => .error .unbounded
  | .opaque => .error .opaque

/-- Public finite cardinality is the member count after the finite-view check. -/
def cardinality (language : Language Cause α Recursive) : Except (Error Cause) Nat := do
  let values ← staticView language
  pure values.length

/-- A successful finite count includes repeated members. -/
theorem cardinality_finite (values : List α) :
    cardinality (Language.finite (.ok values) : Language Cause α Recursive) = .ok values.length := rfl

/-- A recursive construction error is preserved instead of becoming an unbounded-query error. -/
theorem cardinality_recursive_error (cause : Cause) :
    cardinality (Language.recursive (.error cause) : Language Cause α Recursive) =
      .error (.source cause) := rfl

/-- An available recursive language has no finite cardinality. -/
theorem cardinality_recursive (value : Recursive) :
    cardinality (Language.recursive (.ok value) : Language Cause α Recursive) = .error .unbounded := rfl

/-- Opaque sampling does not provide a finite cardinality. -/
theorem cardinality_opaque :
    cardinality (.opaque : Language Cause α Recursive) = .error .opaque := rfl

/-- Select a finite member with the source's signed-rank error precedence. -/
def selectFinite (result : Except Cause (List α)) (rank : Int) : Except (Error Cause) α :=
  if rank < 0 then .error (.negativeRank rank)
  else match result with
    | .error cause => .error (.source cause)
    | .ok values =>
        match values[rank.toNat]? with
        | some value => .ok value
        | none => .error (.outOfRange rank values.length)

/-- A negative rank takes precedence even when construction already failed. -/
theorem negative_rank_precedes_failure (result : Except Cause (List α)) (rank : Int)
    (negative : rank < 0) : selectFinite result rank = .error (.negativeRank rank) := by
  simp [selectFinite, negative]

/-- Successful finite selection has exactly the list's valid indexing semantics. -/
theorem selectFinite_exact (values : List α) (rank : Int) (value : α) :
    selectFinite (Cause := Cause) (.ok values) rank = .ok value ↔
      0 ≤ rank ∧ values[rank.toNat]? = some value := by
  by_cases negative : rank < 0
  · simp [selectFinite, negative, show ¬0 ≤ rank by omega]
  · have nonnegative : 0 ≤ rank := by omega
    simp only [selectFinite, negative, ite_false, nonnegative, true_and]
    cases values[rank.toNat]? <;> simp

/-- Decide witnesses from left to right, stopping at the first non-yes result. -/
def checkWitnesses : List Verdict → Except (Error Cause) Bool
  | [] => .ok true
  | .yes :: rest => checkWitnesses rest
  | .no :: _ => .ok false
  | .unknown :: _ => .error .solverUnknown

/-- Acceptance requires every witness decision to be yes. -/
theorem checkWitnesses_true (witnesses : List Verdict) :
    checkWitnesses (Cause := Cause) witnesses = .ok true ↔
      ∀ verdict, verdict ∈ witnesses → verdict = .yes := by
  induction witnesses with
  | nil => simp [checkWitnesses]
  | cons verdict rest ih =>
      cases verdict <;> simp [checkWitnesses, ih]

/-- Successful checking keeps accepted candidates in their original member order. -/
def checkCandidates : List (α × List Verdict) → Except (Error Cause) (List α)
  | [] => .ok []
  | (value, witnesses) :: rest =>
      match checkWitnesses witnesses with
      | .error err => .error err
      | .ok accepted =>
          match checkCandidates rest with
          | .error err => .error err
          | .ok values => .ok (if accepted then value :: values else values)

/-- Every retained candidate has only established witnesses; every such candidate is retained. -/
theorem checkCandidates_exact (candidates : List (α × List Verdict)) (values : List α)
    (successful : checkCandidates (Cause := Cause) candidates = .ok values) (value : α) :
    value ∈ values ↔ ∃ witnesses, (value, witnesses) ∈ candidates ∧
      ∀ verdict, verdict ∈ witnesses → verdict = .yes := by
  induction candidates generalizing values with
  | nil =>
      have empty : values = [] := by simpa [checkCandidates] using successful.symm
      simp [empty]
  | cons entry rest ih =>
      rcases entry with ⟨head, witnesses⟩
      cases decision : checkWitnesses (Cause := Cause) witnesses with
      | error err => simp [checkCandidates, decision] at successful
      | ok accepted =>
          cases tail : checkCandidates (Cause := Cause) rest with
          | error err => simp [checkCandidates, decision, tail] at successful
          | ok remaining =>
              have restExact := ih remaining tail
              have acceptance := checkWitnesses_true (Cause := Cause) witnesses
              cases accepted with
              | false =>
                  have rejected : ¬∀ verdict, verdict ∈ witnesses → verdict = .yes := by
                    intro h
                    have contradiction := acceptance.mpr h
                    rw [decision] at contradiction
                    cases contradiction
                  have same : remaining = values := by simpa [checkCandidates, decision, tail] using successful
                  subst values
                  rw [restExact]
                  simp only [List.mem_cons, Prod.mk.injEq]
                  constructor
                  · rintro ⟨ws, present, good⟩
                    exact ⟨ws, Or.inr present, good⟩
                  · rintro ⟨ws, (⟨sameValue, sameWitnesses⟩ | present), good⟩
                    · subst ws
                      exact False.elim (rejected good)
                    · exact ⟨ws, present, good⟩
              | true =>
                  have goodHead := acceptance.mp decision
                  have same : head :: remaining = values := by simpa [checkCandidates, decision, tail] using successful
                  subst values
                  simp only [List.mem_cons, restExact, Prod.mk.injEq]
                  constructor
                  · rintro (rfl | ⟨ws, present, good⟩)
                    · exact ⟨witnesses, Or.inl ⟨rfl, rfl⟩, goodHead⟩
                    · exact ⟨ws, Or.inr present, good⟩
                  · rintro ⟨ws, (⟨sameValue, sameWitnesses⟩ | present), good⟩
                    · exact Or.inl sameValue
                    · exact Or.inr ⟨ws, present, good⟩

/-- Successful filtering preserves the order and multiplicity of all accepted candidates. -/
theorem checkCandidates_ordered (candidates : List (α × List Verdict)) (values : List α)
    (successful : checkCandidates (Cause := Cause) candidates = .ok values) :
    values = (candidates.filter (fun entry => entry.2.all (fun verdict => decide (verdict = .yes)))).map Prod.fst := by
  induction candidates generalizing values with
  | nil => simpa [checkCandidates] using successful.symm
  | cons entry rest ih =>
      rcases entry with ⟨head, witnesses⟩
      cases decision : checkWitnesses (Cause := Cause) witnesses with
      | error err => simp [checkCandidates, decision] at successful
      | ok accepted =>
          cases tail : checkCandidates (Cause := Cause) rest with
          | error err => simp [checkCandidates, decision, tail] at successful
          | ok remaining =>
              have restSame := ih remaining tail
              have allSame : witnesses.all (fun verdict => decide (verdict = .yes)) = accepted := by
                cases accepted with
                | true => simpa using (checkWitnesses_true (Cause := Cause) witnesses).mp decision
                | false =>
                    apply Bool.eq_false_iff.mpr
                    intro allYes
                    have allGood : ∀ verdict, verdict ∈ witnesses → verdict = .yes := by simpa using allYes
                    have same := (checkWitnesses_true (Cause := Cause) witnesses).mpr allGood
                    rw [decision] at same
                    cases same
              cases accepted <;> simp_all [checkCandidates]

/-- Unknown is an error when reached; an earlier rejection ends that candidate's check. -/
theorem unknown_is_not_rejection :
    checkWitnesses (Cause := Unit) [.unknown, .no] = .error .solverUnknown ∧
      checkWitnesses (Cause := Unit) [.no, .unknown] = .ok false := by
  exact ⟨rfl, rfl⟩

/-- Equal accepted values remain separate candidate members. -/
theorem duplicate_candidates_remain :
    checkCandidates (Cause := Unit) [(7, [.yes]), (7, [.yes])] = .ok [7, 7] := rfl

/-- Complete-language optimization preserves membership of each distinct term. -/
def PreservesLanguage (before after : List α) : Prop := ∀ term, term ∈ after ↔ term ∈ before

/-- Representative reduction keeps valid outputs and covers inputs by a stated relation. -/
def PreservesRepresentatives (relation : α → α → Prop) (before after : List α) : Prop :=
  (∀ term, term ∈ after → term ∈ before) ∧
    ∀ term, term ∈ before → ∃ representative, representative ∈ after ∧ relation representative term

/-- Complete-language preservation gives representative coverage under a reflexive relation. -/
theorem exact_implies_representative (relation : α → α → Prop)
    (reflexive : ∀ term, relation term term) (before after : List α)
    (exact : PreservesLanguage before after) : PreservesRepresentatives relation before after := by
  exact ⟨fun term present => (exact term).mp present,
    fun term present => ⟨term, (exact term).mpr present, reflexive term⟩⟩

/-- A valid representative can replace a distinct valid input, violating complete enumeration. -/
theorem representatives_do_not_preserve_language :
    PreservesRepresentatives (fun a b : Nat => a ≤ b) [0, 1] [0] ∧
      ¬PreservesLanguage [0, 1] [0] := by
  constructor
  · constructor
    · intro term member
      simp at member
      simp [member]
    · intro term member
      exact ⟨0, by simp, Nat.zero_le term⟩
  · intro exact
    have lost := (exact 1).mpr (by simp)
    simp at lost

end MicroCFTA.PublicResult
