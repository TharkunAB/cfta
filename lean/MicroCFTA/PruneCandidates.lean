import MicroCFTA.PruneSchedule

/-!
# Exact candidate pruning with Unknown fallback

The source either completes its candidate pass, restores the original guarded
edge after an ambiguous Unknown, or returns an error. The completed and
restored cases both preserve the full concrete term language.
-/
namespace MicroCFTA.PruneCandidates
open Language Guards PruneSchedule Observation ObservationGraph
variable {Edge Term : Type}

/-- A returned list denotes the union of its alternatives. -/
def Denotes (meaning : Edge → Term → Prop) (edges : List Edge) (term : Term) : Prop :=
  ∃ edge ∈ edges, meaning edge term

/-- Every successful check either restores the complete original or finishes every candidate. -/
theorem check_success_cases (original : Edge) (retained : List Edge) (candidates : List (PruneSchedule.Candidate Edge))
    (result : List Edge) (success : check original retained candidates = .ok result) :
    result = [original] ∨
      result = retained ++ decided candidates ∧ ∀ candidate ∈ candidates, candidate.verdict ≠ .unknown := by
  induction candidates generalizing retained with
  | nil => exact .inr ⟨by simpa [check, decided] using success.symm, by simp⟩
  | cons candidate rest ih =>
      cases verdict : candidate.verdict with
      | unknown =>
          cases ambiguous : candidate.ambiguous with
          | false => simp [check, verdict, ambiguous] at success
          | true => exact .inl (by simpa [check, verdict, ambiguous] using success.symm)
      | yes =>
          have tail := ih (retained ++ [candidate.edge]) (by simpa [check, verdict] using success)
          rcases tail with restored | ⟨finished, complete⟩
          · exact .inl restored
          · exact .inr ⟨by simpa [decided, verdict, List.append_assoc] using finished, by
              intro item member; rcases List.mem_cons.mp member with rfl | later
              · simp [verdict]
              · exact complete item later⟩
      | no =>
          have tail := ih retained (by simpa [check, verdict] using success)
          rcases tail with restored | ⟨finished, complete⟩
          · exact .inl restored
          · exact .inr ⟨by simpa [decided, verdict] using finished, by
              intro item member; rcases List.mem_cons.mp member with rfl | later
              · simp [verdict]
              · exact complete item later⟩

/-- The decided list contains exactly the candidate edges proved Yes. -/
theorem decided_member (candidates : List (PruneSchedule.Candidate Edge)) (edge : Edge) :
    edge ∈ decided candidates ↔ ∃ candidate ∈ candidates, candidate.verdict = .yes ∧ candidate.edge = edge := by
  induction candidates with
  | nil => simp [decided]
  | cons candidate rest ih =>
      cases verdict : candidate.verdict <;> simp [decided, verdict, ih, eq_comm]

/-- Decided candidates preserve their partition when Yes discharges and No refutes each cell. -/
theorem decided_exact (meaning : Edge → Term → Prop) (cell : PruneSchedule.Candidate Edge → Term → Prop)
    (candidates : List (PruneSchedule.Candidate Edge))
    (complete : ∀ candidate ∈ candidates, candidate.verdict ≠ .unknown)
    (yes : ∀ candidate ∈ candidates, candidate.verdict = .yes → ∀ term, meaning candidate.edge term ↔ cell candidate term)
    (no : ∀ candidate ∈ candidates, candidate.verdict = .no → ∀ term, ¬ cell candidate term) (term : Term) :
    Denotes meaning (decided candidates) term ↔ ∃ candidate ∈ candidates, cell candidate term := by
  constructor
  · rintro ⟨edge, member, accepted⟩
    obtain ⟨candidate, present, proved, rfl⟩ := (decided_member candidates edge).mp member
    exact ⟨candidate, present, (yes candidate present proved term).mp accepted⟩
  · rintro ⟨candidate, present, accepted⟩
    cases verdict : candidate.verdict with
    | unknown => exact False.elim (complete candidate present verdict)
    | no => exact False.elim (no candidate present verdict term accepted)
    | yes => exact ⟨candidate.edge, (decided_member candidates _).mpr ⟨candidate, present, verdict, rfl⟩,
        (yes candidate present verdict term).mpr accepted⟩

/-- The actual check loop preserves every concrete term on every successful return, including Unknown fallback. -/
theorem check_exact (meaning : Edge → Term → Prop) (cell : PruneSchedule.Candidate Edge → Term → Prop)
    (original : Edge) (candidates : List (PruneSchedule.Candidate Edge))
    (cover : ∀ term, (∃ candidate ∈ candidates, cell candidate term) ↔ meaning original term)
    (yes : ∀ candidate ∈ candidates, candidate.verdict = .yes → ∀ term, meaning candidate.edge term ↔ cell candidate term)
    (no : ∀ candidate ∈ candidates, candidate.verdict = .no → ∀ term, ¬ cell candidate term)
    (result : List Edge) (success : check original [] candidates = .ok result) (term : Term) :
    Denotes meaning result term ↔ meaning original term := by
  rcases check_success_cases original [] candidates result success with restored | ⟨finished, complete⟩
  · simp [restored, Denotes]
  · simpa [finished] using (decided_exact meaning cell candidates complete yes no term).trans (cover term)

/-- Source candidate assembly uses the actual finite graph specialization and its stored-view query. -/
def candidates [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (ambiguous : Variant State Symbol Refinement → Bool) :
    List (PruneSchedule.Candidate (ObservationGraph.Node State (Label Symbol Refinement))) :=
  (specialize automaton (planBudget (guardPlan guard)) (guardPlan guard) state).map
    (fun variant => ⟨variant.node, safeVerdict (ambiguous variant) (variantVerdict queries guard variant), ambiguous variant⟩)

/-- Execute the source check on the concrete specialized graph, retaining the full guarded root on fallback. -/
def prune [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (ambiguous : Variant State Symbol Refinement → Bool) :
    Except PruneSchedule.Error (List (ObservationGraph.Node State (Label Symbol Refinement))) :=
  check (guardedRoot automaton state (fun term => decide (verdict queries guard term = .yes))) []
    (candidates automaton queries guard state ambiguous)

/-- Concrete specialization and the complete source fallback loop preserve the full confirmed term language. -/
theorem prune_exact [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (ambiguous : Variant State Symbol Refinement → Bool)
    (result : List (ObservationGraph.Node State (Label Symbol Refinement)))
    (success : prune automaton queries guard state ambiguous = .ok result) (term : Language.Term (Label Symbol Refinement)) :
    Denotes (AcceptsNode automaton) result term ↔
      AcceptsNode automaton (guardedRoot automaton state (fun term => decide (verdict queries guard term = .yes))) term := by
  apply check_exact (AcceptsNode automaton)
    (fun candidate term => AcceptsNode automaton candidate.edge term ∧ verdict queries guard term = .yes)
    _ (candidates automaton queries guard state ambiguous) _ _ _ result success term
  · intro term
    rw [guardedRoot_accepts_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨candidate, member, accepted, proved⟩
      obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
      exact ⟨(specialize_cover automaton _ _ state term).mp ⟨variant, present, accepted⟩, proved⟩
    · rintro ⟨accepted, proved⟩
      obtain ⟨variant, member, run⟩ := (specialize_cover automaton _ _ state term).mpr accepted
      exact ⟨_, List.mem_map.mpr ⟨variant, member, rfl⟩, run, proved⟩
  · intro candidate member proved term
    obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
    have proved := (safeVerdict_yes _ _).mp proved |>.2
    constructor
    · intro accepted
      exact ⟨accepted, (variantVerdict_correct automaton queries guard state variant present term accepted).symm.trans proved⟩
    · exact And.left
  · intro candidate member disproved term ⟨accepted, proved⟩
    obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
    have disproved := (safeVerdict_no _ _).mp disproved |>.2
    have exactQuery := variantVerdict_correct automaton queries guard state variant present term accepted
    have impossible := disproved.symm.trans (exactQuery.trans proved)
    cases impossible


/-- Execute pruning with the declared semantic root guard, independent of solver completeness. -/
def pruneWithGuard [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (test : Language.Term (Label Symbol Refinement) → Bool)
    (ambiguous : Variant State Symbol Refinement → Bool) :
    Except PruneSchedule.Error (List (ObservationGraph.Node State (Label Symbol Refinement))) :=
  check (guardedRoot automaton state test) [] (candidates automaton queries guard state ambiguous)

/-- Sound sparse decisions preserve the declared semantic language on every successful source return. -/
theorem prune_semantic_exact [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (test : Language.Term (Label Symbol Refinement) → Bool)
    (sound : ∀ term, Guards.Supports (verdict queries guard term) (test term = true))
    (ambiguous : Variant State Symbol Refinement → Bool)
    (result : List (ObservationGraph.Node State (Label Symbol Refinement)))
    (success : pruneWithGuard automaton queries guard state test ambiguous = .ok result)
    (term : Language.Term (Label Symbol Refinement)) :
    Denotes (AcceptsNode automaton) result term ↔ AcceptsNode automaton (guardedRoot automaton state test) term := by
  apply check_exact (AcceptsNode automaton)
    (fun candidate term => AcceptsNode automaton candidate.edge term ∧ test term = true)
    _ (candidates automaton queries guard state ambiguous) _ _ _ result success term
  · intro term
    rw [guardedRoot_accepts_iff]
    constructor
    · rintro ⟨candidate, member, accepted, proved⟩
      obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
      exact ⟨(specialize_cover automaton _ _ state term).mp ⟨variant, present, accepted⟩, proved⟩
    · rintro ⟨accepted, proved⟩
      obtain ⟨variant, member, run⟩ := (specialize_cover automaton _ _ state term).mpr accepted
      exact ⟨_, List.mem_map.mpr ⟨variant, member, rfl⟩, run, proved⟩
  · intro candidate member proved term
    obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
    have proved := (safeVerdict_yes _ _).mp proved |>.2
    constructor
    · intro accepted
      have decision : verdict queries guard term = .yes :=
        (variantVerdict_correct automaton queries guard state variant present term accepted).symm.trans proved
      exact ⟨accepted, by simpa [decision, Guards.Supports] using sound term⟩
    · exact And.left
  · intro candidate member disproved term ⟨accepted, proved⟩
    obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
    have disproved := (safeVerdict_no _ _).mp disproved |>.2
    have decision : verdict queries guard term = .no :=
      (variantVerdict_correct automaton queries guard state variant present term accepted).symm.trans disproved
    have falseGuard : test term ≠ true := by simpa [decision, Guards.Supports] using sound term
    exact falseGuard proved


/-- Semantic dispatch preserves the edge language in its Top, recursive-retention, and checked cases. -/
theorem semantic_exact (meaning : Edge → Term → Prop) (cell : PruneSchedule.Candidate Edge → Term → Prop)
    (original discharged : Edge) (semanticTop hasFree readsRecursion : Bool)
    (candidates : List (PruneSchedule.Candidate Edge))
    (top : semanticTop = true → ∀ term, meaning discharged term ↔ meaning original term)
    (cover : ∀ term, (∃ candidate ∈ candidates, cell candidate term) ↔ meaning original term)
    (yes : ∀ candidate ∈ candidates, candidate.verdict = .yes → ∀ term, meaning candidate.edge term ↔ cell candidate term)
    (no : ∀ candidate ∈ candidates, candidate.verdict = .no → ∀ term, ¬ cell candidate term)
    (result : List Edge) (success : semantic original discharged semanticTop hasFree readsRecursion candidates = .ok result)
    (term : Term) : Denotes meaning result term ↔ meaning original term := by
  cases isTop : semanticTop with
  | true =>
      have resultEq : result = [discharged] := by simpa [semantic, isTop] using success.symm
      simpa [resultEq, Denotes] using top isTop term
  | false =>
      cases recursive : hasFree && readsRecursion with
      | true =>
          have resultEq : result = [original] := by simpa [semantic, isTop, recursive] using success.symm
          simp [resultEq, Denotes]
      | false =>
          exact check_exact meaning cell original candidates cover yes no result
            (by simpa [semantic, isTop, recursive] using success) term

end MicroCFTA.PruneCandidates
