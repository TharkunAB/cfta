import MicroCFTA.FTAValidation

/-!
# Redundant alternative removal

The source compares alternatives within one symbol group. It removes an
alternative when its intersection equals the other alternative. A dominating
alternative moves to the front of the next recursive comparison.
-/
namespace MicroCFTA.RedundantEdges

/-- The exact source worker, including promotion of a dominating alternative. -/
def ruleOut [DecidableEq Edge] (meet : Edge → Edge → Edge) (edge : Edge) :
    List Edge → Option Edge × List Edge
  | [] => (none, [])
  | other :: rest =>
    let common := meet edge other
    if common = other then ruleOut meet edge rest
    else if common = edge then (some other, rest)
    else let result := ruleOut meet edge rest; (result.1, other :: result.2)

/-- The worker returns no more candidates than its input tail contains. -/
theorem ruleOut_length [DecidableEq Edge] (meet : Edge → Edge → Edge) (edge : Edge) (edges : List Edge) :
    (ruleOut meet edge edges).1.toList.length + (ruleOut meet edge edges).2.length ≤ edges.length := by
  induction edges with
  | nil => simp [ruleOut]
  | cons other rest ih =>
    simp only [ruleOut]
    split
    · simpa using Nat.le_succ_of_le ih
    · split
      · simp [Nat.add_comm]
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.succ_le_succ ih

/-- The complete terminating source cluster reduction. -/
def reduce [DecidableEq Edge] (meet : Edge → Edge → Edge) (edges : List Edge) : List Edge :=
  match edges with
  | [] => []
  | edge :: rest =>
    match _result : ruleOut meet edge rest with
    | (some other, remaining) => reduce meet (other :: remaining)
    | (none, remaining) => edge :: reduce meet remaining
termination_by edges.length
decreasing_by
  all_goals
    have bound := ruleOut_length meet edge rest
    rw [_result] at bound
    simp at bound ⊢
    omega

/-- An alternative list denotes its union language. -/
def Denotes (meaning : Edge → Term → Prop) (edges : List Edge) (term : Term) : Prop :=
  ∃ edge ∈ edges, meaning edge term

/-- List concatenation denotes language union. -/
theorem denotes_cons (meaning : Edge → Term → Prop) (edge : Edge) (rest : List Edge) (term : Term) :
    Denotes meaning (edge :: rest) term ↔ meaning edge term ∨ Denotes meaning rest term := by
  simp [Denotes]

/-- One comparison worker preserves its pivot's combined language. -/
theorem ruleOut_exact [DecidableEq Edge] (meet : Edge → Edge → Edge) (meaning : Edge → Term → Prop)
    (intersection : ∀ first second term, meaning (meet first second) term ↔ meaning first term ∧ meaning second term)
    (edge : Edge) (edges : List Edge) (term : Term) :
    Denotes meaning ((ruleOut meet edge edges).1.getD edge :: (ruleOut meet edge edges).2) term ↔
      Denotes meaning (edge :: edges) term := by
  induction edges with
  | nil => rfl
  | cons other rest ih =>
    by_cases covered : meet edge other = other
    · have implies : meaning other term → meaning edge term := by
        intro accepted
        exact ((intersection edge other term).mp (by simpa [covered] using accepted)).1
      simp only [ruleOut, ite_eq_left covered]
      simp only [denotes_cons] at *
      grind
    · by_cases dominates : meet edge other = edge
      · have implies : meaning edge term → meaning other term := by
          intro accepted
          exact ((intersection edge other term).mp (by simpa [dominates] using accepted)).2
        simp only [ruleOut, ite_eq_right covered, ite_eq_left dominates, Option.getD_some]
        simp only [denotes_cons]
        grind
      · simp only [ruleOut, ite_eq_right covered, ite_eq_right dominates]
        simp only [denotes_cons] at *
        grind

/-- Removing redundant alternatives preserves every term of the cluster. -/
theorem reduce_exact [DecidableEq Edge] (meet : Edge → Edge → Edge) (meaning : Edge → Term → Prop)
    (intersection : ∀ first second term, meaning (meet first second) term ↔ meaning first term ∧ meaning second term)
    (edges : List Edge) (term : Term) : Denotes meaning (reduce meet edges) term ↔ Denotes meaning edges term := by
  fun_induction reduce meet edges with
  | case1 => rfl
  | case2 edge rest other remaining result ih =>
    have preserved := ruleOut_exact meet meaning intersection edge rest term
    rw [result] at preserved
    exact ih.trans preserved
  | case3 edge rest remaining result ih =>
    have preserved := ruleOut_exact meet meaning intersection edge rest term
    rw [result] at preserved
    simp only [Option.getD_none, denotes_cons] at preserved
    simpa only [denotes_cons] using (or_congr Iff.rfl ih).trans preserved

/-- Reducing each disjoint symbol group preserves their combined language. -/
theorem clusters_exact [DecidableEq Edge] (meet : Edge → Edge → Edge) (meaning : Edge → Term → Prop)
    (intersection : ∀ first second term, meaning (meet first second) term ↔ meaning first term ∧ meaning second term)
    (clusters : List (List Edge)) (term : Term) :
    Denotes meaning (clusters.flatMap (reduce meet)) term ↔ Denotes meaning clusters.flatten term := by
  simp only [Denotes, List.mem_flatMap, List.mem_flatten]
  constructor
  · rintro ⟨edge, ⟨cluster, member, present⟩, accepted⟩
    obtain ⟨original, originalMember, accepts⟩ :=
      (reduce_exact meet meaning intersection cluster term).mp ⟨edge, present, accepted⟩
    exact ⟨original, ⟨cluster, member, originalMember⟩, accepts⟩
  · rintro ⟨edge, ⟨cluster, member, present⟩, accepted⟩
    obtain ⟨retained, retainedMember, accepts⟩ :=
      (reduce_exact meet meaning intersection cluster term).mpr ⟨edge, present, accepted⟩
    exact ⟨retained, ⟨cluster, member, retainedMember⟩, accepts⟩

/-- Key grouping order cannot affect the preserved union language. -/
theorem grouped_exact [DecidableEq Edge] (meet : Edge → Edge → Edge) (meaning : Edge → Term → Prop)
    (intersection : ∀ first second term, meaning (meet first second) term ↔ meaning first term ∧ meaning second term)
    (input : List Edge) (clusters : List (List Edge)) (partition : clusters.flatten.Perm input) (term : Term) :
    Denotes meaning (clusters.flatMap (reduce meet)) term ↔ Denotes meaning input term := by
  rw [clusters_exact meet meaning intersection clusters term]
  simp only [Denotes, partition.mem_iff]

end MicroCFTA.RedundantEdges
