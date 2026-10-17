import MicroCFTA.SourceCurrentLiteralUnionParts
import MicroCFTA.InternedStoredMuOrigins

/-!
# Literal root parts through actual self filtering

Bare self remains unchanged. A stored union removes its self alternative.
Normal available roots distinguish these cases by their literal atoms and
ordinary rows. Mu atoms remain complete opaque values throughout the proof.
-/
namespace MicroCFTA.SourceCurrentLiteralFilterParts
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open InternedUnionNormalForm (Atomic)
open SourceCurrentLiteralRootParts (Literal Row)
open InternedBinderProtocol (Reference)

private theorem atomic_literal {value atom : Value Symbol Guard} (atomic : Atomic value)
    (part : Literal value atom) : value = atom := by
  cases value with
  | empty | node => cases part
  | reference | mu => cases part; rfl
  | union => cases atomic

/-- Normal available parts identify the exceptional bare-self input exactly. -/
theorem bare_iff (state : State Symbol Guard) (normal : Normal state) (name : Reference)
    (value : Value Symbol Guard) (available : Available state value) :
    value = .reference name ↔ Literal value (.reference name) ∧
      (∀ atom, Literal value atom → atom = .reference name) ∧ (∀ row, ¬ Row value row) := by
  constructor
  · rintro rfl
    refine ⟨by constructor, ?_, ?_⟩
    · intro atom part
      cases part
      rfl
    · intro row impossible
      cases impossible
  · rintro ⟨self, unique, noRows⟩
    cases value with
    | empty | node | mu => cases self
    | reference other => cases self; rfl
    | union entry members level free =>
        have flat := InternedUnionNormalForm.resident_flat state normal.flat _ available.resident
        have nonempty := InternedUnionNonemptyMembers.resident_membersNonempty state normal.members _ available.resident
        have proper := InternedNonemptyRecords.resident_nonempty state normal.proper _ available.resident
        have each : ∀ member ∈ members, member = .reference name := by
          intro member included
          have memberAvailable := available.children member included
          have atomic := flat member included
          cases member with
          | empty => exact False.elim (nonempty .empty included rfl)
          | reference other =>
              apply unique
              exact (SourceCurrentLiteralRootParts.literal_union entry members level free _).mpr
                ⟨.reference other, included, by constructor⟩
          | node own rows depth names =>
              have rowsNonempty := InternedNonemptyRecords.resident_nonempty state normal.proper _ memberAvailable.resident
              cases rows with
              | nil => exact False.elim (rowsNonempty rfl)
              | cons row rest =>
                  apply False.elim
                  apply noRows row
                  exact (SourceCurrentLiteralRootParts.row_union entry members level free row).mpr
                    ⟨_, included, (SourceCurrentLiteralRootParts.row_node own _ depth names row).mpr List.mem_cons_self⟩
          | union => cases atomic
          | mu own body depth ordinary =>
              apply unique
              exact (SourceCurrentLiteralRootParts.literal_union entry members level free _).mpr
                ⟨.mu own body depth ordinary, included, by constructor⟩
        change 2 ≤ members.length ∧ (members.map Value.referenceOf).Nodup at proper
        cases members with
        | nil => simp only [List.length_nil] at proper; omega
        | cons first rest =>
            cases rest with
            | nil => simp only [List.length_singleton] at proper; omega
            | cons second rest =>
                have firstSame := each first List.mem_cons_self
                have secondSame := each second (List.mem_cons_of_mem _ List.mem_cons_self)
                have different := (List.nodup_cons.mp proper.2).1
                apply False.elim
                apply different
                exact List.mem_map.mpr ⟨second, List.mem_cons_self, by rw [firstSame, secondSame]⟩

private theorem unchanged (name : Reference) (value atom : Value Symbol Guard) (atomic : Atomic value) :
    Literal value atom ↔ Literal value atom ∧ (value = .reference name ∨ atom ≠ .reference name) := by
  constructor
  · intro part
    refine ⟨part, ?_⟩
    by_cases same : value = .reference name
    · exact Or.inl same
    · exact Or.inr (fun equal => same ((atomic_literal atomic part).trans equal))
  · exact And.left

/-- Actual self filtering removes only the literal self atom, except at a bare-self root. -/
theorem literal [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (normal : Normal state)
    (name : Reference) (value : Value Symbol Guard) (available : Available state value) (atom : Value Symbol Guard) :
    Literal (run (withoutSelfReference name value) state).1 atom ↔
      Literal value atom ∧ (value = .reference name ∨ atom ≠ .reference name) := by
  cases value with
  | empty => exact unchanged name .empty atom trivial
  | reference other => exact unchanged name (.reference other) atom trivial
  | node entry rows level free => exact unchanged name (.node entry rows level free) atom trivial
  | mu entry body depth ordinary => exact unchanged name (.mu entry body depth ordinary) atom trivial
  | union entry members level free =>
      have flat := InternedUnionNormalForm.resident_flat state normal.flat _ available.resident
      by_cases selected : members.any (fun member => member.referenceOf == .ref name) = true
      · simp only [withoutSelfReference, selected, ↓reduceIte]
        rw [SourceCurrentLiteralUnionParts.literal state normal.facts
          (members.filter (fun member => member.referenceOf != .ref name))
          (fun member included => available.children member (List.mem_filter.mp included).1) atom,
          SourceCurrentLiteralRootParts.literal_union]
        constructor
        · rintro ⟨member, included, part⟩
          refine ⟨⟨member, (List.mem_filter.mp included).1, part⟩, Or.inr ?_⟩
          intro same
          have valueSame := (atomic_literal (flat member (List.mem_filter.mp included).1) part).trans same
          have retained := bne_iff_ne.mp (List.mem_filter.mp included).2
          apply retained
          rw [valueSame]
          rfl
        · rintro ⟨⟨member, included, part⟩, different⟩
          rcases different with impossible | different
          · cases impossible
          · refine ⟨member, List.mem_filter.mpr ⟨included, bne_iff_ne.mpr ?_⟩, part⟩
            intro same
            exact different ((atomic_literal (flat member included) part).symm.trans
              ((referenceOf_self_iff name member).mp same))
      · have missing : members.any (fun member => member.referenceOf == .ref name) = false := Bool.eq_false_iff.mpr selected
        simp only [withoutSelfReference, missing, Bool.false_eq_true, ↓reduceIte, run]
        constructor
        · intro part
          refine ⟨part, Or.inr ?_⟩
          intro same
          subst atom
          obtain ⟨member, included, self⟩ :=
            (SourceCurrentLiteralRootParts.literal_union entry members level free (.reference name)).mp part
          have equal := atomic_literal (flat member included) self
          apply selected
          exact List.any_eq_true.mpr ⟨member, included, by rw [equal]; simp only [Value.referenceOf, beq_self_eq_true]⟩
        · exact And.left

/-- Actual self filtering preserves every complete ordinary row without unfolding Mu atoms. -/
theorem row [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (normal : Normal state)
    (name : Reference) (value : Value Symbol Guard) (available : Available state value) (output : EdgeValue Symbol Guard) :
    Row (run (withoutSelfReference name value) state).1 output ↔ Row value output := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members level free =>
      by_cases selected : members.any (fun member => member.referenceOf == .ref name) = true
      · simp only [withoutSelfReference, selected, ↓reduceIte]
        rw [SourceCurrentLiteralUnionParts.row state normal.facts normal.live
          (members.filter (fun member => member.referenceOf != .ref name))
          (fun member included => available.children member (List.mem_filter.mp included).1) output,
          SourceCurrentLiteralRootParts.row_union]
        constructor
        · rintro ⟨member, included, part⟩
          exact ⟨member, (List.mem_filter.mp included).1, part⟩
        · rintro ⟨member, included, part⟩
          refine ⟨member, List.mem_filter.mpr ⟨included, bne_iff_ne.mpr ?_⟩, part⟩
          intro same
          have bare := (referenceOf_self_iff name member).mp same
          subst member
          cases part
      · have missing : members.any (fun member => member.referenceOf == .ref name) = false := Bool.eq_false_iff.mpr selected
        simp only [withoutSelfReference, missing, Bool.false_eq_true, ↓reduceIte, run]

/-- Equal literal atoms and full rows determine equal actual self-filter parts in normal available heaps. -/
theorem congr [DecidableEq (EdgeKey Symbol Guard)] (firstState secondState : State Symbol Guard)
    (firstNormal : Normal firstState) (secondNormal : Normal secondState) (name : Reference)
    (first second : Value Symbol Guard) (firstAvailable : Available firstState first) (secondAvailable : Available secondState second)
    (sameLiteral : ∀ atom, Literal first atom ↔ Literal second atom) (sameRow : ∀ output, Row first output ↔ Row second output) :
    (∀ atom, Literal (run (withoutSelfReference name first) firstState).1 atom ↔
      Literal (run (withoutSelfReference name second) secondState).1 atom) ∧
    ∀ output, Row (run (withoutSelfReference name first) firstState).1 output ↔
      Row (run (withoutSelfReference name second) secondState).1 output := by
  have bare : first = .reference name ↔ second = .reference name := by
    rw [bare_iff firstState firstNormal name first firstAvailable, bare_iff secondState secondNormal name second secondAvailable]
    constructor
    · rintro ⟨self, unique, noRows⟩
      exact ⟨(sameLiteral _).mp self, fun atom part => unique atom ((sameLiteral atom).mpr part),
        fun output part => noRows output ((sameRow output).mpr part)⟩
    · rintro ⟨self, unique, noRows⟩
      exact ⟨(sameLiteral _).mpr self, fun atom part => unique atom ((sameLiteral atom).mp part),
        fun output part => noRows output ((sameRow output).mp part)⟩
  constructor
  · intro atom
    rw [literal firstState firstNormal name first firstAvailable atom,
      literal secondState secondNormal name second secondAvailable atom]
    exact and_congr (sameLiteral atom) (or_congr bare Iff.rfl)
  · intro output
    exact (row firstState firstNormal name first firstAvailable output).trans
      ((sameRow output).trans (row secondState secondNormal name second secondAvailable output).symm)

end MicroCFTA.SourceCurrentLiteralFilterParts
