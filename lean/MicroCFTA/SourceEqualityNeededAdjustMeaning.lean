import MicroCFTA.SourceEqualityNeededAdjust
import MicroCFTA.SourceEqualityNeededMeaning

/-!
# Forest meaning of the actual required-child adjustment fold

Each node callback must preserve exactly its original terms that satisfy its
child requirement. The list proof composes these explicit per-node contracts.
The physical recursive node worker still has to derive those contracts.
-/
namespace MicroCFTA.SourceEqualityNeededAdjustMeaning
open Language SourceEqualityNeeded SourceEqualityNeededMeaning
open SourceEqualityNeededAdjust

/-- One natural child adjustment conjoins the requirement at that existing term. -/
theorem adjustList_exact (meaning : Node → Term Symbol → Prop) (condition : Term Symbol → Prop)
    (change : Node → Node)
    (correct : ∀ value term, meaning (change value) term ↔ meaning value term ∧ condition term)
    (values : List Node) (terms : List (Term Symbol)) (index : Nat) :
    All₂ meaning (TermOperations.adjustList change index values) terms ↔
      All₂ meaning values terms ∧ ∀ term, terms[index]? = some term → condition term := by
  induction values generalizing terms index with
  | nil =>
      cases terms with
      | nil => simp [TermOperations.adjustList]
      | cons term terms =>
          simp only [TermOperations.adjustList]
          constructor
          · intro impossible; cases impossible
          · rintro ⟨impossible, _⟩; cases impossible
  | cons value values ih =>
      cases terms with
      | nil =>
          cases index <;> simp only [TermOperations.adjustList]
          all_goals
            constructor
            · intro impossible; cases impossible
            · rintro ⟨impossible, _⟩; cases impossible
      | cons term terms =>
          cases index with
          | zero =>
              simp only [TermOperations.adjustList, List.getElem?_cons_zero, Option.some.injEq,
                forall_eq']
              constructor
              · intro accepted
                cases accepted with
                | cons first rest =>
                    have retained := (correct value term).mp first
                    exact ⟨.cons retained.1 rest, retained.2⟩
              · rintro ⟨accepted, matched⟩
                cases accepted with
                | cons first rest => exact .cons ((correct value term).mpr ⟨first, matched⟩) rest
          | succ index =>
              simp only [TermOperations.adjustList, List.getElem?_cons_succ]
              constructor
              · intro accepted
                cases accepted with
                | cons first rest =>
                    obtain ⟨before, matched⟩ := (ih terms index).mp rest
                    exact ⟨.cons first before, matched⟩
              · rintro ⟨accepted, matched⟩
                cases accepted with
                | cons first rest => exact .cons first ((ih terms index).mpr ⟨rest, matched⟩)

/-- Signed adjustment imposes a condition only when that child exists. -/
theorem adjust_exact (meaning : Node → Term Symbol → Prop) (condition : Term Symbol → Prop)
    (change : Node → Node)
    (correct : ∀ value term, meaning (change value) term ↔ meaning value term ∧ condition term)
    (values : List Node) (terms : List (Term Symbol)) (index : Int) :
    All₂ meaning (adjust index change values) terms ↔
      All₂ meaning values terms ∧ ∀ term, childAt terms index = some term → condition term := by
  unfold adjust childAt
  split
  · simp
  · exact adjustList_exact meaning condition change correct values terms index.toNat

/-- The source right fold keeps its input forest and all requirements at present positions. -/
theorem apply_exact (meaning : Node → Term Symbol → Prop) (change : Needed → Node → Node)
    (correct : ∀ needed value term,
      meaning (change needed value) term ↔ meaning value term ∧ Matches needed term)
    (entries : List (Int × Needed)) (values : List Node) (terms : List (Term Symbol)) :
    All₂ meaning (apply change entries values) terms ↔
      All₂ meaning values terms ∧ ∀ index needed, (index, needed) ∈ entries →
        ∀ term, childAt terms index = some term → Matches needed term := by
  induction entries with
  | nil => simp [apply]
  | cons entry rest ih =>
      obtain ⟨index, needed⟩ := entry
      change All₂ meaning (adjust index (change needed) (apply change rest values)) terms ↔ _
      rw [adjust_exact meaning (Matches needed) (change needed) (correct needed), ih]
      constructor
      · rintro ⟨⟨before, prior⟩, selected⟩
        refine ⟨before, ?_⟩
        intro key child member
        rcases List.mem_cons.mp member with same | member
        · cases same; exact selected
        · exact prior key child member
      · rintro ⟨before, allChildren⟩
        exact ⟨⟨before, fun key child member => allChildren key child (List.mem_cons_of_mem _ member)⟩,
          allChildren index needed List.mem_cons_self⟩

/-- Existing normalized child positions turn the conditional fold result into the full trie meaning. -/
theorem row_exact (meaning : Node → Term Symbol → Prop) (change : Needed → Node → Node)
    (correct : ∀ needed value term,
      meaning (change needed value) term ↔ meaning value term ∧ Matches needed term)
    (entries : List (Int × Needed)) (values : List Node) (symbol : Symbol) (terms : List (Term Symbol))
    (inside : ∀ index needed, (index, needed) ∈ entries → 0 ≤ index ∧ index < (terms.length : Int)) :
    All₂ meaning (apply change entries values) terms ↔
      All₂ meaning values terms ∧ Matches (.node entries) (.node symbol terms) := by
  rw [apply_exact meaning change correct, Matches]
  constructor
  · rintro ⟨before, allChildren⟩
    refine ⟨before, ?_⟩
    intro index needed member
    have bounds := inside index needed member
    have natural : index.toNat < terms.length := by omega
    have selected : childAt terms index = some terms[index.toNat] := by
      simp [childAt, show ¬index < 0 by omega, List.getElem?_eq_getElem natural]
    exact ⟨terms[index.toNat], selected, allChildren index needed member _ selected⟩
  · rintro ⟨before, allChildren⟩
    refine ⟨before, ?_⟩
    intro index needed member term selected
    obtain ⟨actual, found, matched⟩ := allChildren index needed member
    have same := Option.some.inj (found.symm.trans selected)
    exact same ▸ matched

/-- The actual row arity check and normalized keys derive every required child position. -/
theorem checked_row_exact (meaning : Node → Term Symbol → Prop) (change : Needed → Node → Node)
    (correct : ∀ needed value term,
      meaning (change needed value) term ↔ meaning value term ∧ Matches needed term)
    (entries : List (Int × Needed)) (valid : Valid (.node entries))
    (nonnegative : ∀ index needed, (index, needed) ∈ entries → 0 ≤ index)
    (values : List Node) (symbol : Symbol) (terms : List (Term Symbol))
    (rowFits : fits (.node entries) values.length = true) :
    All₂ meaning (apply change entries values) terms ↔
      All₂ meaning values terms ∧ Matches (.node entries) (.node symbol terms) := by
  have ordered := (show SourceEqualityNeededMap.Ascending entries ∧ _ from
    (by simpa only [Valid] using valid)).1
  have inside (before : All₂ meaning values terms) :
      ∀ index needed, (index, needed) ∈ entries → 0 ≤ index ∧ index < (terms.length : Int) := by
    intro index needed member
    have required := (child_demand entries ordered index).mpr ⟨needed, member⟩
    have bound := (fits_exact (.node entries) valid values.length).mp rowFits index required
    have sameLength := before.length_eq
    exact ⟨nonnegative index needed member, by simpa only [sameLength] using bound⟩
  constructor
  · intro accepted
    have before := ((apply_exact meaning change correct entries values terms).mp accepted).1
    exact (row_exact meaning change correct entries values symbol terms (inside before)).mp accepted
  · rintro ⟨before, matched⟩
    exact (row_exact meaning change correct entries values symbol terms (inside before)).mpr ⟨before, matched⟩

end MicroCFTA.SourceEqualityNeededAdjustMeaning
