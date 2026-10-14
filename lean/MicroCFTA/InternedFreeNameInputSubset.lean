import MicroCFTA.InternedFreeNameSemantics

/-!
# Free-name inclusion at fixed symbolic profiles

Adding names to the lexical free-name lists cannot remove an interpreted
free name. Root profiles and source edge selection stay fixed.
-/
namespace MicroCFTA.InternedFreeNameInputSubset
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedProfileSemantics (Abstract mapNames)
open InternedFreeNameSemantics

/-- Lookup and a name map commute for each lexical free-name list. -/
theorem map_lookup (inputs : List (List Atom)) (function : Atom → Other) (index : Nat) :
    ((inputs.map (List.map function))[index]?).getD [] = ((inputs[index]?).getD []).map function := by
  cases found : inputs[index]? <;> simp [List.getElem?_map, found]

/-- One common bound name and mapped captures retain lexical free-name inclusion. -/
theorem local_included (first second : List (List Atom))
    (included : ∀ (index : Nat) (name : Atom), name ∈ (first[index]?).getD [] → name ∈ (second[index]?).getD []) :
    ∀ (index : Nat) (name : Sum Unit Atom),
      name ∈ (([Sum.inl ()] :: first.map (List.map Sum.inr))[index]?).getD [] →
      name ∈ (([Sum.inl ()] :: second.map (List.map Sum.inr))[index]?).getD [] := by
  intro index name member
  cases index with
  | zero => simpa only [List.getElem?_cons_zero, Option.getD_some] using member
  | succ index =>
      simp only [List.getElem?_cons_succ, map_lookup] at member ⊢
      obtain ⟨original, present, same⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨original, included index original present, same⟩

mutual
/-- Free-name interpretation preserves inclusion of all actual lexical lists. -/
theorem evaluate_included (expression : Syntax Symbol Guard) (profiles : List (Abstract Atom))
    (first second : List (List Atom))
    (included : ∀ (index : Nat) (name : Atom), name ∈ (first[index]?).getD [] → name ∈ (second[index]?).getD [])
    (name : Atom) (member : name ∈ evaluate expression profiles first) : name ∈ evaluate expression profiles second := by
  cases expression with
  | empty => simp [evaluate] at member
  | var index => simpa only [evaluate] using included index name (by simpa only [evaluate] using member)
  | node edges => simpa only [evaluate] using evaluateEdges_included edges profiles first second included name (by simpa only [evaluate] using member)
  | union members => simpa only [evaluate] using evaluateMany_included members profiles first second included name (by simpa only [evaluate] using member)
  | binder smart body =>
      rw [evaluate, lower_member] at member ⊢
      exact evaluate_included body _ _ _ (local_included first second included) (.inr name) member
termination_by sizeOf expression

/-- Ordered child free-name lists preserve inclusion after concatenation. -/
theorem evaluateMany_included (expressions : List (Syntax Symbol Guard)) (profiles : List (Abstract Atom))
    (first second : List (List Atom))
    (included : ∀ (index : Nat) (name : Atom), name ∈ (first[index]?).getD [] → name ∈ (second[index]?).getD [])
    (name : Atom) (member : name ∈ (evaluateMany expressions profiles first).flatten) :
    name ∈ (evaluateMany expressions profiles second).flatten := by
  cases expressions with
  | nil => simp [evaluateMany] at member
  | cons head tail =>
      simp only [evaluateMany, List.flatten_cons, List.mem_append] at member ⊢
      rcases member with headMember | tailMember
      · exact Or.inl (evaluate_included head profiles first second included name headMember)
      · exact Or.inr (evaluateMany_included tail profiles first second included name tailMember)
termination_by sizeOf expressions

/-- The unchanged profile decisions retain inclusion on every surviving source edge. -/
theorem evaluateEdges_included (expressions : List (EdgeSyntax Symbol Guard)) (profiles : List (Abstract Atom))
    (first second : List (List Atom))
    (included : ∀ (index : Nat) (name : Atom), name ∈ (first[index]?).getD [] → name ∈ (second[index]?).getD [])
    (name : Atom) (member : name ∈ evaluateEdges expressions profiles first) :
    name ∈ evaluateEdges expressions profiles second := by
  cases expressions with
  | nil => simp [evaluateEdges] at member
  | cons edge tail =>
      cases edge with
      | mk symbol guard children =>
          simp only [evaluateEdges, List.mem_append] at member ⊢
          rcases member with headMember | tailMember
          · apply Or.inl
            cases live : (InternedProfileSemantics.evaluateMany children profiles).all
                (fun child => !InternedProfileSemantics.isEmpty child) with
            | true =>
                simp only [live, ↓reduceIte] at headMember ⊢
                exact evaluateMany_included children profiles first second included name headMember
            | false => simpa only [live, Bool.false_eq_true, ↓reduceIte] using headMember
          · exact Or.inr (evaluateEdges_included tail profiles first second included name tailMember)
termination_by sizeOf expressions
end

end MicroCFTA.InternedFreeNameInputSubset
