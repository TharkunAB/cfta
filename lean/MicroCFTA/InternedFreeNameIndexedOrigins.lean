import MicroCFTA.InternedFreshOrdinaryContext

/-!
# Exact lexical positions of returned free-name origins

Every returned free name comes from a syntactically used lexical position.
Binder traversal shifts that position and excludes its symbolic local.
The support relation can include an occurrence in a deleted edge.
-/
namespace MicroCFTA.InternedFreeNameIndexedOrigins
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreeNameSemantics
open InternedBinderProtocol (Reference)

mutual
/-- A syntax tree contains an occurrence of this external lexical position. -/
def Uses (expression : Syntax Symbol Guard) (index : Nat) : Prop :=
  match expression with
  | .empty => False
  | .var selected => selected = index
  | .node edges => UsesEdges edges index
  | .union members => UsesMany members index
  | .binder _ body => Uses body (index + 1)
termination_by sizeOf expression

/-- One ordered operand contains the specified external lexical occurrence. -/
def UsesMany (expressions : List (Syntax Symbol Guard)) (index : Nat) : Prop :=
  match expressions with
  | [] => False
  | first :: rest => Uses first index ∨ UsesMany rest index
termination_by sizeOf expressions

/-- One source edge child contains the specified external lexical occurrence. -/
def UsesEdges (edges : List (EdgeSyntax Symbol Guard)) (index : Nat) : Prop :=
  match edges with
  | [] => False
  | .mk _ _ children :: rest => UsesMany children index ∨ UsesEdges rest index
termination_by sizeOf edges
end

mutual
/-- Pure free-name evaluation retains a used external position for each returned name. -/
theorem evaluate_indexed {Atom : Type} (expression : Syntax Symbol Guard)
    (profiles : List (InternedProfileSemantics.Abstract Atom)) (freeNames : List (List Atom)) (name : Atom)
    (member : name ∈ evaluate expression profiles freeNames) :
    ∃ index, Uses expression index ∧ name ∈ (freeNames[index]?).getD [] := by
  cases expression with
  | empty => simp [evaluate] at member
  | var index => exact ⟨index, by rw [Uses], by simpa only [evaluate] using member⟩
  | node edges =>
      simpa only [Uses] using evaluateEdges_indexed edges profiles freeNames name (by simpa only [evaluate] using member)
  | union members =>
      simpa only [Uses] using evaluateMany_indexed members profiles freeNames name (by simpa only [evaluate] using member)
  | binder smart body =>
      rw [evaluate, lower_member] at member
      obtain ⟨index, used, named⟩ := evaluate_indexed body
        (some [.inl ()] :: profiles.map (InternedProfileSemantics.mapNames Sum.inr))
        ([.inl ()] :: freeNames.map (List.map Sum.inr)) (.inr name) member
      cases index with
      | zero => simp at named
      | succ index =>
          refine ⟨index, by simpa only [Uses] using used, ?_⟩
          cases found : freeNames[index]? with
          | none => simp [List.getElem?_map, found] at named
          | some names => simpa [List.getElem?_map, found] using named
termination_by sizeOf expression

/-- A name in ordered operands retains its original used lexical position. -/
theorem evaluateMany_indexed {Atom : Type} (expressions : List (Syntax Symbol Guard))
    (profiles : List (InternedProfileSemantics.Abstract Atom)) (freeNames : List (List Atom)) (name : Atom)
    (member : name ∈ (evaluateMany expressions profiles freeNames).flatten) :
    ∃ index, UsesMany expressions index ∧ name ∈ (freeNames[index]?).getD [] := by
  cases expressions with
  | nil => simp [evaluateMany] at member
  | cons first rest =>
      simp only [evaluateMany, List.flatten_cons, List.mem_append] at member
      rcases member with included | included
      · obtain ⟨index, used, named⟩ := evaluate_indexed first profiles freeNames name included
        exact ⟨index, by rw [UsesMany]; exact Or.inl used, named⟩
      · obtain ⟨index, used, named⟩ := evaluateMany_indexed rest profiles freeNames name included
        exact ⟨index, by rw [UsesMany]; exact Or.inr used, named⟩
termination_by sizeOf expressions

/-- A name in surviving edges retains its original used lexical position. -/
theorem evaluateEdges_indexed {Atom : Type} (edges : List (EdgeSyntax Symbol Guard))
    (profiles : List (InternedProfileSemantics.Abstract Atom)) (freeNames : List (List Atom)) (name : Atom)
    (member : name ∈ evaluateEdges edges profiles freeNames) :
    ∃ index, UsesEdges edges index ∧ name ∈ (freeNames[index]?).getD [] := by
  cases edges with
  | nil => simp [evaluateEdges] at member
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [evaluateEdges, List.mem_append] at member
          rcases member with included | included
          · split at included
            · obtain ⟨index, used, named⟩ := evaluateMany_indexed children profiles freeNames name included
              exact ⟨index, by rw [UsesEdges]; exact Or.inl used, named⟩
            · simp at included
          · obtain ⟨index, used, named⟩ := evaluateEdges_indexed rest profiles freeNames name included
            exact ⟨index, by rw [UsesEdges]; exact Or.inr used, named⟩
termination_by sizeOf edges
end

/-- Every actual returned free name has an exact used lexical slot and its complete original record. -/
theorem source_indexed [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context state environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryConstruction.build expression environment state = .done value after)
    (name : Reference) (member : name ∈ value.free) :
    ∃ index original, Uses expression index ∧ environment[index]? = some original ∧ name ∈ original.free := by
  have same := (InternedFreshOrdinaryFreeNames.build_free expression environment state context.normal context.inputs
    context.freeNames context.profiles).result value after done name
  obtain ⟨index, used, named⟩ := evaluate_indexed expression (environment.map InternedRootProfile.profile)
    (environment.map Value.free) name (same.mp member)
  cases found : environment[index]? with
  | none => simp [List.getElem?_map, found] at named
  | some original => exact ⟨index, original, used, found, by simpa [List.getElem?_map, found] using named⟩

end MicroCFTA.InternedFreeNameIndexedOrigins
