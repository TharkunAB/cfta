import MicroCFTA.InternedProfileSemantics

/-!
# Pure free names for complete constructor syntax

Root profiles decide which node edges survive. The interpreter combines
the free names from those edges and from every union operand. Both binder
forms remove their symbolic local. External-name maps need not be injective.
Source cache correspondence is a separate obligation.
-/
namespace MicroCFTA.InternedFreeNameSemantics
open InternedNestedConstruction
open InternedProfileSemantics (Abstract mapNames isEmpty)

/-- Remove the symbolic local when leaving either binder form. -/
def lower (names : List (Sum Unit Atom)) : List Atom :=
  names.filterMap (fun name => match name with | .inl _ => none | .inr value => some value)

mutual
/-- Interpret free names with root profiles that decide live node edges. -/
def evaluate {Atom : Type} (expression : Syntax Symbol Guard)
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) : List Atom :=
  match expression with
  | .empty => []
  | .var index => freeNames[index]?.getD []
  | .node edges => evaluateEdges edges profiles freeNames
  | .union members => (evaluateMany members profiles freeNames).flatten
  | .binder _ body => lower (evaluate body
      (some [.inl ()] :: profiles.map (mapNames Sum.inr))
      ([.inl ()] :: freeNames.map (List.map Sum.inr)))
termination_by sizeOf expression

/-- Retain the free-name list for each source operand in source order. -/
def evaluateMany {Atom : Type} (expressions : List (Syntax Symbol Guard))
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) : List (List Atom) :=
  match expressions with
  | [] => []
  | first :: rest => evaluate first profiles freeNames :: evaluateMany rest profiles freeNames
termination_by sizeOf expressions

/-- Combine the free names of children from each surviving node edge. -/
def evaluateEdges {Atom : Type} (edges : List (EdgeSyntax Symbol Guard))
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) : List Atom :=
  match edges with
  | [] => []
  | .mk _ _ children :: rest =>
      (if (InternedProfileSemantics.evaluateMany children profiles).all (fun child => !isEmpty child)
        then (evaluateMany children profiles freeNames).flatten else []) ++
      evaluateEdges rest profiles freeNames
termination_by sizeOf edges
end

/-- Lowering commutes with every external-name map. -/
theorem lower_map (function : Atom → Other) (names : List (Sum Unit Atom)) :
    lower (names.map (Sum.map id function)) = (lower names).map function := by
  unfold lower
  induction names with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [ih]

/-- A free-name environment map preserves the distinguished symbolic local. -/
theorem local_map (function : Atom → Other) (freeNames : List (List Atom)) :
    ([Sum.inl ()] :: freeNames.map (List.map Sum.inr)).map (List.map (Sum.map id function)) =
      [.inl ()] :: (freeNames.map (List.map function)).map (List.map Sum.inr) := by
  simp [List.map_map, Function.comp_def]

mutual
/-- Full syntax free names commute with arbitrary external-name maps. -/
theorem evaluate_map {Atom Other : Type} (function : Atom → Other) (expression : Syntax Symbol Guard)
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) :
    evaluate expression (profiles.map (mapNames function)) (freeNames.map (List.map function)) =
      (evaluate expression profiles freeNames).map function := by
  cases expression with
  | empty => simp [evaluate]
  | var index =>
      rw [evaluate, evaluate]
      cases found : freeNames[index]? <;> simp [List.getElem?_map, found]
  | node edges => simpa only [evaluate] using evaluateEdges_map function edges profiles freeNames
  | union members =>
      simp only [evaluate, evaluateMany_map function members profiles freeNames, List.map_flatten]
  | binder smart body =>
      rw [evaluate, evaluate, ← InternedProfileSemantics.local_map function profiles,
        ← local_map function freeNames, evaluate_map (Sum.map id function) body, lower_map]
termination_by sizeOf expression

/-- The map law preserves the list of operand free-name results. -/
theorem evaluateMany_map {Atom Other : Type} (function : Atom → Other) (expressions : List (Syntax Symbol Guard))
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) :
    evaluateMany expressions (profiles.map (mapNames function)) (freeNames.map (List.map function)) =
      (evaluateMany expressions profiles freeNames).map (List.map function) := by
  cases expressions with
  | nil => simp [evaluateMany]
  | cons first rest =>
      simp only [evaluateMany, evaluate_map function first profiles freeNames,
        evaluateMany_map function rest profiles freeNames, List.map_cons]
termination_by sizeOf expressions

/-- Mapping external names preserves edge liveness and maps the surviving free names. -/
theorem evaluateEdges_map {Atom Other : Type} (function : Atom → Other) (edges : List (EdgeSyntax Symbol Guard))
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) :
    evaluateEdges edges (profiles.map (mapNames function)) (freeNames.map (List.map function)) =
      (evaluateEdges edges profiles freeNames).map function := by
  cases edges with
  | nil => simp [evaluateEdges]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [evaluateEdges, InternedProfileSemantics.evaluateMany_map function children profiles,
            List.all_map, Function.comp_def, InternedProfileSemantics.isEmpty_map,
            evaluateMany_map function children profiles freeNames,
            evaluateEdges_map function rest profiles freeNames, List.map_append]
          split <;> simp [List.map_flatten]
termination_by sizeOf edges
end

/-- Lowering retains exactly the externally tagged names. -/
theorem lower_member (names : List (Sum Unit Atom)) (name : Atom) :
    name ∈ lower names ↔ Sum.inr name ∈ names := by
  unfold lower
  induction names with
  | nil => simp
  | cons first rest ih => cases first <;> simp [ih]

/-- A combined operand result contains a name exactly when one operand contains it. -/
theorem evaluateMany_member (expressions : List (Syntax Symbol Guard))
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) (name : Atom) :
    name ∈ (evaluateMany expressions profiles freeNames).flatten ↔
      ∃ expression ∈ expressions, name ∈ evaluate expression profiles freeNames := by
  induction expressions with
  | nil => simp [evaluateMany]
  | cons first rest ih => simp [evaluateMany, ih]

/-- A node free name belongs to a child of one surviving source edge. -/
theorem evaluateEdges_member (edges : List (EdgeSyntax Symbol Guard))
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) (name : Atom) :
    name ∈ evaluateEdges edges profiles freeNames ↔
      ∃ symbol guard children, EdgeSyntax.mk symbol guard children ∈ edges ∧
        (InternedProfileSemantics.evaluateMany children profiles).all (fun child => !isEmpty child) = true ∧
        ∃ expression ∈ children, name ∈ evaluate expression profiles freeNames := by
  induction edges with
  | nil => simp [evaluateEdges]
  | cons first rest ih =>
      cases first with
      | mk symbol guard children =>
          simp only [evaluateEdges, List.mem_append, ih, List.mem_cons, EdgeSyntax.mk.injEq]
          have head : (name ∈ if (InternedProfileSemantics.evaluateMany children profiles).all
                (fun child => !isEmpty child) then (evaluateMany children profiles freeNames).flatten else []) ↔
              (InternedProfileSemantics.evaluateMany children profiles).all (fun child => !isEmpty child) = true ∧
                ∃ expression ∈ children, name ∈ evaluate expression profiles freeNames := by
            split <;> simp_all only [evaluateMany_member, true_and, false_and, iff_self, List.not_mem_nil, Bool.false_eq_true]
          rw [head]
          constructor
          · rintro (⟨live, member⟩ | ⟨s, g, c, included, live, member⟩)
            · exact ⟨symbol, guard, children, Or.inl ⟨rfl, rfl, rfl⟩, live, member⟩
            · exact ⟨s, g, c, Or.inr included, live, member⟩
          · rintro ⟨s, g, c, included, live, member⟩
            rcases included with same | included
            · rcases same with ⟨rfl, rfl, rfl⟩
              exact Or.inl ⟨live, member⟩
            · exact Or.inr ⟨s, g, c, included, live, member⟩

mutual
/-- Every external free name comes from one supplied free-name list. -/
theorem evaluate_origins {Atom : Type} (expression : Syntax Symbol Guard)
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) (name : Atom)
    (member : name ∈ evaluate expression profiles freeNames) :
    ∃ names ∈ freeNames, name ∈ names := by
  cases expression with
  | empty => simp [evaluate] at member
  | var index =>
      rw [evaluate] at member
      cases found : freeNames[index]? with
      | none => simp [found] at member
      | some names => exact ⟨names, List.mem_of_getElem? found, by simpa [found] using member⟩
  | node edges =>
      exact evaluateEdges_origins edges profiles freeNames name (by simpa only [evaluate] using member)
  | union members =>
      exact evaluateMany_origins members profiles freeNames name (by simpa only [evaluate] using member)
  | binder smart body =>
      rw [evaluate, lower_member] at member
      obtain ⟨names, included, present⟩ := evaluate_origins body
        (some [.inl ()] :: profiles.map (mapNames Sum.inr))
        ([.inl ()] :: freeNames.map (List.map Sum.inr)) (.inr name) member
      rcases List.mem_cons.mp included with bound | captured
      · simp [bound] at present
      · obtain ⟨original, originalIncluded, same⟩ := List.mem_map.mp captured
        rw [← same] at present
        exact ⟨original, originalIncluded, by simpa using present⟩
termination_by sizeOf expression

/-- Each external name in an operand result comes from the supplied environment. -/
theorem evaluateMany_origins {Atom : Type} (expressions : List (Syntax Symbol Guard))
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) (name : Atom)
    (member : name ∈ (evaluateMany expressions profiles freeNames).flatten) :
    ∃ names ∈ freeNames, name ∈ names := by
  cases expressions with
  | nil => simp [evaluateMany] at member
  | cons first rest =>
      simp only [evaluateMany, List.flatten_cons, List.mem_append] at member
      rcases member with firstMember | restMember
      · exact evaluate_origins first profiles freeNames name firstMember
      · exact evaluateMany_origins rest profiles freeNames name restMember
termination_by sizeOf expressions

/-- Each external name in live edges comes from the supplied environment. -/
theorem evaluateEdges_origins {Atom : Type} (edges : List (EdgeSyntax Symbol Guard))
    (profiles : List (Abstract Atom)) (freeNames : List (List Atom)) (name : Atom)
    (member : name ∈ evaluateEdges edges profiles freeNames) :
    ∃ names ∈ freeNames, name ∈ names := by
  cases edges with
  | nil => simp [evaluateEdges] at member
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [evaluateEdges, List.mem_append] at member
          rcases member with firstMember | restMember
          · split at firstMember
            · exact evaluateMany_origins children profiles freeNames name firstMember
            · simp at firstMember
          · exact evaluateEdges_origins rest profiles freeNames name restMember
termination_by sizeOf edges
end

end MicroCFTA.InternedFreeNameSemantics
