import MicroCFTA.RecursiveJoinSupportSemantics

/-!
# Source support views through joins, application spines, and closing

A view retains its actual open graph, its application-spine alternatives,
and the roots emitted by label closing. Constructor proofs derive each
view from the preceding views. Guards remain attached to their roots.
-/
namespace MicroCFTA.RecursiveJoinSupportView
open Language GeneratorCombinators BinderLanguage SupportGraph SupportTerms

/-- A closed user root retains its ordered children and its complete predicate. -/
abbrev ClosedRoot (Symbol : Type) := List (Support Symbol) × (Term (Label Symbol) → Prop)

/-- Source label closing emits one user edge for each retained root. -/
def closed (symbol : Symbol) (roots : List (ClosedRoot Symbol)) : Support Symbol :=
  .alternatives (roots.map fun root => .branch ⟨.user symbol, root.2⟩ root.1)

/-- Every accepted closed term has the requested user root. -/
theorem closed_root (environment : Env (Label Symbol)) (symbol : Symbol) (roots : List (ClosedRoot Symbol))
    (term : Term (Label Symbol)) (accepted : meaning environment (closed symbol roots) term) :
    ∃ children, term = .node (.user symbol) children := by
  obtain ⟨shape, present, accepted⟩ := (SupportClosing.alternatives_exact _ _ _).mp accepted
  obtain ⟨root, _, rfl⟩ := List.mem_map.mp present
  simp only [meaning] at accepted
  obtain ⟨children, rfl, _, _⟩ := accepted
  exact ⟨children, rfl⟩

/-- One support view carries source spine and closing correspondence in every open environment. -/
structure View (Symbol : Type) where
  graph : Support Symbol
  spine : SupportSpineAlternatives.Spine Symbol
  valid : SupportSpineAlternatives.Valid spine
  spine_exact : ∀ environment term,
    meaning environment (SupportSpineAlternatives.graph spine) term ↔ meaning environment graph term
  closeRoots : Symbol → List (ClosedRoot Symbol)
  close_exact : ∀ environment symbol term,
    meaning environment (closed symbol (closeRoots symbol)) term ↔
      ∃ original, meaning environment graph original ∧ term = labelTerm symbol original

/-- Pure contributes no user children when the source closes its support. -/
def pure : View Symbol where
  graph := edge .pure []
  spine := .pure
  valid := by simp [SupportSpineAlternatives.Valid]
  spine_exact := by intros; simp only [SupportSpineAlternatives.graph]
  closeRoots := fun _ => [([], fun _ => True)]
  close_exact := by
    intro environment symbol term
    simp only [closed, List.map_cons, List.map_nil, SupportClosing.one_exact]
    change meaning environment (edge (.user symbol) []) term ↔ _
    simp only [SupportClosing.leaf_exact]
    simp [labelTerm]

/-- Ordinary support roots remain complete children under later labels. -/
def ordinary (payload : Payload (Label Symbol)) (children : List (Support Symbol))
    (ordinary : SupportClosing.ordinary payload.label = true) : View Symbol where
  graph := .branch payload children
  spine := .base payload children
  valid := by cases label : payload.label <;> simp_all [SupportClosing.ordinary, SupportSpineAlternatives.Valid]
  spine_exact := by intros; simp only [SupportSpineAlternatives.graph]
  closeRoots := fun _ => [([.branch payload children], fun _ => True)]
  close_exact := by
    intro environment symbol term
    simp only [closed, List.map_cons, List.map_nil, SupportClosing.one_exact]
    change meaning environment (edge (.user symbol) [.branch payload children]) term ↔ _
    rw [SupportClosing.unary_exact]
    constructor <;> rintro ⟨original, accepted, same⟩
    all_goals
      have parsed := accepted
      simp only [meaning] at parsed
      obtain ⟨terms, shape, _, _⟩ := parsed
      exact ⟨original, accepted, by simpa [shape, SupportClosing.ordinary_term symbol payload.label terms ordinary] using same⟩

/-- The join view retains the exact keyed children and descendant equalities. -/
def join (component : Nat) (operation : View Symbol) (arguments : List (View Symbol)) : View Symbol where
  graph := SupportJoin.joinNode component operation.graph (arguments.map (·.graph))
  spine := .base
    ⟨.joinN, fun term => ∀ index < arguments.length, PathsEqual term [0, index + 1] [index + 1, 0]⟩
    (edge .centerKeyed (operation.graph :: (SupportJoin.keys component 0 arguments.length).map singleton) ::
      SupportJoin.argumentNodes component 0 (arguments.map (·.graph)))
  valid := by simp [SupportSpineAlternatives.Valid]
  spine_exact := by intro environment term; simp only [SupportSpineAlternatives.graph, SupportJoin.joinNode, List.length_map]
  closeRoots := fun _ => [
    (edge .centerKeyed (operation.graph :: (SupportJoin.keys component 0 arguments.length).map singleton) ::
      SupportJoin.argumentNodes component 0 (arguments.map (·.graph)),
      fun term => ∀ index < arguments.length, PathsEqual term [0, index + 1] [index + 1, 0])]
  close_exact := by
    intro environment symbol term
    simp only [closed, List.map_cons, List.map_nil, SupportClosing.one_exact]
    simpa only [SupportRoot.closeJoin, SupportRoot.closeEdge, List.length_map] using
      SupportRoot.closeJoin_exact environment symbol component operation.graph (arguments.map (·.graph)) term

/-- An application preserves separate left-spine alternatives and the complete argument. -/
def ap (functions argument : View Symbol) : View Symbol where
  graph := edge .apply [functions.graph, argument.graph]
  spine := .apply functions.spine argument.graph
  valid := by simpa only [SupportSpineAlternatives.Valid] using functions.valid
  spine_exact := by
    intro environment term
    simp only [SupportSpineAlternatives.graph, SupportSpine.apply_exact, functions.spine_exact]
  closeRoots := fun _ => (SupportSpineAlternatives.prefixes functions.spine).map
    (fun children => (children ++ [argument.graph], fun _ => True))
  close_exact := by
    intro environment symbol term
    have source := SupportSpineAlternatives.close_exact environment symbol functions.spine argument.graph functions.valid term
    change meaning environment (closed symbol _) term ↔ _
    have shapes : ∀ original, meaning environment (SupportSpineAlternatives.graph (.apply functions.spine argument.graph)) original ↔
        meaning environment (edge .apply [functions.graph, argument.graph]) original := by
      intro original
      simp only [SupportSpineAlternatives.graph, SupportSpine.apply_exact, functions.spine_exact]
    simpa only [closed, List.map_map, SupportSpineAlternatives.close, shapes, Function.comp_def, edge] using source

/-- Every source choice term carries the index of its complete selected body. -/
theorem choice_exact (environment : Env (Label Symbol)) (bodies : List (View Symbol)) (term : Term (Label Symbol)) :
    meaning environment (.alternatives (bodies.mapIdx fun index body => edge (.choice index) [body.graph])) term ↔
      ∃ index, ∃ inside : index < bodies.length, ∃ original,
        meaning environment bodies[index].graph original ∧ term = .node (.choice index) [original] := by
  rw [SupportClosing.alternatives_exact]
  constructor
  · rintro ⟨shape, member, accepted⟩
    obtain ⟨index, inside, rfl⟩ := List.mem_mapIdx.mp member
    obtain ⟨original, childAccepted, rfl⟩ := (SupportClosing.unary_exact _ _ _ _).mp accepted
    exact ⟨index, inside, original, childAccepted, rfl⟩
  · rintro ⟨index, inside, original, accepted, rfl⟩
    exact ⟨_, List.mem_mapIdx.mpr ⟨index, inside, rfl⟩,
      (SupportClosing.unary_exact _ _ _ _).mpr ⟨original, accepted, rfl⟩⟩

/-- Choice closing removes each private wrapper and retains all alternative roots. -/
def choice (bodies : List (View Symbol)) : View Symbol where
  graph := .alternatives (bodies.mapIdx fun index body => edge (.choice index) [body.graph])
  spine := .alternatives (bodies.mapIdx fun index body => .base ⟨.choice index, fun _ => True⟩ [body.graph])
  valid := by
    simp only [SupportSpineAlternatives.Valid]
    intro spine member
    obtain ⟨index, inside, rfl⟩ := List.mem_mapIdx.mp member
    simp [SupportSpineAlternatives.Valid]
  spine_exact := by
    intro environment term
    simp [SupportSpineAlternatives.graph, List.mapIdx_eq_zipIdx_map, List.map_map, edge, Function.comp_def]
  closeRoots := fun symbol => bodies.flatMap (fun body => body.closeRoots symbol)
  close_exact := by
    intro environment symbol term
    rw [closed]
    simp only [List.map_flatMap]
    rw [SupportClosing.alternatives_exact]
    constructor
    · rintro ⟨shape, member, accepted⟩
      obtain ⟨body, bodyMember, rootMember⟩ := List.mem_flatMap.mp member
      have closed := (SupportClosing.alternatives_exact environment _ _).mpr ⟨shape, rootMember, accepted⟩
      obtain ⟨original, accepted, same⟩ := (body.close_exact environment symbol term).mp closed
      obtain ⟨index, inside, rfl⟩ := List.mem_iff_getElem.mp bodyMember
      refine ⟨.node (.choice index) [original], ?_, ?_⟩
      · apply (choice_exact environment bodies _).mpr
        exact ⟨index, inside, original, accepted, rfl⟩
      · simpa [labelTerm] using same
    · rintro ⟨original, accepted, same⟩
      obtain ⟨index, inside, value, childAccepted, rfl⟩ := (choice_exact environment bodies original).mp accepted
      have closed := (bodies[index].close_exact environment symbol term).mpr
        ⟨value, childAccepted, by simpa [labelTerm] using same⟩
      obtain ⟨shape, rootMember, accepted⟩ := (SupportClosing.alternatives_exact _ _ _).mp closed
      exact ⟨shape, List.mem_flatMap.mpr ⟨bodies[index], List.getElem_mem inside, rootMember⟩, accepted⟩

/-- Labels execute source closing and retain the resulting user roots for later constructors. -/
def label (symbol : Symbol) (body : View Symbol) : View Symbol where
  graph := closed symbol (body.closeRoots symbol)
  spine := .alternatives ((body.closeRoots symbol).map fun root => .base ⟨.user symbol, root.2⟩ root.1)
  valid := by
    simp only [SupportSpineAlternatives.Valid]
    intro spine member
    obtain ⟨root, _, rfl⟩ := List.mem_map.mp member
    simp [SupportSpineAlternatives.Valid]
  spine_exact := by intro environment term; simp only [SupportSpineAlternatives.graph, List.map_map, closed, Function.comp_def]
  closeRoots := fun _ => [([closed symbol (body.closeRoots symbol)], fun _ => True)]
  close_exact := by
    intro environment next term
    simp only [closed, List.map_cons, List.map_nil, SupportClosing.one_exact]
    change meaning environment (edge (.user next) [closed symbol (body.closeRoots symbol)]) term ↔ _
    rw [SupportClosing.unary_exact]
    constructor <;> rintro ⟨original, accepted, same⟩
    all_goals
      obtain ⟨children, shape⟩ := closed_root environment symbol _ original accepted
      exact ⟨original, accepted, by simpa [shape, labelTerm, applicationTermChildren] using same⟩

/-- The view's explicit label constructor has exactly the source term callback image. -/
theorem label_exact (environment : Env (Label Symbol)) (symbol : Symbol) (body : View Symbol) (term : Term (Label Symbol)) :
    meaning environment (label symbol body).graph term ↔
      ∃ original, meaning environment body.graph original ∧ term = labelTerm symbol original :=
  body.close_exact environment symbol term

end MicroCFTA.RecursiveJoinSupportView
