import MicroCFTA.EnumerationBuilder

/-!
# Scoped language of the finite bounded builder

Readback is required only for populated memo keys. Their child closure is
proved by the executable traversal. Thus a finite cache need not represent
unrequested bounds, and equal output rows can share a canonical identity.
-/
namespace MicroCFTA.EnumerationBuilder
open Language EnumerationState EnumerationSemantics EnumerationCorrectness EnumerationSharedRows EnumerationInternedRows SymbolicGraphView

/-- Change a child relation using membership on both sides of the ordered list. -/
theorem all₂_members (before after : Left → Right → Prop) {left : List Left} {right : List Right}
    (related : All₂ before left right)
    (step : ∀ a ∈ left, ∀ b ∈ right, before a b → after a b) : All₂ after left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (step _ (by simp) _ (by simp) head)
      (ih (fun a ha b hb => step a (by simp [ha]) b (by simp [hb])))

/-- Normalized row readback is sufficient on a domain closed under source children. -/
theorem normalized_exact_on (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (scope : Source → Prop)
    (closed : ∀ state, scope state → ∀ edge ∈ source state, ∀ child ∈ edge.children, scope child)
    (keep : Source → Language.Edge Source Symbol → Bool)
    (members : ∀ state, scope state → ∀ edge, edge ∈ target (encode state) ↔
      ∃ original ∈ source state, keep state original = true ∧ edge = renameEdge encode original)
    (rejected : ∀ state, scope state → ∀ edge ∈ source state, keep state edge = false → DropReason target encode edge)
    (state : Source) (present : scope state) (term : Term Symbol) :
    Accepts target (encode state) term ↔ Accepts source state term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ state, scope state →
      (Accepts target (encode state) term ↔ Accepts source state term)) generalizing state with
  | node symbol children ih =>
    rw [accepts_node_iff, accepts_node_iff]
    constructor
    · rintro ⟨edge, member, label, runs, guard⟩
      obtain ⟨original, sourceMember, _, rfl⟩ := (members state present edge).mp member
      have mapped := (all₂_map_iff (Accepts target) encode original.children children).mp runs
      refine ⟨original, sourceMember, label, all₂_members _ _ mapped ?_, guard⟩
      intro child childMember term termMember accepted
      exact (ih term termMember child (closed state present original sourceMember child childMember)).mp accepted
    · rintro ⟨edge, member, label, runs, guard⟩
      have copied : All₂ (fun child term => Accepts target (encode child) term) edge.children children := by
        apply all₂_members _ _ runs
        intro child childMember term termMember accepted
        exact (ih term termMember child (closed state present edge member child childMember)).mpr accepted
      have retained : keep state edge = true := by
        cases choice : keep state edge with
        | true => rfl
        | false =>
          rcases rejected state present edge member choice with impossible | ⟨child, childMember, empty⟩
          · have denied := impossible (.node symbol children)
            simp [guard] at denied
          · obtain ⟨subtree, _, accepted⟩ := SymbolicSmartRows.all₂_child _ _ _ copied child childMember
            exact False.elim (empty_rows_reject target (encode child) empty subtree accepted)
      exact ⟨renameEdge encode edge, (members state present _).mpr ⟨edge, member, retained, rfl⟩,
        label, (all₂_map_iff (Accepts target) encode edge.children children).mpr copied, guard⟩
  | nil => simp_all
  | cons first rest head tail =>
    rename_i term member state present
    rcases List.mem_cons.mp member with rfl | member
    · exact head state present
    · exact tail term member state present

/-- Smart-constructor cleanup tests only the copied child row lists. -/
def keep (state : BuildState Symbol Guard) (_ : Key) (edge : Language.Edge Key Other) : Bool :=
  edge.children.all (fun child => !(lookup state.cache (encode state child)).isEmpty)

/-- A populated memo domain is closed under the bounded source graph. -/
theorem scope_closed (source : Nat → RowKey Symbol Guard) (state : BuildState Symbol Guard)
    (valid : Valid source state) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (present : Scope state key)
    (edge : Language.Edge Key Symbol)
    (member : edge ∈ BoundDepth.bound (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key)
    (child : Key) (childMember : child ∈ edge.children) : Scope state child := by
  apply valid.ready key present child
  obtain ⟨height, node⟩ := key
  cases height with
  | zero => simp [BoundDepth.bound] at member
  | succ remaining =>
    obtain ⟨base, filtered, rfl⟩ := List.mem_map.mp member
    obtain ⟨mapped, shallowMember⟩ := List.mem_filter.mp filtered
    obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp mapped
    obtain ⟨originalChild, inside, rfl⟩ := List.mem_map.mp childMember
    exact child_dependency source remaining node original
      (List.mem_filter.mpr ⟨sourceMember, shallowMember⟩) originalChild inside

/-- Final constructor rows are exactly the surviving renamed bounded source rows. -/
theorem scoped_members (source : Nat → RowKey Symbol Guard) (state : BuildState Symbol Guard)
    (valid : Valid source state) (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (present : Scope state key) (edge : Language.Edge Nat Symbol) :
    edge ∈ EnumerationLanguage.automaton (graph state.cache meet) meaning (encode state key) ↔
      ∃ original ∈ BoundDepth.bound (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key,
        keep state key original = true ∧ edge = renameEdge (encode state) original := by
  obtain ⟨identity, found⟩ := present
  have readback : lookup state.cache (encode state key) =
      construct (encode state) (lookup state.cache) source key.1 key.2 := by
    simpa [encode, found] using valid.readback key identity found
  rw [automaton_rows, graph_rows, readback]
  obtain ⟨height, node⟩ := key
  cases height with
  | zero => simp [construct, BoundDepth.bound]
  | succ remaining =>
    constructor
    · intro member
      obtain ⟨bounded, listed, rfl⟩ := List.mem_map.mp member
      obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp listed
      obtain ⟨sourceFiltered, childrenKept⟩ := List.mem_filter.mp filtered
      obtain ⟨sourceMember, shallowMember⟩ := List.mem_filter.mp sourceFiltered
      refine ⟨BoundDepth.copyEdge remaining (EnumerationLanguage.edgeView meaning original), ?_, ?_,
        EnumerationBoundedRows.copy_view _ _ _ _⟩
      · exact List.mem_map.mpr ⟨EnumerationLanguage.edgeView meaning original,
          List.mem_filter.mpr ⟨List.mem_map.mpr ⟨original, sourceMember, rfl⟩, shallowMember⟩, rfl⟩
      · simpa [keep, BoundDepth.copyEdge, EnumerationLanguage.edgeView, List.all_map, Function.comp_def] using childrenKept
    · rintro ⟨original, member, kept, rfl⟩
      obtain ⟨base, filtered, rfl⟩ := List.mem_map.mp member
      obtain ⟨mapped, shallowMember⟩ := List.mem_filter.mp filtered
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp mapped
      rw [← EnumerationBoundedRows.copy_view]
      apply List.mem_map.mpr
      refine ⟨EnumerationBoundedRows.copyEdge (encode state) remaining original, ?_, rfl⟩
      apply List.mem_map.mpr
      refine ⟨original, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨sourceMember, shallowMember⟩, ?_⟩, rfl⟩
      simpa [keep, BoundDepth.copyEdge, EnumerationLanguage.edgeView, List.all_map, Function.comp_def] using kept

/-- A rejected row contains an empty final child, so no complete term is lost. -/
theorem scoped_rejected (state : BuildState Symbol Guard) (meet : Nat → Nat → Nat)
    (meaning : Guard → Term Symbol → Prop) (key : Key) (edge : Language.Edge Key Symbol)
    (rejected : keep state key edge = false) :
    DropReason (EnumerationLanguage.automaton (graph state.cache meet) meaning) (encode state) edge := by
  have empty : ∃ child ∈ edge.children, lookup state.cache (encode state child) = [] := by
    simpa [keep] using rejected
  obtain ⟨child, member, absent⟩ := empty
  exact Or.inr ⟨child, member, by simp [automaton_rows, graph_rows, absent]⟩

/-- Every populated key has exactly its original language below the requested height. -/
theorem scoped_accepted_exact (source : Nat → RowKey Symbol Guard) (state : BuildState Symbol Guard)
    (valid : Valid source state) (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (present : Scope state key) (term : Term Symbol) :
    Accepted (graph state.cache meet) meaning (encode state key) term ↔
      Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1 := by
  rw [EnumerationLanguage.accepted_iff _ _ (complete state.cache meet valid.stored)]
  exact (normalized_exact_on
    (BoundDepth.bound (fun node => (source node).map (EnumerationLanguage.edgeView meaning)))
    (EnumerationLanguage.automaton (graph state.cache meet) meaning) (encode state) (Scope state)
    (scope_closed source state valid meaning) (keep state)
    (scoped_members source state valid meet meaning)
    (fun _ _ _ _ rejected => scoped_rejected state meet meaning _ _ rejected) key present term).trans
    (BoundDepth.bound_exact _ key.1 key.2 term)

/-- A finite executable batch derives complete requested-root language equivalence. -/
theorem requested_accepted_exact [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge) (requests : List Key)
    (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (member : key ∈ requests) (term : Term Symbol) :
    Accepted (graph (buildAll source requests).cache meet) meaning (encode (buildAll source requests) key) term ↔
      Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1 := by
  obtain ⟨valid, reached⟩ := buildAll_correct source sourceValid requests
  exact scoped_accepted_exact source _ valid meet meaning key (reached key member) term

/-- The actual enumeration driver has exact finite support at every requested built root. -/
theorem requested_runs_exact [DecidableEq Symbol] [DecidableEq (RowKey Symbol Guard)]
    (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge) (requests : List Key)
    (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (intersection : EnumerationIntersection.HashRows
      (EnumerationLanguage.automaton (graph (buildAll source requests).cache meet) meaning) meet)
    (marker : Symbol) (key : Key) (member : key ∈ requests) (term : Term Symbol) :
    (Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1) ↔
      ∃ fuel pending after, .ok ((term, pending), after) ∈
        runs (graph (buildAll source requests).cache meet) marker fuel (encode (buildAll source requests) key) ∧
        ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  have complete := complete (buildAll source requests).cache meet (buildAll_correct source sourceValid requests).1.stored
  rw [← requested_accepted_exact source sourceValid requests meet meaning key member term]
  exact EnumerationExact.runs_exact _ meaning complete
    (EnumerationIntersection.intersection_correct _ meaning complete intersection) marker _ term

end MicroCFTA.EnumerationBuilder
