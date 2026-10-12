import MicroCFTA.Language

/-!
# Symbol relabelling and constraint transport

Graph copying retains state references and changes each edge symbol.
Preserving a guard is a separate requirement. Path equality satisfies that
requirement for injective symbol maps. Arbitrary symbol erasure does not.
-/
namespace MicroCFTA.SymbolRelabel
open Language

/-- Copy every symbol without changing the ordered tree shape. -/
def termMap (rename : Symbol → Other) : Term Symbol → Term Other
  | .node symbol children => .node (rename symbol) (children.map (termMap rename))

/-- An injective symbol map remains injective on complete finite terms. -/
theorem termMap_injective (rename : Symbol → Other) (injective : ∀ a b, rename a = rename b → a = b)
    (left right : Term Symbol) (same : termMap rename left = termMap rename right) : left = right := by
  induction left using Term.rec
    (motive_2 := fun children => ∀ others,
      children.map (termMap rename) = others.map (termMap rename) → children = others)
    generalizing right with
  | node symbol children ih =>
    cases right with
    | node other others =>
      simp only [termMap, Term.node.injEq] at same
      rw [injective _ _ same.1, ih others same.2]
  | nil => rename_i others same; cases others <;> simp_all
  | cons first rest ih ir =>
    rename_i others same
    cases others with
    | nil => simp at same
    | cons other others =>
      simp only [List.map_cons, List.cons.injEq] at same
      rw [ih other same.1, ir others same.2]

/-- Relabelling commutes with successful and failed path lookup. -/
theorem path_map (rename : Symbol → Other) (term : Term Symbol) (path : List Nat) :
    (termMap rename term).atPath path = (term.atPath path).map (termMap rename) := by
  induction path generalizing term with
  | nil => simp [Term.atPath]
  | cons index rest ih =>
    cases term with
    | node symbol children =>
      simp only [termMap, Term.atPath, List.getElem?_map]
      cases found : children[index]? with
      | none => simp
      | some child => simpa using ih child

/-- Existing equal subtrees remain equal under every symbol map. -/
theorem equality_forward (rename : Symbol → Other) (term : Term Symbol) (left right : List Nat)
    (equal : PathsEqual term left right) : PathsEqual (termMap rename term) left right := by
  obtain ⟨value, first, second⟩ := equal
  exact ⟨termMap rename value, by simp [path_map, first], by simp [path_map, second]⟩

/-- Injective relabelling neither introduces nor removes a path equality. -/
theorem equality_exact (rename : Symbol → Other) (injective : ∀ a b, rename a = rename b → a = b)
    (term : Term Symbol) (left right : List Nat) :
    PathsEqual (termMap rename term) left right ↔ PathsEqual term left right := by
  constructor
  · rintro ⟨value, first, second⟩
    rw [path_map] at first second
    obtain ⟨a, atLeft, first⟩ := Option.map_eq_some_iff.mp first
    obtain ⟨b, atRight, second⟩ := Option.map_eq_some_iff.mp second
    have same := termMap_injective rename injective a b (first.trans second.symm)
    exact ⟨a, atLeft, same ▸ atRight⟩
  · exact equality_forward rename term left right

/-- The executable equality test also commutes with an injective symbol map. -/
theorem equality_guard [DecidableEq Symbol] [DecidableEq Other]
    (rename : Symbol → Other) (injective : ∀ a b, rename a = rename b → a = b)
    (left right : List Nat) (term : Term Symbol) :
    pathEquality left right (termMap rename term) = pathEquality left right term := by
  apply Bool.eq_iff_iff.mpr
  rw [pathEquality_correct, pathEquality_correct, equality_exact rename injective]

/-- A finite conjunction of the source path-equality tests. -/
def tests [DecidableEq Symbol] (constraints : List (List Nat × List Nat)) (term : Term Symbol) : Bool :=
  constraints.all (fun pair => pathEquality pair.1 pair.2 term)

/-- Injective relabelling preserves every finite conjunction of path equalities. -/
theorem tests_exact [DecidableEq Symbol] [DecidableEq Other]
    (rename : Symbol → Other) (injective : ∀ a b, rename a = rename b → a = b)
    (constraints : List (List Nat × List Nat)) (term : Term Symbol) :
    tests constraints (termMap rename term) = tests constraints term := by
  simp only [tests, equality_guard rename injective]

/-- Copy one complete row, including its transported constraint. -/
def copyEdge (rename : Symbol → Other) (guards : Edge State Symbol → Term Other → Bool)
    (source : Edge State Symbol) : Edge State Other :=
  ⟨rename source.label, source.children, guards source⟩

/-- Copy every edge while retaining its state and child references. -/
def graphMap (rename : Symbol → Other) (guards : Edge State Symbol → Term Other → Bool)
    (source : Automaton State Symbol) : Automaton State Other :=
  fun state => (source state).map (copyEdge rename guards)

/-- A local constraint transport requirement, only on rows that occur in the source. -/
def GuardLaw (rename : Symbol → Other) (guards : Edge State Symbol → Term Other → Bool)
    (source : Automaton State Symbol) : Prop :=
  ∀ state edge, edge ∈ source state → ∀ term, guards edge (termMap rename term) = edge.guard term

/-- Graph copying preserves every finite accepting run. -/
theorem graph_forward (rename : Symbol → Other) (guards : Edge State Symbol → Term Other → Bool)
    (source : Automaton State Symbol) (law : GuardLaw rename guards source)
    (state : State) (term : Term Symbol) (accepted : Accepts source state term) :
    Accepts (graphMap rename guards source) state (termMap rename term) := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => All₂ (Accepts (graphMap rename guards source)) states (terms.map (termMap rename))) with
  | @node state edge children member runs guard ih =>
    simp only [termMap]
    apply Accepts.node (copyEdge rename guards edge) _
    · exact List.mem_map.mpr ⟨edge, member, rfl⟩
    · exact ih
    · have transported := law state edge member (.node edge.label children)
      simp only [termMap] at transported
      exact transported.trans guard
  | nil => exact .nil
  | cons head tail ih it => exact .cons ih it

/-- Every run in the copied graph comes from an original finite run. -/
theorem graph_backward (rename : Symbol → Other) (guards : Edge State Symbol → Term Other → Bool)
    (source : Automaton State Symbol) (law : GuardLaw rename guards source)
    (state : State) (term : Term Other) (accepted : Accepts (graphMap rename guards source) state term) :
    ∃ original, Accepts source state original ∧ term = termMap rename original := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => ∃ originals, All₂ (Accepts source) states originals ∧ terms = originals.map (termMap rename)) with
  | @node state copied children member runs guard ih =>
    obtain ⟨edge, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨originals, originalRuns, rfl⟩ := ih
    refine ⟨.node edge.label originals, ?_, by simp [termMap, copyEdge]⟩
    apply Accepts.node edge originals inputMember originalRuns
    have transported := law state edge inputMember (.node edge.label originals)
    simp only [termMap] at transported
    exact transported.symm.trans guard
  | nil => exact ⟨[], .nil, rfl⟩
  | cons head tail ih it =>
    obtain ⟨original, run, rfl⟩ := ih
    obtain ⟨originals, runs, rfl⟩ := it
    exact ⟨original :: originals, .cons run runs, rfl⟩

/-- Cyclic graph copying has exactly the image language under the local guard law. -/
theorem graph_exact (rename : Symbol → Other) (guards : Edge State Symbol → Term Other → Bool)
    (source : Automaton State Symbol) (law : GuardLaw rename guards source) (state : State) (term : Term Other) :
    Accepts (graphMap rename guards source) state term ↔
      ∃ original, Accepts source state original ∧ term = termMap rename original :=
  ⟨graph_backward rename guards source law state term,
    fun ⟨original, accepted, same⟩ => same ▸ graph_forward rename guards source law state original accepted⟩

/-- Collapsing two symbols can make a previously false equality true. -/
theorem noninjective_changes_equality :
    let input : Term Bool := .node false [.node false [], .node true []]
    ¬PathsEqual input [0] [1] ∧ PathsEqual (termMap (fun _ => ()) input) [0] [1] := by
  simp [PathsEqual, termMap, Term.atPath]

end MicroCFTA.SymbolRelabel
