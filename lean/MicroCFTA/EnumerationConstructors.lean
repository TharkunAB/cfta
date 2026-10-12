import MicroCFTA.EnumerationLanguage

/-!
# Constructor checks for complete enumeration

The source `mkEdge` rejects contradictory constraints and equality paths that
exceed the edge arity. Its sentinel has one empty child. The source `mkNode`
removes that sentinel with every other edge that has an empty child. These
checks derive the edge invariant required by the complete enumeration proof.
-/

namespace MicroCFTA.EnumerationConstructors
open EnumerationState EnumerationSemantics

/-- The source checks the largest root index of each equality trie. -/
def fitsArity (edge : Edge Symbol Guard) : Bool :=
  edge.equalities.all fun trie => (EqualityTrie.getMaxNonemptyIndex trie).all (· < edge.children.length)

/-- The source sentinel has one empty child and no constraints. -/
def emptyEdge (empty : Nat) (symbol : Symbol) : Edge Symbol Guard :=
  ⟨symbol, [empty], [], none⟩

/-- The source edge constructor checks contradiction and root arity. -/
def mkEdge (empty : Nat) (contradictory : Bool) (edge : Edge Symbol Guard) : Edge Symbol Guard :=
  if contradictory || !fitsArity edge then emptyEdge empty edge.symbol else edge

/-- The source node constructor removes empty children before identity deduplication. -/
def smartEdges (empty : Nat) (inputs : List (Bool × Edge Symbol Guard)) : List (Edge Symbol Guard) :=
  (inputs.map fun input => mkEdge empty input.1 input.2).filter fun edge => !edge.children.contains empty

/-- A canonical trie converts the maximum-index test into the required path bound. -/
theorem fitsArity_valid (edge : Edge Symbol Guard)
    (canonical : ∀ trie ∈ edge.equalities, EqualityTrie.Valid trie)
    (fits : fitsArity edge = true) : ValidEdge edge := by
  refine ⟨canonical, ?_⟩
  intro trie member
  exact (EqualityTrie.arity_exact trie (canonical trie member) edge.children.length).mp
    (List.all_eq_true.mp fits trie member)

/-- A retained source edge has passed the arity check. -/
theorem mkEdge_valid (empty : Nat) (contradictory : Bool) (edge : Edge Symbol Guard)
    (canonical : ∀ trie ∈ edge.equalities, EqualityTrie.Valid trie)
    (retained : empty ∉ (mkEdge empty contradictory edge).children) :
    ValidEdge (mkEdge empty contradictory edge) := by
  by_cases checks : (contradictory || !fitsArity edge) = true
  · simp only [mkEdge, checks, ↓reduceIte, emptyEdge, List.mem_singleton] at retained
    exact (retained trivial).elim
  · simp only [mkEdge, checks]
    apply fitsArity_valid edge canonical
    cases fit : fitsArity edge <;> simp_all

/-- Every row that survives the source node constructor has valid equality paths. -/
theorem smartEdges_valid (empty : Nat) (inputs : List (Bool × Edge Symbol Guard))
    (canonical : ∀ input ∈ inputs, ∀ trie ∈ input.2.equalities, EqualityTrie.Valid trie)
    (edge : Edge Symbol Guard) (member : edge ∈ smartEdges empty inputs) : ValidEdge edge := by
  obtain ⟨present, retained⟩ := List.mem_filter.mp member
  obtain ⟨input, listed, rfl⟩ := List.mem_map.mp present
  apply mkEdge_valid empty input.1 input.2 (canonical input listed)
  simpa using retained

/-- Readback can reorder and remove duplicate edge identities. It must retain exactly the surviving rows. -/
def SourceRows (empty : Nat) (edges : List (Edge Symbol Guard)) : Prop :=
  ∃ inputs : List (Bool × Edge Symbol Guard),
    (∀ input ∈ inputs, ∀ trie ∈ input.2.equalities, EqualityTrie.Valid trie) ∧
    ∀ edge, edge ∈ edges ↔ edge ∈ smartEdges empty inputs

/-- Constructor-only readback and the source checks derive the complete-graph invariant. -/
theorem complete_of_readback (graph : Graph Symbol Guard) (empty : Nat)
    (constructors : ∀ node, graph.node node = .empty ∨ ∃ edges, graph.node node = .alternatives edges)
    (rows : ∀ node edges, graph.node node = .alternatives edges → SourceRows empty edges) : CompleteGraph graph := by
  constructor
  · intro node body recursive
    rcases constructors node with view | ⟨edges, view⟩ <;> simp [view] at recursive
  · intro node edges view edge member
    obtain ⟨inputs, canonical, same⟩ := rows node edges view
    exact smartEdges_valid empty inputs canonical edge ((same edge).mp member)

/-- `setChildren` preserves edge validity when it retains the source arity. -/
theorem setChildren_valid (edge : Edge Symbol Guard) (children : List Nat)
    (same : children.length = edge.children.length) (valid : ValidEdge edge) :
    ValidEdge {edge with children := children} := by
  exact ⟨valid.1, by simpa only [same] using valid.2⟩

/-- Successful construction from supported path classes supplies the canonical trie premise. -/
theorem built_trie_valid (paths : List EqualityTrie.Path) (supported : EqualityTrie.Supported paths)
    (trie : EqualityTrie.Trie) (built : EqualityTrie.toPathTrie paths = some trie) : EqualityTrie.Valid trie := by
  obtain ⟨actual, found, valid, _⟩ := EqualityTrie.toPathTrie_correct paths supported
  have same : actual = trie := Option.some.inj (found.symm.trans built)
  simpa only [same] using valid

end MicroCFTA.EnumerationConstructors
