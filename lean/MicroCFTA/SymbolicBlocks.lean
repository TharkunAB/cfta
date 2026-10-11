import MicroCFTA.SymbolicDecoderTotal

/-!
# Exact constructor-block partitions and child selection bounds

Distinct constructor tags form disjoint finite languages. Coverage of every
existing subtree makes their cardinalities sum to the complete root language.
Conditioning preserves pending subtree height bounds at all child positions.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- Every accepted subtree at a position is bounded by a finite height. -/
def SubtreeHeight (meaning : FiniteMeaning graph) (root : Nat) (path : List Nat) (height : Nat) : Prop :=
  ∀ whole ∈ meaning.terms root, ∀ part, whole.atPath path = some part → part.height ≤ height

/-- Add the exact finite cardinalities of the remaining constructor blocks. -/
def blockCount (graph : Graph Symbol) (meaning : FiniteMeaning graph) (root : Nat) (path : List Nat)
    (constructors : List (Symbol × Nat)) : Nat :=
  (constructors.map fun constructor => (meaning.terms (graph.condition path constructor root)).length).sum

/-- A term cannot occupy two different constructor blocks at the same position. -/
theorem condition_disjoint (graph : Graph Symbol) (meaning : FiniteMeaning graph) (root : Nat) (path : List Nat)
    (first second : Symbol × Nat) (different : first ≠ second) (term : Term Symbol)
    (left : term ∈ meaning.terms (graph.condition path first root))
    (right : term ∈ meaning.terms (graph.condition path second root)) : False := by
  obtain ⟨_, children, firstFound, firstArity⟩ := (meaning.condition path first.1 first.2 root term).mp left
  obtain ⟨_, others, secondFound, secondArity⟩ := (meaning.condition path second.1 second.2 root term).mp right
  have same := Term.node.inj (Option.some.inj (firstFound.symm.trans secondFound))
  exact different (Prod.ext same.1 (firstArity.symm.trans ((congrArg List.length same.2).trans secondArity)))

/-- Concatenating distinct constructor blocks contains no duplicate term. -/
theorem constructor_blocks_nodup (graph : Graph Symbol) (meaning : FiniteMeaning graph) (root : Nat) (path : List Nat)
    (constructors : List (Symbol × Nat)) (distinct : constructors.Nodup) :
    (constructors.flatMap fun constructor => meaning.terms (graph.condition path constructor root)).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro constructor _
    exact meaning.distinct (graph.condition path constructor root)
  · apply distinct.imp
    intro first second different left leftMember right rightMember same
    subst right
    exact condition_disjoint graph meaning root path first second different left leftMember rightMember

/-- Complete constructor coverage partitions the finite root language exactly. -/
theorem constructor_blocks_count (graph : Graph Symbol) (meaning : FiniteMeaning graph) (root : Nat) (path : List Nat)
    (constructors : List (Symbol × Nat)) (distinct : constructors.Nodup) (existsPath : PathExists meaning root path)
    (covered : ∀ whole ∈ meaning.terms root, ∀ symbol children,
      whole.atPath path = some (.node symbol children) → (symbol, children.length) ∈ constructors) :
    blockCount graph meaning root path constructors = (meaning.terms root).length := by
  let blocks := constructors.flatMap fun constructor => meaning.terms (graph.condition path constructor root)
  have firstSubset : blocks ⊆ meaning.terms root := by
    intro term member
    obtain ⟨constructor, _, accepted⟩ := List.mem_flatMap.mp member
    exact ((meaning.condition path constructor.1 constructor.2 root term).mp accepted).1
  have secondSubset : meaning.terms root ⊆ blocks := by
    intro whole member
    obtain ⟨part, located⟩ := existsPath whole member
    cases part with
    | node symbol children =>
        apply List.mem_flatMap.mpr
        refine ⟨(symbol, children.length), covered whole member symbol children located, ?_⟩
        exact (meaning.condition path symbol children.length root whole).mpr ⟨member, children, located, rfl⟩
  have equalLength : blocks.length = (meaning.terms root).length :=
    Nat.le_antisymm (List.Nodup.length_le_of_subset (constructor_blocks_nodup graph meaning root path constructors distinct) firstSubset)
      (List.Nodup.length_le_of_subset (meaning.distinct root) secondSubset)
  simpa only [blocks, List.length_flatMap, blockCount] using equalLength

/-- The literal source candidate list partitions every accepted existing position. -/
theorem constructorsAt_count [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (coverage : ConstructorCoverage graph order meaning) (root : Nat) (path : List Nat)
    (existsPath : PathExists meaning root path) :
    blockCount graph meaning root path (constructorsAt graph order path root) = (meaning.terms root).length :=
  constructor_blocks_count graph meaning root path _ (constructorsAt_nodup graph order path root) existsPath
    (fun whole member symbol children found => coverage root path whole symbol children member found)

/-- A selected subset retains all existing paths from the previous candidate graph. -/
theorem pathExists_subset (meaning : FiniteMeaning graph) (first second : Nat) (subset : GraphSubset meaning first second)
    (path : List Nat) (existsPath : PathExists meaning second path) : PathExists meaning first path :=
  fun whole member => existsPath whole (subset whole member)

/-- A selected subset retains every finite height bound from the previous candidate graph. -/
theorem subtreeHeight_subset (meaning : FiniteMeaning graph) (first second : Nat) (subset : GraphSubset meaning first second)
    (path : List Nat) (height : Nat) (bounded : SubtreeHeight meaning second path height) : SubtreeHeight meaning first path height :=
  fun whole member part found => bounded whole (subset whole member) part found

/-- Every child of the selected constructor has an existing path and a strictly smaller height bound. -/
theorem conditioned_child_height (graph : Graph Symbol) (meaning : FiniteMeaning graph) (root : Nat) (path : List Nat)
    (constructor : Symbol × Nat) (height : Nat) (bounded : SubtreeHeight meaning root path height)
    (index : Nat) (indexBound : index < constructor.2) :
    PathExists meaning (graph.condition path constructor root) (path ++ [index]) ∧
      SubtreeHeight meaning (graph.condition path constructor root) (path ++ [index]) (height - 1) := by
  constructor
  · intro whole member
    obtain ⟨_, children, located, arity⟩ := (meaning.condition path constructor.1 constructor.2 root whole).mp member
    have valid : index < children.length := by omega
    refine ⟨children[index], ?_⟩
    simp only [atPath_append, located, Option.bind_some, Term.atPath, List.getElem?_eq_getElem valid, Option.bind_some]
  · intro whole member part found
    obtain ⟨original, children, located, arity⟩ := (meaning.condition path constructor.1 constructor.2 root whole).mp member
    have parentBound := bounded whole original (.node constructor.1 children) located
    have valid : index < children.length := by omega
    have partSame : part = children[index] := by
      simp only [atPath_append, located, Option.bind_some, Term.atPath, List.getElem?_eq_getElem valid] at found
      exact Option.some.inj found.symm
    subst part
    have childBound := height_le_forestHeight children children[index] (List.getElem_mem valid)
    simp only [Term.height, forestHeight] at parentBound childBound
    omega

/-- An in-range rank at an existing position gives a positive available subtree height. -/
theorem subtreeHeight_positive (meaning : FiniteMeaning graph) (root : Nat) (path : List Nat) (height : Nat)
    (nonempty : 0 < (meaning.terms root).length) (existsPath : PathExists meaning root path)
    (bounded : SubtreeHeight meaning root path height) : 0 < height := by
  obtain ⟨whole, member⟩ := List.length_pos_iff_exists_mem.mp nonempty
  obtain ⟨part, located⟩ := existsPath whole member
  have bound := bounded whole member part located
  have positive := Term.height_pos part
  omega

end MicroCFTA.SymbolicDriver
