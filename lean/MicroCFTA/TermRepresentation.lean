import MicroCFTA.Language

/-!
# Small-arity term representation

`Data.CFTA.Term` stores arities zero through three in separate constructors.
Lists model the many-child sequence. The correspondence assumes that the
sequence implements ordered lookup. Direct `Many` construction requires four
or more children. The public `Node` builder establishes this invariant.
-/

namespace MicroCFTA.TermRepresentation

/-- The five source storage constructors. -/
inductive Packed (Symbol : Type) where
  | leaf : Symbol → Packed Symbol
  | one : Symbol → Packed Symbol → Packed Symbol
  | two : Symbol → Packed Symbol → Packed Symbol → Packed Symbol
  | three : Symbol → Packed Symbol → Packed Symbol → Packed Symbol → Packed Symbol
  | many : Symbol → List (Packed Symbol) → Packed Symbol

/-- The source `Node` builder dispatches on the number of children. -/
def node (symbol : Symbol) : List (Packed Symbol) → Packed Symbol
  | [] => .leaf symbol
  | [a] => .one symbol a
  | [a,b] => .two symbol a b
  | [a,b,c] => .three symbol a b c
  | children => .many symbol children

/-- Read the root symbol. -/
def root : Packed Symbol → Symbol
  | .leaf s | .one s _ | .two s _ _ | .three s _ _ _ | .many s _ => s

/-- Read children in their index order. -/
def children : Packed Symbol → List (Packed Symbol)
  | .leaf _ => []
  | .one _ a => [a]
  | .two _ a b => [a,b]
  | .three _ a b c => [a,b,c]
  | .many _ cs => cs

/-- Read a child with the source's small-arity dispatch. -/
def child : Packed Symbol → Nat → Option (Packed Symbol)
  | .one _ a, 0 | .two _ a _, 0 | .three _ a _ _, 0 => some a
  | .two _ _ b, 1 | .three _ _ b _, 1 => some b
  | .three _ _ _ c, 2 => some c
  | .many _ cs, i => cs[i]?
  | _, _ => none

/-- Interpret packed storage as the tree used by the language proof. -/
def unpack : Packed Symbol → Language.Term Symbol
  | .leaf s => .node s []
  | .one s a => .node s [unpack a]
  | .two s a b => .node s [unpack a, unpack b]
  | .three s a b c => .node s [unpack a, unpack b, unpack c]
  | .many s cs => .node s (cs.map unpack)

/-- Build canonical packed storage from an ordinary tree. -/
def pack : Language.Term Symbol → Packed Symbol
  | .node s cs => node s (cs.map pack)

/-- Every nested many-child node has at least four children. -/
def Valid : Packed Symbol → Prop
  | .leaf _ => True
  | .one _ a => Valid a
  | .two _ a b => Valid a ∧ Valid b
  | .three _ a b c => Valid a ∧ Valid b ∧ Valid c
  | .many _ cs => 4 ≤ cs.length ∧ ∀ t ∈ cs, Valid t

/-- Packing a child list preserves the root and the complete child list. -/
theorem node_views (s : Symbol) (cs : List (Packed Symbol)) :
    root (node s cs) = s ∧ children (node s cs) = cs := by
  cases cs with
  | nil => simp [node, root, children]
  | cons a cs => cases cs with
    | nil => simp [node, root, children]
    | cons b cs => cases cs with
      | nil => simp [node, root, children]
      | cons c cs => cases cs <;> simp [node, root, children]

/-- Direct constructor lookup has exactly the list lookup semantics. -/
theorem child_correct (t : Packed Symbol) (i : Nat) : child t i = (children t)[i]? := by
  cases t <;> cases i with
  | zero => rfl
  | succ i => cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => simp [child, children]

/-- The source builder never changes the ordinary tree. -/
theorem unpack_node (s : Symbol) (cs : List (Packed Symbol)) :
    unpack (node s cs) = .node s (cs.map unpack) := by
  cases cs with
  | nil => simp [node, unpack]
  | cons a cs => cases cs with
    | nil => simp [node, unpack]
    | cons b cs => cases cs with
      | nil => simp [node, unpack]
      | cons c cs => cases cs <;> simp [node, unpack]

/-- Canonical construction preserves the recursive arity invariant. -/
theorem node_valid (s : Symbol) (cs : List (Packed Symbol))
    (valid : ∀ t ∈ cs, Valid t) : Valid (node s cs) := by
  cases cs with
  | nil => simp [node, Valid]
  | cons a cs => cases cs with
    | nil => simpa [node, Valid] using valid a (by simp)
    | cons b cs => cases cs with
      | nil => simpa [node, Valid] using And.intro (valid a (by simp)) (valid b (by simp))
      | cons c cs => cases cs with
        | nil => simpa [node, Valid] using And.intro (valid a (by simp)) (And.intro (valid b (by simp)) (valid c (by simp)))
        | cons d ds => simp only [node, Valid]; exact ⟨by simp, valid⟩

/-- Packing followed by unpacking is the identity on every finite tree. -/
theorem unpack_pack (t : Language.Term Symbol) : unpack (pack t) = t := by
  refine Language.Term.rec (motive_1 := fun t => unpack (pack t) = t)
    (motive_2 := fun ts => (ts.map pack).map unpack = ts) ?_ ?_ ?_ t
  · intro s cs ih
    simp only [pack, unpack_node, ih]
  · rfl
  · intro a cs ha hs
    simp only [List.map_cons, ha, hs]

/-- Every tree produced by packing satisfies the storage invariant. -/
theorem pack_valid (t : Language.Term Symbol) : Valid (pack t) := by
  refine Language.Term.rec (motive_1 := fun t => Valid (pack t))
    (motive_2 := fun ts => ∀ t ∈ ts, Valid (pack t)) ?_ ?_ ?_ t
  · intro s cs ih
    simp only [pack]
    apply node_valid
    intro p member
    obtain ⟨t, ht, hp⟩ := List.mem_map.mp member
    rw [← hp]
    exact ih t ht
  · simp
  · intro a cs ha hs t member
    rcases List.mem_cons.mp member with rfl | member
    · exact ha
    · exact hs t member

/-- Reading a stored tree has the same root and children as its views. -/
theorem unpack_views (t : Packed Symbol) :
    unpack t = .node (root t) ((children t).map unpack) := by
  cases t <;> simp [unpack, root, children]

/-- Direct constructors round trip when their documented invariant holds. -/
theorem pack_unpack (t : Packed Symbol) (valid : Valid t) : pack (unpack t) = t := by
  induction t using Packed.rec (motive_2 := fun ts =>
      (∀ t ∈ ts, Valid t) → (ts.map unpack).map pack = ts) with
  | leaf s => simp [pack, unpack, node]
  | one s a ih => simp only [Valid] at valid; simp [unpack, pack, node, ih valid]
  | two s a b ia ib => simp only [Valid] at valid; simp [unpack, pack, node, ia valid.1, ib valid.2]
  | three s a b c ia ib ic => simp only [Valid] at valid; simp [unpack, pack, node, ia valid.1, ib valid.2.1, ic valid.2.2]
  | many s cs ih =>
      simp only [Valid] at valid
      simp only [unpack, pack]
      rw [ih valid.2]
      match cs with
      | [] | [_] | [_,_] | [_,_,_] => simp at valid
      | _ :: _ :: _ :: _ :: _ => simp [node]
  | nil => rfl
  | cons a cs ia ih =>
      rename_i valid
      simp only [List.map_cons, ia (valid a (by simp)), ih (fun t ht => valid t (by simp [ht]))]

/-- Equal ordinary trees have equal valid packed representations. -/
theorem unpack_injective (a b : Packed Symbol) (va : Valid a) (vb : Valid b)
    (same : unpack a = unpack b) : a = b := by
  rw [← pack_unpack a va, ← pack_unpack b vb, same]

/-- Lookup gives precisely the ordinary subtree. -/
theorem child_unpack (t : Packed Symbol) (i : Nat) :
    (child t i).map unpack = ((children t).map unpack)[i]? := by
  rw [child_correct, List.getElem?_map]

/-- Invalid direct construction breaks representation injectivity. -/
theorem invalid_many_counterexample :
    unpack (Packed.leaf (0 : Nat)) = unpack (.many 0 []) ∧
      Packed.leaf (0 : Nat) ≠ .many 0 [] ∧ ¬ Valid (Packed.many (0 : Nat) []) := by
  constructor
  · simp [unpack]
  constructor
  · intro h; cases h
  · simp [Valid]

end MicroCFTA.TermRepresentation
