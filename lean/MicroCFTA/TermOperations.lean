import MicroCFTA.TermRepresentation

/-!
# Packed-term updates, folds, and preorder traversal

The direct constructor cases follow `Data.CFTA.Term`. Finite lists implement
the many-child sequence. Negative child indices retain the source behavior.
-/

namespace MicroCFTA.TermOperations
open TermRepresentation

/-- Sequence adjustment preserves every position except the requested child. -/
def adjustList (f : α → α) : Nat → List α → List α
  | _, [] => []
  | 0, child :: rest => f child :: rest
  | index + 1, child :: rest => child :: adjustList f index rest

/-- The source updates small-arity fields without constructing a child list. -/
def adjust (f : Packed Symbol → Packed Symbol) : Nat → Packed Symbol → Packed Symbol
  | 0, .one symbol a => .one symbol (f a)
  | 0, .two symbol a b => .two symbol (f a) b
  | 1, .two symbol a b => .two symbol a (f b)
  | 0, .three symbol a b c => .three symbol (f a) b c
  | 1, .three symbol a b c => .three symbol a (f b) c
  | 2, .three symbol a b c => .three symbol a b (f c)
  | index, .many symbol children => .many symbol (adjustList f index children)
  | _, term => term

/-- Signed lookup rejects a negative index before converting to a natural. -/
def signedChild (index : Int) (term : Packed Symbol) : Option (Packed Symbol) :=
  if index < 0 then none else child term index.toNat

/-- Signed adjustment leaves a negative or out-of-range position unchanged. -/
def signedAdjust (f : Packed Symbol → Packed Symbol) (index : Int) (term : Packed Symbol) : Packed Symbol :=
  if index < 0 then term else adjust f index.toNat term

/-- The storage optimization has exactly the ordered-list adjustment semantics. -/
theorem adjust_children (f : Packed Symbol → Packed Symbol) (index : Nat) (term : Packed Symbol) :
    children (adjust f index term) = adjustList f index (children term) := by
  cases term <;> cases index with
  | zero => rfl
  | succ index => cases index with
    | zero => rfl
    | succ index => cases index with
      | zero => rfl
      | succ index => simp [adjust, children, adjustList]

/-- Adjustment does not change the root symbol. -/
theorem adjust_root (f : Packed Symbol → Packed Symbol) (index : Nat) (term : Packed Symbol) :
    root (adjust f index term) = root term := by
  cases term <;> cases index with
  | zero => rfl
  | succ index => cases index with
    | zero => rfl
    | succ index => cases index <;> simp [adjust, root]

/-- Updating one position cannot add or drop a child. -/
theorem adjustList_length (f : α → α) (index : Nat) (items : List α) :
    (adjustList f index items).length = items.length := by
  induction items generalizing index with
  | nil => simp [adjustList]
  | cons first rest ih => cases index <;> simp [adjustList, ih]

/-- Packed adjustment preserves the arity, including the sequence case. -/
theorem adjust_arity (f : Packed Symbol → Packed Symbol) (index : Nat) (term : Packed Symbol) :
    (children (adjust f index term)).length = (children term).length := by
  rw [adjust_children, adjustList_length]

/-- Every other lookup is unchanged; the selected lookup receives the function. -/
theorem adjustList_lookup (f : α → α) (index query : Nat) (items : List α) :
    (adjustList f index items)[query]? =
      if query = index then (items[query]?).map f else items[query]? := by
  induction items generalizing index query with
  | nil => simp [adjustList]
  | cons first rest ih =>
      cases index <;> cases query <;> simp [adjustList, ih]

/-- The source child lookup observes precisely the requested update. -/
theorem adjust_lookup (f : Packed Symbol → Packed Symbol) (index query : Nat) (term : Packed Symbol) :
    child (adjust f index term) query =
      if query = index then (child term query).map f else child term query := by
  simp only [child_correct, adjust_children, adjustList_lookup]

/-- Invalid high indices are no-ops. -/
theorem adjustList_outside (f : α → α) (index : Nat) (items : List α)
    (outside : items.length ≤ index) : adjustList f index items = items := by
  induction items generalizing index with
  | nil => simp [adjustList]
  | cons first rest ih =>
      cases index with
      | zero => simp at outside
      | succ index => simp only [adjustList]; rw [ih index (by simpa using outside)]

/-- The source sequence update preserves every child invariant. -/
theorem adjustList_valid (property : α → Prop) (f : α → α)
    (preserves : ∀ value, property value → property (f value))
    (index : Nat) (items : List α) (valid : ∀ value ∈ items, property value) :
    ∀ value ∈ adjustList f index items, property value := by
  induction items generalizing index with
  | nil => simp [adjustList]
  | cons first rest ih =>
      cases index with
      | zero =>
          simpa [adjustList] using (And.intro
            (preserves first (valid first (by simp))) (fun value member => valid value (by simp [member])))
      | succ index =>
          simpa [adjustList] using (And.intro (valid first (by simp))
            (ih index (fun value member => valid value (by simp [member]))))

/-- Valid packed children remain valid after the field update. -/
theorem adjust_valid (f : Packed Symbol → Packed Symbol)
    (preserves : ∀ term, Valid term → Valid (f term))
    (index : Nat) (term : Packed Symbol) (valid : Valid term) : Valid (adjust f index term) := by
  cases term with
  | leaf symbol => cases index <;> simp [adjust, Valid]
  | one symbol a => cases index <;> simp_all [adjust, Valid]
  | two symbol a b => cases index with
    | zero => simp_all [adjust, Valid]
    | succ index => cases index <;> simp_all [adjust, Valid]
  | three symbol a b c => cases index with
    | zero => simp_all [adjust, Valid]
    | succ index => cases index with
      | zero => simp_all [adjust, Valid]
      | succ index => cases index <;> simp_all [adjust, Valid]
  | many symbol cs =>
      simp only [Valid] at valid
      simp only [adjust, Valid]
      exact ⟨by simpa [adjustList_length] using valid.1,
        adjustList_valid Valid f preserves index cs valid.2⟩

mutual
  /-- Source preorder traversal with an explicit output suffix. -/
  def flattenAcc : Packed Symbol → List Symbol → List Symbol
    | .leaf symbol, rest => symbol :: rest
    | .one symbol a, rest => symbol :: flattenAcc a rest
    | .two symbol a b, rest => symbol :: flattenAcc a (flattenAcc b rest)
    | .three symbol a b c, rest => symbol :: flattenAcc a (flattenAcc b (flattenAcc c rest))
    | .many symbol children, rest => symbol :: flattenChildren children rest

  /-- Source right fold over the many-child sequence. -/
  def flattenChildren : List (Packed Symbol) → List Symbol → List Symbol
    | [], rest => rest
    | child :: children, rest => flattenAcc child (flattenChildren children rest)
end

/-- Independent preorder of an ordinary term. -/
def preorder : Language.Term Symbol → List Symbol
  | .node symbol children => symbol :: children.flatMap preorder

/-- The optimized traversal preserves every symbol in preorder. -/
theorem flatten_exact (term : Packed Symbol) (rest : List Symbol) :
    flattenAcc term rest = preorder (unpack term) ++ rest := by
  induction term using Packed.rec
    (motive_2 := fun children => ∀ rest, flattenChildren children rest =
      ((children.map unpack).flatMap preorder) ++ rest) generalizing rest with
  | leaf symbol => simp [flattenAcc, preorder, unpack]
  | one symbol a ih => simp [flattenAcc, unpack, preorder, ih]
  | two symbol a b ia ib => simp [flattenAcc, unpack, preorder, ia, ib, List.append_assoc]
  | three symbol a b c ia ib ic => simp [flattenAcc, unpack, preorder, ia, ib, ic, List.append_assoc]
  | many symbol children ih => simp [flattenAcc, unpack, preorder, ih]
  | nil => rfl
  | cons child children first tail => simp [flattenChildren, first, tail, List.append_assoc]

mutual
  /-- The source bottom-up fold, with direct storage dispatch. -/
  def fold (combine : Symbol → List Value → Value) : Packed Symbol → Value
    | .leaf symbol => combine symbol []
    | .one symbol a => combine symbol [fold combine a]
    | .two symbol a b => combine symbol [fold combine a, fold combine b]
    | .three symbol a b c => combine symbol [fold combine a, fold combine b, fold combine c]
    | .many symbol children => combine symbol (foldChildren combine children)

  /-- Fold all children without changing their order. -/
  def foldChildren (combine : Symbol → List Value → Value) : List (Packed Symbol) → List Value
    | [] => []
    | child :: rest => fold combine child :: foldChildren combine rest
end

/-- Reference rose-tree fold. -/
def foldReference (combine : Symbol → List Value → Value) : Language.Term Symbol → Value
  | .node symbol children => combine symbol (children.map (foldReference combine))

/-- Every bottom-up user fold agrees with the ordinary tree fold. -/
theorem fold_exact (combine : Symbol → List Value → Value) (term : Packed Symbol) :
    fold combine term = foldReference combine (unpack term) := by
  induction term using Packed.rec
    (motive_2 := fun children => foldChildren combine children =
      (children.map unpack).map (foldReference combine)) with
  | leaf symbol => simp [fold, foldReference, unpack]
  | one symbol a ih => simp [fold, foldReference, unpack, ih]
  | two symbol a b ia ib => simp [fold, foldReference, unpack, ia, ib]
  | three symbol a b c ia ib ic => simp [fold, foldReference, unpack, ia, ib, ic]
  | many symbol children ih => simp [fold, foldReference, unpack, ih]
  | nil => rfl
  | cons child children first tail => simp [foldChildren, first, tail]

end MicroCFTA.TermOperations
