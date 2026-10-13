import MicroCFTA.InternedFreeNameSemantics

/-!
# Pure depth semantics with root and deep references

Root alternatives and references below an ordinary or Mu boundary have
different effects on smart cleanup. A fresh symbolic local can retain a
smart binder only through a deep occurrence. This interpretation records
both sets separately. Source cache correspondence is a separate obligation.
-/
namespace MicroCFTA.InternedDepthSemantics
open InternedNestedConstruction

/-- A source shape keeps root alternatives, deep names, opacity, and Mu depth. -/
structure Shape (Atom : Type) where
  roots : List Atom := []
  deep : List Atom := []
  hasOpaque : Bool := false
  depth : Nat := 0

/-- Renaming changes names and preserves the shape and cached depth. -/
def Shape.map (function : Atom → Other) (value : Shape Atom) : Shape Other :=
  ⟨value.roots.map function, value.deep.map function, value.hasOpaque, value.depth⟩

/-- Free names comprise both root and deep occurrences. -/
def Shape.free (value : Shape Atom) : List Atom := value.roots ++ value.deep

/-- An empty shape has no opaque alternative and no literal root. -/
def Shape.isEmpty (value : Shape Atom) : Bool := !value.hasOpaque && value.roots.isEmpty

/-- Combine source union operands without selecting canonical identities. -/
def combine (first second : Shape Atom) : Shape Atom :=
  ⟨first.roots ++ second.roots, first.deep ++ second.deep,
    first.hasOpaque || second.hasOpaque, max first.depth second.depth⟩

/-- Combine all ordered child or union shapes. -/
def combineMany : List (Shape Atom) → Shape Atom
  | [] => {}
  | first :: rest => combine first (combineMany rest)

/-- A surviving ordinary edge makes every child occurrence deep. -/
def edge (children : List (Shape Atom)) : Shape Atom :=
  if children.any Shape.isEmpty then {}
  else ⟨[], (combineMany children).free, true, (combineMany children).depth⟩

/-- Detect the symbolic local without comparing external names. -/
def hasLocal (names : List (Sum Unit Atom)) : Bool :=
  names.any (fun name => match name with | .inl _ => true | .inr _ => false)

/-- Remove the symbolic local when leaving its source binder. -/
def lower (names : List (Sum Unit Atom)) : List Atom := InternedFreeNameSemantics.lower names

/-- Raw binders always add depth; smart binders need a deep local occurrence. -/
def binder (smart : Bool) (body : Shape (Sum Unit Atom)) : Shape Atom :=
  if !smart || hasLocal body.deep then
    ⟨[], lower body.free, true, body.depth + 1⟩
  else ⟨lower body.roots, lower body.deep, body.hasOpaque, body.depth⟩

mutual
/-- Interpret source syntax with fresh symbolic locals and no canonical cache. -/
def evaluate {Atom : Type} (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) : Shape Atom :=
  match expression with
  | .empty => {}
  | .var index => environment[index]?.getD {}
  | .node edges => evaluateEdges edges environment
  | .union members => combineMany (evaluateMany members environment)
  | .binder smart body => binder smart (evaluate body
      (⟨[.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)))
termination_by sizeOf expression

/-- Evaluate every source child in its original order. -/
def evaluateMany {Atom : Type} (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom)) : List (Shape Atom) :=
  match expressions with
  | [] => []
  | first :: rest => evaluate first environment :: evaluateMany rest environment
termination_by sizeOf expressions

/-- Empty children erase one edge's shape while other edges remain available. -/
def evaluateEdges {Atom : Type} (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom)) : Shape Atom :=
  match expressions with
  | [] => {}
  | .mk _ _ children :: rest => combine (edge (evaluateMany children environment)) (evaluateEdges rest environment)
termination_by sizeOf expressions
end

/-- External renaming preserves emptiness. -/
theorem isEmpty_map (function : Atom → Other) (value : Shape Atom) :
    (value.map function).isEmpty = value.isEmpty := by
  simp [Shape.isEmpty, Shape.map]

/-- External renaming commutes with a shape union. -/
theorem combine_map (function : Atom → Other) (first second : Shape Atom) :
    combine (first.map function) (second.map function) = (combine first second).map function := by
  simp [combine, Shape.map]

/-- External renaming commutes with all ordered operands. -/
theorem combineMany_map (function : Atom → Other) (values : List (Shape Atom)) :
    combineMany (values.map (Shape.map function)) = (combineMany values).map function := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, combineMany, ih, combine_map]

/-- Renaming preserves edge survival and maps its deep free names. -/
theorem edge_map (function : Atom → Other) (children : List (Shape Atom)) :
    edge (children.map (Shape.map function)) = (edge children).map function := by
  simp only [edge, List.any_map, Function.comp_def, isEmpty_map, combineMany_map]
  split <;> simp [Shape.map, Shape.free]

/-- A map of external names preserves every occurrence of the distinct local. -/
theorem hasLocal_map (function : Atom → Other) (names : List (Sum Unit Atom)) :
    hasLocal (names.map (Sum.map id function)) = hasLocal names := by
  induction names with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [hasLocal] at ih ⊢ <;> exact ih

/-- External renaming commutes with either binder form and its depth decision. -/
theorem binder_map (function : Atom → Other) (smart : Bool) (body : Shape (Sum Unit Atom)) :
    binder smart (body.map (Sum.map id function)) = (binder smart body).map function := by
  simp only [binder, Shape.map, hasLocal_map]
  split
  · simp only [lower, Shape.free, Shape.mk.injEq, List.map_nil, true_and, and_true]
    rw [← List.map_append, InternedFreeNameSemantics.lower_map]
  · simp only [lower, InternedFreeNameSemantics.lower_map]

/-- Extending the shape environment preserves its fresh symbolic local. -/
theorem local_map (function : Atom → Other) (environment : List (Shape Atom)) :
    (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)).map (Shape.map (Sum.map id function)) =
      ⟨[Sum.inl ()], [], false, 0⟩ :: (environment.map (Shape.map function)).map (Shape.map Sum.inr) := by
  simp [Shape.map, List.map_map, Function.comp_def]

mutual
/-- Complete depth interpretation commutes with arbitrary external-name maps. -/
theorem evaluate_map {Atom Other : Type} (function : Atom → Other) (expression : Syntax Symbol Guard)
    (environment : List (Shape Atom)) :
    evaluate expression (environment.map (Shape.map function)) = (evaluate expression environment).map function := by
  cases expression with
  | empty => simp [evaluate, Shape.map]
  | var index =>
      rw [evaluate, evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map, found, Shape.map]
  | node edges => simpa only [evaluate] using evaluateEdges_map function edges environment
  | union members => simp only [evaluate, evaluateMany_map function members environment, combineMany_map]
  | binder smart body =>
      rw [evaluate, evaluate, ← local_map function environment,
        evaluate_map (Sum.map id function) body _, binder_map]
termination_by sizeOf expression

/-- Ordered child shapes retain their external-name map. -/
theorem evaluateMany_map {Atom Other : Type} (function : Atom → Other) (expressions : List (Syntax Symbol Guard))
    (environment : List (Shape Atom)) :
    evaluateMany expressions (environment.map (Shape.map function)) =
      (evaluateMany expressions environment).map (Shape.map function) := by
  cases expressions with
  | nil => simp [evaluateMany]
  | cons first rest => simp only [evaluateMany, evaluate_map function first environment,
      evaluateMany_map function rest environment, List.map_cons]
termination_by sizeOf expressions

/-- Renaming preserves source edge deletion and every remaining edge depth. -/
theorem evaluateEdges_map {Atom Other : Type} (function : Atom → Other) (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Shape Atom)) :
    evaluateEdges expressions (environment.map (Shape.map function)) =
      (evaluateEdges expressions environment).map function := by
  cases expressions with
  | nil => simp [evaluateEdges, Shape.map]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [evaluateEdges, evaluateMany_map function children environment, edge_map,
            evaluateEdges_map function rest environment, combine_map]
termination_by sizeOf expressions
end

/-- Even a noninjective external-name map preserves the predicted cached depth. -/
theorem depth_map (function : Atom → Other) (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) :
    (evaluate expression (environment.map (Shape.map function))).depth = (evaluate expression environment).depth := by
  rw [evaluate_map]
  rfl

/-- Supplying a literal argument preserves the fresh symbolic body's predicted depth. -/
theorem supplied_depth (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) (argument : Atom) :
    (evaluate expression (⟨[argument], [], false, 0⟩ :: environment)).depth =
      (evaluate expression (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr))).depth := by
  let supply : Sum Unit Atom → Atom := fun name => match name with | .inl _ => argument | .inr captured => captured
  have mapped := depth_map supply expression (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr))
  have input : (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)).map (Shape.map supply) =
      ⟨[argument], [], false, 0⟩ :: environment := by
    simp [Shape.map, supply, List.map_map, Function.comp_def]
  simpa only [input] using mapped

/-- Both probe arguments and any actual literal local have the same predicted body depth. -/
theorem arguments_depth (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) (first second : Atom) :
    (evaluate expression (⟨[first], [], false, 0⟩ :: environment)).depth =
      (evaluate expression (⟨[second], [], false, 0⟩ :: environment)).depth :=
  (supplied_depth expression environment first).trans (supplied_depth expression environment second).symm

end MicroCFTA.InternedDepthSemantics
