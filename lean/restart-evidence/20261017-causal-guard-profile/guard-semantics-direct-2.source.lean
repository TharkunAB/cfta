import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
import MicroCFTA.InternedRecordDepthShape

/-!
# Joint source shapes and exact guard-depth evaluation

The interpreter retains root alternatives, deep names, cached depth, and
finite guard depth. It tests actual row survival before it reads a row guard.
Each nested binder has a distinct symbolic local. Renaming external names
therefore preserves every guard-depth decision. Actual cache correspondence
requires separate normalization and causal publication proofs.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardSemantics
open InternedConstructorTemplates InternedNestedConstruction
/-- The structural and guard-depth observations remain distinct fields. -/
structure Shape (Atom : Type) where
  /-- Root alternatives, deep names, opacity, and original cached depth. -/
  shape : InternedDepthSemantics.Shape Atom := {}
  /-- The exact finite guard depth, with a missing value for a nonhereditary Mu. -/
  guardDepth : Option Nat := some 0

/-- Renaming retains both numeric observations and changes only literal names. -/
def Shape.map (function : Atom → Other) (value : Shape Atom) : Shape Other :=
  ⟨value.shape.map function, value.guardDepth⟩

/-- A literal reference has one root occurrence and no guard constraint. -/
def reference (name : Atom) : Shape Atom := ⟨⟨[name], [], false, 0⟩, some 0⟩

/-- Ordered alternatives join both their structural and guard observations. -/
def combine (first second : Shape Atom) : Shape Atom :=
  ⟨InternedDepthSemantics.combine first.shape second.shape, SourceCurrentConstrainedCapGuardDepth.join first.guardDepth second.guardDepth⟩

/-- All ordered alternatives retain the largest finite depth and every obstruction. -/
def combineMany : List (Shape Atom) → Shape Atom
  | [] => {}
  | first :: rest => combine first (combineMany rest)

/-- An erased row contributes no guard; a surviving row consumes its actual ordinary layer. -/
noncomputable def edge (valid : Guard → Prop) (guard : Guard) (values : List (Shape Atom)) : Shape Atom :=
  ⟨InternedDepthSemantics.edge (values.map Shape.shape),
    if (values.map Shape.shape).any InternedDepthSemantics.Shape.isEmpty then some 0
    else SourceCurrentConstrainedCapGuardDepth.join (some (SourceCurrentConstrainedCapGuardDepth.guardCost valid guard)) (SourceCurrentConstrainedCapGuardDepth.raise (combineMany values).guardDepth)⟩

/-- A retained wrapper permits finite guard depth only when its body is hereditary. -/
def binder (smart : Bool) (body : Shape (Sum Unit Atom)) : Shape Atom :=
  ⟨InternedDepthSemantics.binder smart body.shape,
    if !smart || InternedDepthSemantics.hasLocal body.shape.deep then
      if body.guardDepth = some 0 then some 0 else none
    else body.guardDepth⟩

mutual
/-- Full source syntax evaluates with its literal guards and fresh symbolic binders. -/
noncomputable def evaluate (valid : Guard → Prop) (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) : Shape Atom :=
  match expression with
  | .empty => {}
  | .var index => environment[index]?.getD {}
  | .node edges => evaluateEdges valid edges environment
  | .union members => combineMany (evaluateMany valid members environment)
  | .binder smart body => binder smart (evaluate valid body (reference (.inl ()) :: environment.map (Shape.map Sum.inr)))
termination_by sizeOf expression

/-- Each source child retains the same original lexical environment. -/
noncomputable def evaluateMany (valid : Guard → Prop) (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom)) : List (Shape Atom) :=
  match expressions with
  | [] => []
  | first :: rest => evaluate valid first environment :: evaluateMany valid rest environment
termination_by sizeOf expressions

/-- Row evaluation tests original child emptiness before joining the complete guard field. -/
noncomputable def evaluateEdges (valid : Guard → Prop) (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom)) : Shape Atom :=
  match expressions with
  | [] => {}
  | .mk _ guard children :: rest => combine (edge valid guard (evaluateMany valid children environment)) (evaluateEdges valid rest environment)
termination_by sizeOf expressions
end

/-- Structural projection retains ordered shape combination. -/
theorem combineMany_shape (values : List (Shape Atom)) :
    (combineMany values).shape = InternedDepthSemantics.combineMany (values.map Shape.shape) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [combineMany, combine, List.map_cons, InternedDepthSemantics.combineMany, ih]

/-- Mapping each lexical record commutes with structural projection. -/
theorem shapes_map (function : Atom → Other) (values : List (Shape Atom)) :
    (values.map (Shape.map function)).map Shape.shape = (values.map Shape.shape).map (InternedDepthSemantics.Shape.map function) := by
  simp [Shape.map, List.map_map, Function.comp_def]

/-- Renaming changes neither operand's guard observation. -/
theorem combine_map (function : Atom → Other) (first second : Shape Atom) :
    combine (first.map function) (second.map function) = (combine first second).map function := by
  simp only [combine, Shape.map, InternedDepthSemantics.combine_map]

/-- Ordered shape combination commutes with arbitrary external-name maps. -/
theorem combineMany_map (function : Atom → Other) (values : List (Shape Atom)) :
    combineMany (values.map (Shape.map function)) = (combineMany values).map function := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, combineMany, ih, combine_map]

/-- Renaming preserves both actual empty-child tests and row guard-depth costs. -/
theorem edge_map (function : Atom → Other) (valid : Guard → Prop) (guard : Guard) (values : List (Shape Atom)) :
    edge valid guard (values.map (Shape.map function)) = (edge valid guard values).map function := by
  simp only [edge, shapes_map, InternedDepthSemantics.edge_map, List.any_map, Function.comp_def,
    InternedDepthSemantics.isEmpty_map, combineMany_map, Shape.map]

/-- External renaming preserves the distinct local and every nested binder guard decision. -/
theorem binder_map (function : Atom → Other) (smart : Bool) (body : Shape (Sum Unit Atom)) :
    binder smart (body.map (Sum.map id function)) = (binder smart body).map function := by
  simp only [binder, Shape.map, InternedDepthSemantics.binder_map, InternedDepthSemantics.Shape.map, InternedDepthSemantics.hasLocal_map]

/-- Mapping the outer scope leaves each new symbolic local distinct. -/
theorem local_map (function : Atom → Other) (environment : List (Shape Atom)) :
    (reference (Sum.inl ()) :: environment.map (Shape.map Sum.inr)).map (Shape.map (Sum.map id function)) =
      reference (.inl ()) :: (environment.map (Shape.map function)).map (Shape.map Sum.inr) := by
  simp [reference, Shape.map, InternedDepthSemantics.Shape.map, List.map_map, Function.comp_def]

mutual
/-- Complete joint evaluation commutes with every external-name map. -/
theorem evaluate_map (function : Atom → Other) (valid : Guard → Prop) (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) :
    evaluate valid expression (environment.map (Shape.map function)) = (evaluate valid expression environment).map function := by
  cases expression with
  | empty => simp [evaluate, Shape.map, InternedDepthSemantics.Shape.map]
  | var index =>
      rw [evaluate, evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map, found, Shape.map, InternedDepthSemantics.Shape.map]
  | node edges => simpa only [evaluate] using evaluateEdges_map function valid edges environment
  | union members => simp only [evaluate, evaluateMany_map function valid members environment, combineMany_map]
  | binder smart body =>
      rw [evaluate, evaluate, ← local_map function environment, evaluate_map (Sum.map id function) valid body _, binder_map]
termination_by sizeOf expression

/-- Every ordered child evaluation retains its external-name map. -/
theorem evaluateMany_map (function : Atom → Other) (valid : Guard → Prop) (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom)) :
    evaluateMany valid expressions (environment.map (Shape.map function)) = (evaluateMany valid expressions environment).map (Shape.map function) := by
  cases expressions with
  | nil => rfl
  | cons first rest => simp only [evaluateMany, evaluate_map function valid first environment,
      evaluateMany_map function valid rest environment, List.map_cons]
termination_by sizeOf expressions

/-- Source row survival and guard costs are invariant under every external renaming. -/
theorem evaluateEdges_map (function : Atom → Other) (valid : Guard → Prop) (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom)) :
    evaluateEdges valid expressions (environment.map (Shape.map function)) = (evaluateEdges valid expressions environment).map function := by
  cases expressions with
  | nil => simp [evaluateEdges, Shape.map, InternedDepthSemantics.Shape.map]
  | cons first rest =>
      cases first with
      | mk symbol guard children => simp only [evaluateEdges, evaluateMany_map function valid children environment,
          edge_map, evaluateEdges_map function valid rest environment, combine_map]
termination_by sizeOf expressions
end

mutual
/-- The joint interpreter retains the entire existing structural source evaluation. -/
theorem evaluate_shape (valid : Guard → Prop) (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) :
    (evaluate valid expression environment).shape = InternedDepthSemantics.evaluate expression (environment.map Shape.shape) := by
  cases expression with
  | empty => rfl
  | var index =>
      rw [evaluate, InternedDepthSemantics.evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map, found]
  | node edges => simpa only [evaluate, InternedDepthSemantics.evaluate] using evaluateEdges_shape valid edges environment
  | union members => simp only [evaluate, combineMany_shape, evaluateMany_shape valid members environment, InternedDepthSemantics.evaluate]
  | binder smart body =>
      simp only [evaluate, binder, evaluate_shape valid body _, InternedDepthSemantics.evaluate]
      congr 1
      simp [reference, Shape.map, List.map_map, Function.comp_def]
termination_by sizeOf expression

/-- Structural projection retains all original ordered source child evaluations. -/
theorem evaluateMany_shape (valid : Guard → Prop) (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom)) :
    (evaluateMany valid expressions environment).map Shape.shape = InternedDepthSemantics.evaluateMany expressions (environment.map Shape.shape) := by
  cases expressions with
  | nil => rfl
  | cons first rest => simp only [evaluateMany, List.map_cons, evaluate_shape valid first environment, evaluateMany_shape valid rest environment, InternedDepthSemantics.evaluateMany]
termination_by sizeOf expressions

/-- Structural projection retains the exact original surviving-row schedule. -/
theorem evaluateEdges_shape (valid : Guard → Prop) (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom)) :
    (evaluateEdges valid expressions environment).shape = InternedDepthSemantics.evaluateEdges expressions (environment.map Shape.shape) := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
      cases first with
      | mk symbol guard children => simp only [evaluateEdges, combine, edge, evaluateMany_shape valid children environment, evaluateEdges_shape valid rest environment,
          InternedDepthSemantics.evaluateEdges]
termination_by sizeOf expressions
end

/-- Supplying a literal argument leaves captured names unchanged. -/
def supply (argument : Atom) : Sum Unit Atom → Atom
  | .inl _ => argument
  | .inr captured => captured

/-- Each literal callback argument is an image of the same fresh symbolic body. -/
theorem evaluate_supplied (valid : Guard → Prop) (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) (argument : Atom) :
    evaluate valid expression (reference argument :: environment) =
      (evaluate valid expression (reference (.inl ()) :: environment.map (Shape.map Sum.inr))).map (supply argument) := by
  have mapped := evaluate_map (supply argument) valid expression (reference (.inl ()) :: environment.map (Shape.map Sum.inr))
  have input : (reference (Sum.inl ()) :: environment.map (Shape.map Sum.inr)).map (Shape.map (supply argument)) =
      reference argument :: environment := by
    simp [reference, Shape.map, InternedDepthSemantics.Shape.map, supply, List.map_map, Function.comp_def]
  simpa only [input] using mapped

/-- Literal callback arguments cannot change the exact predicted guard depth. -/
theorem arguments_guardDepth (valid : Guard → Prop) (expression : Syntax Symbol Guard) (environment : List (Shape Atom)) (first second : Atom) :
    (evaluate valid expression (reference first :: environment)).guardDepth =
      (evaluate valid expression (reference second :: environment)).guardDepth := by
  rw [evaluate_supplied valid expression environment first, evaluate_supplied valid expression environment second]
  rfl

/-- Root self filtering changes literal alternatives and retains both numeric observations. -/
def normalize [DecidableEq Atom] (argument : Atom) (value : Shape Atom) : Shape Atom :=
  {value with shape := {value.shape with roots :=
    if value.shape.hasOpaque || !(value.shape.roots.all (· == argument)) then value.shape.roots.filter (· != argument)
    else value.shape.roots}}

/-- The actual root-filter model preserves the guard observation even when it removes a bare local. -/
theorem normalize_guardDepth [DecidableEq Atom] (argument : Atom) (value : Shape Atom) :
    (normalize argument value).guardDepth = value.guardDepth := rfl

/-- Normalized callbacks share the same exact guard-depth prediction. -/
theorem normalized_arguments_guardDepth [DecidableEq Atom] (valid : Guard → Prop) (expression : Syntax Symbol Guard)
    (environment : List (Shape Atom)) (first second : Atom) :
    (normalize first (evaluate valid expression (reference first :: environment))).guardDepth =
      (normalize second (evaluate valid expression (reference second :: environment))).guardDepth :=
  arguments_guardDepth valid expression environment first second

/-- A complete stored record supplies both original structural fields and its exact guard depth. -/
noncomputable def decode (valid : Guard → Prop) (value : Value Symbol Guard) : Shape InternedBinderProtocol.Reference :=
  ⟨InternedRecordDepthShape.shape value, SourceCurrentConstrainedCapGuardDepth.profile valid value⟩

/-- The decoded guard observation is exactly the existing finite-cap predicate. -/
theorem decode_within_iff (valid : Guard → Prop) (depth : Nat) (value : Value Symbol Guard) :
    SourceCurrentConstrainedCapGuardDepth.Within depth (decode valid value).guardDepth ↔ SourceCurrentConstrainedCap.Cap valid depth value :=
  SourceCurrentConstrainedCapGuardDepth.within_iff_cap valid depth value

end MicroCFTA.SourceCurrentConstrainedCapGuardSemantics
