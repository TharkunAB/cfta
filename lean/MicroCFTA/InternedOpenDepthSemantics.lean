import MicroCFTA.InternedDepthSemantics
import MicroCFTA.InternedStoredPlanBinderDepth

/-!
# Open binder depth in pure source interpretation

The existing shape interpretation supplies free names and empty decisions.
A separate ordered depth environment assigns zero to closed captures.
Closing a binder resets its open depth to zero. This interpretation does
not by itself prove correspondence with the interned executor.
-/
namespace MicroCFTA.InternedOpenDepthSemantics
open InternedNestedConstruction
open InternedDepthSemantics (Shape hasLocal)

/-- A binder adds one open level only when it remains open and retains its wrapper. -/
def binderDepth (smart : Bool) (body : Shape (Sum Unit Atom)) (depth : Nat) : Nat :=
  if (InternedDepthSemantics.binder smart body).free.isEmpty then 0
  else if !smart || hasLocal body.deep then depth + 1 else depth

/-- External renaming preserves the exact open-depth contribution of a binder. -/
theorem binderDepth_map (function : Atom → Other) (smart : Bool)
    (body : Shape (Sum Unit Atom)) (depth : Nat) :
    binderDepth smart (body.map (Sum.map id function)) depth = binderDepth smart body depth := by
  unfold binderDepth
  rw [InternedDepthSemantics.binder_map]
  have mapped (value : Shape Atom) : (value.map function).free = value.free.map function := by
    simp [Shape.map, Shape.free]
  rw [mapped, List.isEmpty_map]
  simp only [Shape.map, InternedDepthSemantics.hasLocal_map]

mutual
/-- Interpret open binder depth with the original shape and separate lexical depth inputs. -/
def evaluate {Atom : Type} (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (depths : List Nat) : Nat :=
  match expression with
  | .empty => 0
  | .var index => depths[index]?.getD 0
  | .node edges => evaluateEdges edges environment depths
  | .union members => evaluateMany members environment depths
  | .binder smart body =>
      let inner := ⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)
      binderDepth smart (InternedDepthSemantics.evaluate body inner) (evaluate body inner (0 :: depths))
termination_by sizeOf expression

/-- Ordered source operands contribute their maximum open depth. -/
def evaluateMany {Atom : Type} (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom))
    (depths : List Nat) : Nat :=
  match expressions with
  | [] => 0
  | first :: rest => max (evaluate first environment depths) (evaluateMany rest environment depths)
termination_by sizeOf expressions

/-- Empty source children remove an edge before its open-depth maximum contributes. -/
def evaluateEdges {Atom : Type} (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom))
    (depths : List Nat) : Nat :=
  match expressions with
  | [] => 0
  | .mk _ _ children :: rest =>
      max (if (InternedDepthSemantics.evaluateMany children environment).any Shape.isEmpty then 0
        else evaluateMany children environment depths) (evaluateEdges rest environment depths)
termination_by sizeOf expressions
end

mutual
/-- Renaming external atoms preserves open depth, including every closed-binder cut. -/
theorem evaluate_map {Atom Other : Type} (function : Atom → Other) (expression : Syntax Symbol Guard)
    (environment : List (Shape Atom)) (depths : List Nat) :
    evaluate expression (environment.map (Shape.map function)) depths = evaluate expression environment depths := by
  cases expression with
  | empty | var => simp only [evaluate]
  | node edges => simpa only [evaluate] using evaluateEdges_map function edges environment depths
  | union members => simpa only [evaluate] using evaluateMany_map function members environment depths
  | binder smart body =>
      rw [evaluate, evaluate, ← InternedDepthSemantics.local_map function environment,
        InternedDepthSemantics.evaluate_map, evaluate_map (Sum.map id function), binderDepth_map]
termination_by sizeOf expression

/-- External renaming preserves the maximum open depth of every ordered operand. -/
theorem evaluateMany_map {Atom Other : Type} (function : Atom → Other) (expressions : List (Syntax Symbol Guard))
    (environment : List (Shape Atom)) (depths : List Nat) :
    evaluateMany expressions (environment.map (Shape.map function)) depths = evaluateMany expressions environment depths := by
  cases expressions with
  | nil => simp only [evaluateMany]
  | cons first rest => rw [evaluateMany, evaluateMany, evaluate_map function, evaluateMany_map function]
termination_by sizeOf expressions

/-- External renaming preserves source edge survival and its exact open-depth maximum. -/
theorem evaluateEdges_map {Atom Other : Type} (function : Atom → Other) (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Shape Atom)) (depths : List Nat) :
    evaluateEdges expressions (environment.map (Shape.map function)) depths = evaluateEdges expressions environment depths := by
  cases expressions with
  | nil => simp only [evaluateEdges]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [evaluateEdges, evaluateEdges, InternedDepthSemantics.evaluateMany_map function children environment]
          simp only [List.any_map, Function.comp_def, InternedDepthSemantics.isEmpty_map]
          rw [evaluateMany_map function children environment depths, evaluateEdges_map function rest environment depths]
termination_by sizeOf expressions
end

/-- A literal argument has the same interpreted open depth as its distinct symbolic local. -/
theorem supplied_depth (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (depths : List Nat) (argument : Atom) :
    evaluate expression (⟨[argument], [], false, 0⟩ :: environment) (0 :: depths) =
      evaluate expression (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)) (0 :: depths) := by
  let supply : Sum Unit Atom → Atom := fun name => match name with | .inl _ => argument | .inr capture => capture
  have mapped := evaluate_map supply expression (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)) (0 :: depths)
  have input : (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)).map (Shape.map supply) =
      ⟨[argument], [], false, 0⟩ :: environment := by
    simp [Shape.map, supply, List.map_map, Function.comp_def]
  simpa only [input] using mapped

/-- Both actual probes and the fresh body argument have the same interpreted open depth. -/
theorem arguments_depth (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (depths : List Nat) (first second : Atom) :
    evaluate expression (⟨[first], [], false, 0⟩ :: environment) (0 :: depths) =
      evaluate expression (⟨[second], [], false, 0⟩ :: environment) (0 :: depths) :=
  (supplied_depth expression environment depths first).trans (supplied_depth expression environment depths second).symm

open InternedStoredPlanBinderDepth

mutual
/-- Source binder nesting plus a lexical input bound bounds the interpreted open depth. -/
theorem evaluate_bound (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (depths : List Nat) (bound : Nat) (inputs : ∀ depth ∈ depths, depth ≤ bound) :
    evaluate expression environment depths ≤ syntaxDepth expression + bound := by
  cases expression with
  | empty => simp [evaluate, syntaxDepth]
  | var index =>
      rw [evaluate, syntaxDepth, Nat.zero_add]
      cases found : depths[index]? with
      | none => exact Nat.zero_le _
      | some depth => exact inputs depth (List.mem_of_getElem? found)
  | node edges => simpa only [evaluate, syntaxDepth] using evaluateEdges_bound edges environment depths bound inputs
  | union members => simpa only [evaluate, syntaxDepth] using evaluateMany_bound members environment depths bound inputs
  | binder smart body =>
      rw [evaluate, syntaxDepth]
      have nested := evaluate_bound body
        (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)) (0 :: depths) bound
        (by intro depth member; rcases List.mem_cons.mp member with rfl | member; exact Nat.zero_le _; exact inputs depth member)
      unfold binderDepth
      split
      · omega
      · split <;> omega
termination_by sizeOf expression

/-- Ordered source operands retain the maximum static binder-depth bound. -/
theorem evaluateMany_bound (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom))
    (depths : List Nat) (bound : Nat) (inputs : ∀ depth ∈ depths, depth ≤ bound) :
    evaluateMany expressions environment depths ≤ syntaxManyDepth expressions + bound := by
  cases expressions with
  | nil => simp [evaluateMany, syntaxManyDepth]
  | cons first rest =>
      rw [evaluateMany, syntaxManyDepth]
      have head := evaluate_bound first environment depths bound inputs
      have tail := evaluateMany_bound rest environment depths bound inputs
      omega
termination_by sizeOf expressions

/-- Source edge deletion can only reduce the interpreted binder-depth bound. -/
theorem evaluateEdges_bound (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom))
    (depths : List Nat) (bound : Nat) (inputs : ∀ depth ∈ depths, depth ≤ bound) :
    evaluateEdges expressions environment depths ≤ syntaxEdgesDepth expressions + bound := by
  cases expressions with
  | nil => simp [evaluateEdges, syntaxEdgesDepth]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [evaluateEdges, syntaxEdgesDepth]
          have head := evaluateMany_bound children environment depths bound inputs
          have tail := evaluateEdges_bound rest environment depths bound inputs
          split <;> omega
termination_by sizeOf expressions
end

end MicroCFTA.InternedOpenDepthSemantics
