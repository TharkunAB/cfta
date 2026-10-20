import MicroCFTA.SourceCurrentNativeWalkPrefix

/-!
# An actual ordered walk prefix reaches its selected child call

The original bound walk retains its actual prefix to an original indexed
call. The same unbound child prefix reaches the selected optional instruction.
A completed whole walk remains a separate alternative.
-/
namespace MicroCFTA.SourceCurrentNativeWalkOptionalPrefix
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
open SourceCurrentNativeWalkPrefix (walk_prefix_cases)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A B C : Type} {width : Nat}
private theorem walk_append (call : A → Code Symbol Guard B) (first rest : List A) :
    walk call (first ++ rest) =
      (walk call first).bind (fun values => (walk call rest).bind (fun tail => .pure (values ++ tail))) := by
  induction first with
  | nil => simp only [List.nil_append,walk,Code.bind,code_bind_pure]
  | cons first front ih =>
    simp only [List.cons_append,walk,ih,Code.bind_assoc,Code.bind]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem prefix_trace (call : A → Code Symbol Guard B) (front : List A) (input : A) (tail : List A)
    (next : List B → Code Symbol Guard C) {before entry : Checked width} {values : List B} {fuel : Nat}
    (earlier : Walk call front before values entry fuel) :
    Trace fuel ((.code (walk call (front ++ input :: tail)) : Control (List B)).bind next) before
      ((.code (call input) : Control B).bind
        (fun value => (walk call tail).bind (fun rest => next (values ++ value :: rest)))) entry := by
  let continuation := fun values => (call input).bind
    (fun value => (walk call tail).bind (fun rest => next (values ++ value :: rest)))
  have actual := earlier.trace.bind continuation
  have start : ((.code (walk call (front ++ input :: tail)) : Control (List B)).bind next) =
      ((.code (walk call front) : Control (List B)).bind continuation) := by
    simp only [walk_append,Control.bind,Code.bind_assoc,walk,Code.bind,continuation]
  rw [start]
  exact actual

/-- A bound walk reaches an original indexed call or completes before its outer optional prefix. -/
theorem cut (call : A → Code Symbol Guard B) (inputs : List A) (next : List B → Code Symbol Guard C)
    (fuel : Nat) (before after : Checked width) (pair : Nat × Nat) (body : Node)
    (siteNext : Node → Code Symbol Guard C)
    (actual : Trace fuel ((.code (walk call inputs) : Control (List B)).bind next) before
      (.code (.optionalBinder pair body siteNext)) after) :
    (∃ walkFuel outerFuel values middle, walkFuel + outerFuel = fuel ∧
      Walk call inputs before values middle walkFuel ∧
      Trace outerFuel (.code (next values)) middle (.code (.optionalBinder pair body siteNext)) after) ∨
    (∃ index input values entry prefixFuel childFuel innerNext,
      let callNext := fun value =>
        (walk call (inputs.drop (index + 1))).bind (fun tail => next (values ++ value :: tail))
      inputs[index]? = some input ∧
      Walk call (inputs.take index) before values entry prefixFuel ∧
      prefixFuel + childFuel = fuel ∧
      Trace prefixFuel ((.code (walk call inputs) : Control (List B)).bind next) before
        ((.code (call input) : Control B).bind callNext) entry ∧
      Trace childFuel (.code (call input)) entry (.code (.optionalBinder pair body innerNext)) after ∧
      siteNext = fun value => (innerNext value).bind callNext) := by
  rcases walk_prefix_cases call inputs next fuel before after (.code (.optionalBinder pair body siteNext)) actual with
    ⟨index,input,values,entry,prefixFuel,childFuel,inner,selected,earlier,total,called,nonpure,same⟩ | completed
  · have split : inputs = inputs.take index ++ input :: inputs.drop (index + 1) := by
      obtain ⟨bounded,atIndex⟩ := List.getElem?_eq_some_iff.mp selected
      have dropped := List.drop_eq_getElem_cons bounded
      rw [atIndex] at dropped
      rw [←dropped]
      exact (List.take_append_drop index inputs).symm
    have prefixCall := prefix_trace call (inputs.take index) input (inputs.drop (index + 1)) next earlier
    rw [←split] at prefixCall
    apply Or.inr
    cases inner with
    | edgeBody => cases same
    | code code =>
      cases code with
      | pure value => exact False.elim (nonpure value rfl)
      | optionalBinder own stored innerNext =>
        change Control.code (.optionalBinder pair body siteNext) =
          .code (.optionalBinder own stored (fun value => (innerNext value).bind
            (fun value => (walk call (inputs.drop (index + 1))).bind
              (fun tail => next (values ++ value :: tail))))) at same
        obtain ⟨rfl,rfl,rfl⟩ := Code.optionalBinder.inj (Control.code.inj same)
        exact ⟨index,input,values,entry,prefixFuel,childFuel,innerNext,
          selected,earlier,total,prefixCall,called,rfl⟩
      | _ => cases same
  · exact Or.inl completed

end MicroCFTA.SourceCurrentNativeWalkOptionalPrefix
