import MicroCFTA.SourceCurrentNativeTracePrefixBind

/-!
# Exact indexed physical prefixes of ordered native calls

The trace either completes the walk or stops inside one original call.
The selected call retains its original index and the actual earlier walk.
The remaining continuation retains the ordered results and original tail.
-/
namespace MicroCFTA.SourceCurrentNativeWalkPrefix
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
open SourceCurrentNativeTracePrefixBind (bind_prefix_cases)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A B C : Type} {width : Nat}

/-- A physical walk prefix retains the exact unfinished input or its completed ordered results. -/
theorem walk_prefix_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (inputs : List A) (next : List B → Code Symbol Guard C)
    (fuel : Nat) (before after : Checked width) (remaining : Control C)
    (actual : Trace fuel ((.code (walk call inputs) : Control (List B)).bind next) before remaining after) :
    (∃ index input values entry prefixFuel currentFuel inner,
      inputs[index]? = some input ∧
      Walk call (inputs.take index) before values entry prefixFuel ∧
      prefixFuel + currentFuel = fuel ∧
      Trace currentFuel (.code (call input)) entry inner after ∧
      (∀ value, inner ≠ .code (.pure value)) ∧
      remaining = inner.bind (fun value =>
        (walk call (inputs.drop (index + 1))).bind (fun tail => next (values ++ value :: tail)))) ∨
    (∃ walkFuel outerFuel values middle, walkFuel + outerFuel = fuel ∧
      Walk call inputs before values middle walkFuel ∧
      Trace outerFuel (.code (next values)) middle remaining after) := by
  induction inputs generalizing fuel before next with
  | nil =>
      exact Or.inr ⟨0, fuel, [], before, rfl, .nil _, actual⟩
  | cons first rest ih =>
      let continuation := fun value => (walk call rest).bind (fun values => next (value :: values))
      have bound : Trace fuel ((.code (call first) : Control B).bind continuation) before remaining after := by
        simpa only [walk, Control.bind, Code.bind_assoc, Code.bind] using actual
      rcases bind_prefix_cases fuel (.code (call first)) continuation before after remaining bound with
        ⟨inner, called, nonpure, same⟩ | ⟨firstFuel, tailFuel, value, middle, count, called, tailTrace⟩
      · exact Or.inl ⟨0, first, [], before, 0, fuel, inner, rfl, .nil _, rfl, called, nonpure, same⟩
      · have tailBound : Trace tailFuel
            ((.code (walk call rest) : Control (List B)).bind (fun values => next (value :: values)))
            middle remaining after := tailTrace
        rcases ih (fun values => next (value :: values)) tailFuel middle tailBound with
          ⟨index, input, values, entry, prefixFuel, currentFuel, inner,
            selected, earlier, total, current, nonpure, same⟩ |
          ⟨walkFuel, outerFuel, values, final, total, earlier, later⟩
        · refine Or.inl ⟨index + 1, input, value :: values, entry, firstFuel + prefixFuel, currentFuel,
            inner, ?_, ?_, by omega, current, nonpure, ?_⟩
          · simpa only [List.getElem?_cons_succ] using selected
          · exact .cons first (rest.take index) before middle entry value values firstFuel prefixFuel called earlier
          · simpa only [List.drop_succ_cons, List.cons_append] using same
        · exact Or.inr ⟨firstFuel + walkFuel, outerFuel, value :: values, final, by omega,
            .cons first rest before middle final value values firstFuel walkFuel called earlier, later⟩

end MicroCFTA.SourceCurrentNativeWalkPrefix
