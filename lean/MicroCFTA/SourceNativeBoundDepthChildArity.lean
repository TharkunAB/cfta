import MicroCFTA.SourceNativeBoundDepth

namespace MicroCFTA.SourceNativeBoundDepth
open InternedConstructorTemplates

/-- A successful ordered child traversal retains the input arity. -/
theorem children_length
    (copy : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard →
      Result Symbol Guard (Value Symbol Guard))
    (inputs outputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (memo finalMemo : Memo Symbol Guard)
    (completed : children copy inputs before memo = (.done outputs after, finalMemo)) :
    outputs.length = inputs.length := by
  induction inputs generalizing outputs before after memo finalMemo with
  | nil => cases completed; rfl
  | cons first rest ih =>
      cases headActual : copy first before memo with
      | mk headResult nextMemo =>
          cases headResult with
          | failed fault middle =>
              simp only [children, headActual, bind] at completed
              cases congrArg Prod.fst completed
          | done value middle =>
              cases tailActual : children copy rest middle nextMemo with
              | mk tailResult lastMemo =>
                  cases tailResult with
                  | failed fault final =>
                      simp only [children, headActual, bind, tailActual] at completed
                      cases congrArg Prod.fst completed
                  | done values final =>
                      have same :
                          ((.done (value :: values) final, lastMemo) :
                            Result Symbol Guard (List (Value Symbol Guard))) =
                            (.done outputs after, finalMemo) := by
                        simpa only [children, headActual, bind, tailActual] using completed
                      have sameValues : value :: values = outputs :=
                        (MergedSourceComparison.Result.done.inj (congrArg Prod.fst same)).1
                      rw [← sameValues, List.length_cons, List.length_cons]
                      exact congrArg Nat.succ
                        (ih values middle final nextMemo lastMemo tailActual)

end MicroCFTA.SourceNativeBoundDepth
