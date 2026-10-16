import MicroCFTA.SourceCurrentAllocatedNativeContextExecution
open MicroCFTA Language InternedConstructorTemplates
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedNativeContextCache
open SourceCurrentAllocatedNativeContextExecution
#print axioms body_contextual
#print axioms step_contextual
#print axioms execute_contextual
#print axioms done_contextual
#check FinishLaw
#check FinishThrough
#check body_contextual
#check step_contextual
#check execute_contextual
#check done_contextual
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- No finish law is needed when the finite execution performs no instruction.
example (control : Control Output) (state : Checked width) :
    FinishThrough view model ranked holds 0 control state := True.intro
example (value : Nat) (state : Checked width) :
    FinishLaw view model ranked holds (.code (.pure value)) state := True.intro
example (request : EdgeRequest Symbol Guard) (state : Checked width) :
    FinishLaw view model ranked holds (.edgeBody request .pure) state := True.intro
example (request : NodeRequest Symbol Guard) (state : Checked width) :
    FinishLaw view model ranked holds (.code (.node request .pure)) state := True.intro

-- The actual interpreter keeps the operation state on these native steps.
example (value : Nat) (state : Checked width) :
    execute 1 (.code (.pure value)) state = .done value state := by rfl
example (state : Checked width) :
    execute 1 (.code (.fail .exhausted) : Control Nat) state = .failed .exhausted state := by rfl

-- Finishing an absent cell needs no semantic result receipt.
example (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (handle : Nat) (value : Value Symbol Guard) :
    FinishLaw view model ranked holds (.code (.finishNode handle value (.pure 0)))
      (⟨initial width machine, operations⟩ : Checked width) := by
  intro request found
  cases found
example (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (handle : Nat) (value : EdgeValue Symbol Guard) :
    FinishLaw view model ranked holds (.code (.finishEdge handle value (.pure 0)))
      (⟨initial width machine, operations⟩ : Checked width) := by
  intro request found
  cases found
example (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (handle : Nat) (value : Value Symbol Guard) :
    execute 1 (.code (.finishNode handle value (.pure 0))) (⟨initial width machine, operations⟩ : Checked width) =
      .yielded (.code (.pure 0)) ⟨initial width machine, operations⟩ := by rfl
example (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (handle : Nat) (value : EdgeValue Symbol Guard) :
    execute 1 (.code (.finishEdge handle value (.pure 0))) (⟨initial width machine, operations⟩ : Checked width) =
      .yielded (.code (.pure 0)) ⟨initial width machine, operations⟩ := by rfl

-- Context retention follows even when no input/output semantic theorem is supplied.
example (control : Control Output) (state : Checked width)
    (context : Contextual view model ranked holds state.native) :
    Contextual view model ranked holds (execute 0 control state).state.native :=
  execute_contextual view model ranked holds 0 control state context True.intro
example (request : EdgeRequest Symbol Guard) (state : Checked width)
    (context : Contextual view model ranked holds state.native) :
    Contextual view model ranked holds (body request .pure state).state.native :=
  body_contextual view model ranked holds request .pure state context
