import MicroCFTA.SourceCurrentMemoMergeMeasured
import MicroCFTA.SourceCurrentMemoMergeResourceControl

/-!
# Scalar resources at every heap of a completed Merge graph

The indexed trace records resources and local input facts at the exact heaps
of a supplied completed graph. It converts actual selection receipts to one
computed comparison fuel. It does not construct an initial Merge execution.
-/
namespace MicroCFTA.SourceCurrentMemoMergeResourceTrace
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph (Code Memo body)
open SourceCurrentMemoMergeMeasured
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Guard : Type}
variable [symbolEq : DecidableEq Symbol] [edgeEq : DecidableEq (EdgeKey Symbol Guard)]

mutual
/-- Exact completed instructions retain scalar resources at every reached heap. -/
inductive Trace {clear : Guard → Bool} {top : Guard} (bound : Nat) :
    {Output : Type} → {cost : Nat} → {code : Code Symbol Guard Output} → {before : State Symbol Guard} →
      {memo : Memo Symbol Guard} → {output : Output} → {after : State Symbol Guard} → {saved : Memo Symbol Guard} →
      MeasuredRun clear top cost code before memo output after saved → Prop where
  /-- A pure return retains the same heap. -/
  | pure (value : Output) (state : State Symbol Guard) (memo : Memo Symbol Guard)
      (fits : Fits bound state) : Trace bound (.pure value state memo)
  /-- A physical instruction records both literal heap endpoints. -/
  | work (job : Work Symbol Guard Output) (state : State Symbol Guard) (memo : Memo Symbol Guard)
      (beforeFits : Fits bound state) (afterFits : Fits bound (run job state).2) :
      Trace bound (.work job state memo)
  /-- A reached selection records its actual inputs and both exact heap endpoints. -/
  | select (oldFuel : Nat) (done : SourceMergedSelection.select clear oldFuel inputs before = .done values after)
      (semantic : SemanticReady before) (beforeFits : Fits bound before)
      (available : Values before inputs) (closed : ClosedValues inputs) (afterFits : Fits bound after) :
      Trace bound (MeasuredRun.select (top := top) (memo := memo) oldFuel done)
  /-- A request uses the same completed child call. -/
  | request {actual : MeasuredCall clear top cost input before memo output after saved}
      (trace : CallTrace bound actual) : Trace bound (.request actual)
  /-- Both actual bind stages use the same scalar envelope. -/
  | bind {First Output : Type} {firstCost lastCost : Nat}
      {code : Code Symbol Guard First} {next : First → Code Symbol Guard Output}
      {before middle after : State Symbol Guard} {memo current saved : Memo Symbol Guard}
      {value : First} {output : Output}
      {first : MeasuredRun clear top firstCost code before memo value middle current}
      {later : MeasuredRun clear top lastCost (next value) middle current output after saved}
      (firstTrace : Trace bound first) (lastTrace : Trace bound later) : Trace bound (.bind first later)

/-- Exact completed calls retain resources across hits and actual miss bodies. -/
inductive CallTrace {clear : Guard → Bool} {top : Guard} (bound : Nat) :
    {cost : Nat} → {input : Value Symbol Guard} → {before : State Symbol Guard} → {memo : Memo Symbol Guard} →
      {output : Value Symbol Guard} → {after : State Symbol Guard} → {saved : Memo Symbol Guard} →
      MeasuredCall clear top cost input before memo output after saved → Prop where
  /-- A warm hit executes no body and retains the current heap. -/
  | hit {memo : Memo Symbol Guard} {input : Value Symbol Guard} {before : State Symbol Guard}
      {entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard}
      (found : memo input.referenceOf = some entry) (fits : Fits bound before) :
      CallTrace bound (.hit (before := before) found)
  /-- A miss records the same actual body before its current-winner reread. -/
  | miss {actual : MeasuredRun clear top cost (body top input) before memo candidate after current}
      (absent : memo input.referenceOf = none) (trace : Trace bound actual) :
      CallTrace bound (.miss absent actual)
end

/-- A larger scalar envelope retains all actual instruction facts. -/
theorem Trace.mono {clear : Guard → Bool} {top : Guard} {first last : Nat}
    {actual : MeasuredRun clear top cost code before memo output after saved}
    (trace : Trace first actual) (increase : first ≤ last) : Trace last actual := by
  induction trace using Trace.rec
      (motive_2 := fun _ input before memo output after saved actual _ =>
        @CallTrace Symbol Guard symbolEq edgeEq clear top last _ input before memo output after saved actual) with
  | pure value state memo fits => exact .pure value state memo (fits.mono increase)
  | work job state memo beforeFits afterFits => exact .work job state memo (beforeFits.mono increase) (afterFits.mono increase)
  | select oldFuel done semantic beforeFits available closed afterFits =>
      exact .select oldFuel done semantic (beforeFits.mono increase) available closed (afterFits.mono increase)
  | request child ih => exact .request ih
  | bind firstTrace lastTrace firstIH lastIH => exact .bind firstIH lastIH
  | hit found fits => exact .hit found (fits.mono increase)
  | miss absent bodyTrace ih => exact .miss absent ih

/-- A larger scalar envelope retains all actual call facts. -/
theorem CallTrace.mono {clear : Guard → Bool} {top : Guard} {first last : Nat}
    {actual : MeasuredCall clear top cost input before memo output after saved}
    (trace : CallTrace first actual) (increase : first ≤ last) : CallTrace last actual := by
  induction trace using CallTrace.rec
      (motive_1 := fun {Output} _ code before memo output after saved actual _ =>
        @Trace Symbol Guard symbolEq edgeEq clear top last Output _ code before memo output after saved actual) with
  | pure value state memo fits => exact .pure value state memo (fits.mono increase)
  | work job state memo beforeFits afterFits => exact .work job state memo (beforeFits.mono increase) (afterFits.mono increase)
  | select oldFuel done semantic beforeFits available closed afterFits =>
      exact .select oldFuel done semantic (beforeFits.mono increase) available closed (afterFits.mono increase)
  | request child ih => exact .request ih
  | bind firstTrace lastTrace firstIH lastIH => exact .bind firstIH lastIH
  | hit found fits => exact .hit found (fits.mono increase)
  | miss absent bodyTrace ih => exact .miss absent ih

private theorem trace_heaps {clear : Guard → Bool} {top : Guard} {bound : Nat}
    {actual : MeasuredRun clear top cost code before memo output after saved}
    (trace : Trace bound actual) : Fits bound before ∧ Fits bound after := by
  induction trace using Trace.rec
      (motive_2 := fun _ _ before _ _ after _ _ _ => Fits bound before ∧ Fits bound after) with
  | pure value state memo fits => exact ⟨fits, fits⟩
  | work job state memo beforeFits afterFits => exact ⟨beforeFits, afterFits⟩
  | select oldFuel done semantic beforeFits available closed afterFits => exact ⟨beforeFits, afterFits⟩
  | request child ih => exact ih
  | bind firstTrace lastTrace firstIH lastIH => exact ⟨firstIH.1, lastIH.2⟩
  | hit found fits => exact ⟨fits, fits⟩
  | miss absent bodyTrace ih => exact ih

private theorem call_heaps {clear : Guard → Bool} {top : Guard} {bound : Nat}
    {actual : MeasuredCall clear top cost input before memo output after saved}
    (trace : CallTrace bound actual) : Fits bound before ∧ Fits bound after := by
  induction trace using CallTrace.rec
      (motive_1 := fun {Output} _ _ before _ _ after _ _ _ => Fits bound before ∧ Fits bound after) with
  | pure value state memo fits => exact ⟨fits, fits⟩
  | work job state memo beforeFits afterFits => exact ⟨beforeFits, afterFits⟩
  | select oldFuel done semantic beforeFits available closed afterFits => exact ⟨beforeFits, afterFits⟩
  | request child ih => exact ih
  | bind firstTrace lastTrace firstIH lastIH => exact ⟨firstIH.1, lastIH.2⟩
  | hit found fits => exact ⟨fits, fits⟩
  | miss absent bodyTrace ih => exact ih

/-- The exact initial instruction heap satisfies the recorded envelope. -/
theorem Trace.initial_fits {clear : Guard → Bool} {top : Guard} {bound : Nat}
    {actual : MeasuredRun clear top cost code before memo output after saved}
    (trace : Trace bound actual) : Fits bound before := (trace_heaps trace).1

/-- The exact final instruction heap satisfies the recorded envelope. -/
theorem Trace.final_fits {clear : Guard → Bool} {top : Guard} {bound : Nat}
    {actual : MeasuredRun clear top cost code before memo output after saved}
    (trace : Trace bound actual) : Fits bound after := (trace_heaps trace).2

/-- The exact initial call heap satisfies the recorded envelope. -/
theorem CallTrace.initial_fits {clear : Guard → Bool} {top : Guard} {bound : Nat}
    {actual : MeasuredCall clear top cost input before memo output after saved}
    (trace : CallTrace bound actual) : Fits bound before := (call_heaps trace).1

/-- The exact final call heap satisfies the recorded envelope. -/
theorem CallTrace.final_fits {clear : Guard → Bool} {top : Guard} {bound : Nat}
    {actual : MeasuredCall clear top cost input before memo output after saved}
    (trace : CallTrace bound actual) : Fits bound after := (call_heaps trace).2

/-- The scalar envelope computes one exact selection fuel for the completed instruction graph. -/
theorem Trace.selection_ready {clear : Guard → Bool} {top : Guard} {bound : Nat}
    {actual : MeasuredRun clear top cost code before memo output after saved}
    (trace : Trace bound actual) :
    SelectionReady (SourceMergedComparisonNumeric.comparisonFuel bound bound bound) actual := by
  induction trace using Trace.rec
      (motive_2 := fun _ input before memo output after saved actual _ =>
        @CallSelectionReady Symbol Guard symbolEq edgeEq clear top
          (SourceMergedComparisonNumeric.comparisonFuel bound bound bound) _ input before memo output after saved actual) with
  | pure value state memo fits => exact .pure value state memo
  | work job state memo beforeFits afterFits => exact .work job state memo
  | select oldFuel done semantic beforeFits available closed afterFits =>
      exact .select oldFuel done
        (SourceCurrentMemoMergeResourceControl.selection_replay clear oldFuel _ _ bound semantic beforeFits available closed _ _ done).2.2.1
  | request child ih => exact .request ih
  | bind firstTrace lastTrace firstIH lastIH => exact .bind firstIH lastIH
  | hit found fits => exact .hit found
  | miss absent bodyTrace ih => exact .miss absent ih

/-- The scalar envelope computes one exact selection fuel for the completed call graph. -/
theorem CallTrace.selection_ready {clear : Guard → Bool} {top : Guard} {bound : Nat}
    {actual : MeasuredCall clear top cost input before memo output after saved}
    (trace : CallTrace bound actual) :
    CallSelectionReady (SourceMergedComparisonNumeric.comparisonFuel bound bound bound) actual := by
  induction trace using CallTrace.rec
      (motive_1 := fun {Output} _ code before memo output after saved actual _ =>
        @SelectionReady Symbol Guard symbolEq edgeEq clear top
          (SourceMergedComparisonNumeric.comparisonFuel bound bound bound) Output _ code before memo output after saved actual) with
  | pure value state memo fits => exact .pure value state memo
  | work job state memo beforeFits afterFits => exact .work job state memo
  | select oldFuel done semantic beforeFits available closed afterFits =>
      exact .select oldFuel done
        (SourceCurrentMemoMergeResourceControl.selection_replay clear oldFuel _ _ bound semantic beforeFits available closed _ _ done).2.2.1
  | request child ih => exact .request ih
  | bind firstTrace lastTrace firstIH lastIH => exact .bind firstIH lastIH
  | hit found fits => exact .hit found
  | miss absent bodyTrace ih => exact .miss absent ih

end MicroCFTA.SourceCurrentMemoMergeResourceTrace
