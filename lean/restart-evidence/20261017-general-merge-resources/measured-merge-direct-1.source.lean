import MicroCFTA.SourceCurrentMemoMergeWorkerProofs

/-!
# Exact additive costs for completed memo-aware Merge graphs

Measured graphs retain the literal code, heap, result, and completed memo.
Each instruction adds one unit. Bind counts both executed stages. Worker
replay uses one shared selection certificate at the actual selection sites.
This structural certificate does not supply an initial Merge resource bound.
-/
namespace MicroCFTA.SourceCurrentMemoMergeMeasured
open InternedConstructorTemplates
open SourceCurrentMemoMergeGraph (Code Memo body winner remember)
open SourceCurrentMemoMergeWorker (execute call Outcome)
variable {Symbol Guard : Type}

mutual
/-- Every literal executed instruction contributes to the additive graph cost. -/
inductive MeasuredRun [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
    {Output : Type} → Nat → Code Symbol Guard Output → State Symbol Guard → Memo Symbol Guard →
      Output → State Symbol Guard → Memo Symbol Guard → Prop where
  /-- A pure return executes one instruction. -/
  | pure (value : Output) (state : State Symbol Guard) (memo : Memo Symbol Guard) :
      MeasuredRun clear top 1 (.pure value) state memo value state memo
  /-- A physical Work instruction retains its literal returned heap. -/
  | work (job : Work Symbol Guard Output) (state : State Symbol Guard) (memo : Memo Symbol Guard) :
      MeasuredRun clear top 1 (.work job) state memo (run job state).1 (run job state).2 memo
  /-- A selection records its actual local comparison receipt. -/
  | select (fuel : Nat) (done : SourceMergedSelection.select clear fuel inputs before = .done values after) :
      MeasuredRun clear top 1 (.select inputs) before memo values after memo
  /-- A recursive instruction pays its completed child call and the instruction itself. -/
  | request (actual : MeasuredCall clear top cost input before memo output after saved) :
      MeasuredRun clear top (cost + 1) (.request input) before memo output after saved
  /-- Sequential cost includes both executed stages and the bind instruction. -/
  | bind (first : MeasuredRun clear top firstCost code before memo value middle current)
      (later : MeasuredRun clear top lastCost (next value) middle current output after saved) :
      MeasuredRun clear top (firstCost + lastCost + 1) (.bind code next) before memo output after saved

/-- A measured call retains the exact current-winner reread after its body. -/
inductive MeasuredCall [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
    Nat → Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Value Symbol Guard →
      State Symbol Guard → Memo Symbol Guard → Prop where
  /-- A warm lookup executes one call without a body. -/
  | hit (found : memo input.referenceOf = some entry) :
      MeasuredCall clear top 1 input before memo entry.result before memo
  /-- A miss pays its literal recursive body and call instruction. -/
  | miss (absent : memo input.referenceOf = none)
      (actual : MeasuredRun clear top cost (body top input) before memo candidate after current) :
      MeasuredCall clear top (cost + 1) input before memo (winner current input candidate).result after (remember current input candidate)
end

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Removing the cost retains exactly the original completed instruction graph. -/
theorem MeasuredRun.erase {clear : Guard → Bool} {top : Guard} {cost : Nat} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : MeasuredRun clear top cost code before memo output after saved) :
    SourceCurrentMemoMergeGraph.Run clear top code before memo output after saved := by
  induction actual using MeasuredRun.rec
      (motive_2 := fun _ input before memo output after saved _ => SourceCurrentMemoMergeGraph.Call clear top input before memo output after saved) with
  | pure => exact .pure _ _ _
  | work => exact .work _ _ _
  | select fuel done => exact .select fuel done
  | request actual ih => exact .request ih
  | bind first later firstIH laterIH => exact .bind firstIH laterIH
  | hit found => exact .hit found
  | miss absent actual ih => exact .miss absent ih

/-- Removing the cost retains the exact hit or current-winner miss observation. -/
theorem MeasuredCall.erase {clear : Guard → Bool} {top : Guard} {cost : Nat} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : MeasuredCall clear top cost input before memo output after saved) :
    SourceCurrentMemoMergeGraph.Call clear top input before memo output after saved := by
  induction actual using MeasuredCall.rec
      (motive_1 := fun {_} _ code before memo output after saved _ => SourceCurrentMemoMergeGraph.Run clear top code before memo output after saved) with
  | pure => exact .pure _ _ _
  | work => exact .work _ _ _
  | select fuel done => exact .select fuel done
  | request actual ih => exact .request ih
  | bind first later firstIH laterIH => exact .bind firstIH laterIH
  | hit found => exact .hit found
  | miss absent actual ih => exact .miss absent ih

/-- Every supplied actual instruction graph has an exact finite additive cost. -/
theorem of_run {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : SourceCurrentMemoMergeGraph.Run clear top code before memo output after saved) :
    ∃ cost, MeasuredRun clear top cost code before memo output after saved := by
  induction actual using SourceCurrentMemoMergeGraph.Run.rec
      (motive_2 := fun input before memo output after saved _ => ∃ cost, MeasuredCall clear top cost input before memo output after saved) with
  | pure => exact ⟨1, .pure _ _ _⟩
  | work => exact ⟨1, .work _ _ _⟩
  | select fuel done => exact ⟨1, .select fuel done⟩
  | request actual ih => obtain ⟨cost, measured⟩ := ih; exact ⟨cost + 1, .request measured⟩
  | bind first later firstIH laterIH =>
      obtain ⟨firstCost, firstMeasured⟩ := firstIH
      obtain ⟨lastCost, lastMeasured⟩ := laterIH
      exact ⟨firstCost + lastCost + 1, .bind firstMeasured lastMeasured⟩
  | hit found => exact ⟨1, .hit found⟩
  | miss absent actual ih => obtain ⟨cost, measured⟩ := ih; exact ⟨cost + 1, .miss absent measured⟩

/-- Every supplied actual completed request has an exact finite additive cost. -/
theorem of_call {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : SourceCurrentMemoMergeGraph.Call clear top input before memo output after saved) :
    ∃ cost, MeasuredCall clear top cost input before memo output after saved := by
  induction actual using SourceCurrentMemoMergeGraph.Call.rec
      (motive_1 := fun {_} code before memo output after saved _ => ∃ cost, MeasuredRun clear top cost code before memo output after saved) with
  | pure => exact ⟨1, .pure _ _ _⟩
  | work => exact ⟨1, .work _ _ _⟩
  | select fuel done => exact ⟨1, .select fuel done⟩
  | request actual ih => obtain ⟨cost, measured⟩ := ih; exact ⟨cost + 1, .request measured⟩
  | bind first later firstIH laterIH =>
      obtain ⟨firstCost, firstMeasured⟩ := firstIH
      obtain ⟨lastCost, lastMeasured⟩ := laterIH
      exact ⟨firstCost + lastCost + 1, .bind firstMeasured lastMeasured⟩
  | hit found => exact ⟨1, .hit found⟩
  | miss absent actual ih => obtain ⟨cost, measured⟩ := ih; exact ⟨cost + 1, .miss absent measured⟩

mutual
/-- Only the actually demanded selection sites require a shared comparison receipt. -/
def SelectionReady {clear : Guard → Bool} {top : Guard} {cost : Nat} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (selectionFuel : Nat) (actual : MeasuredRun clear top cost code before memo output after saved) : Prop :=
  match actual with
  | .pure .. | .work .. => True
  | .select _ _ => SourceMergedSelection.select clear selectionFuel _ before = .done output after
  | .request child => CallSelectionReady selectionFuel child
  | .bind first later => SelectionReady selectionFuel first ∧ SelectionReady selectionFuel later

/-- Hits need no selection receipt; misses use only their actual body's certificate. -/
def CallSelectionReady {clear : Guard → Bool} {top : Guard} {cost : Nat} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (selectionFuel : Nat) (actual : MeasuredCall clear top cost input before memo output after saved) : Prop :=
  match actual with
  | .hit .. => True
  | .miss _ actual => SelectionReady selectionFuel actual
end

private theorem replay (cost : Nat) {clear : Guard → Bool} {top : Guard} :
    (∀ {Output : Type} {code : Code Symbol Guard Output} {before after : State Symbol Guard}
      {memo saved : Memo Symbol Guard} {output : Output}
      (actual : MeasuredRun clear top cost code before memo output after saved) (selectionBound : Nat)
      (ready : SelectionReady selectionBound actual) (workFuel selectionFuel : Nat),
      cost ≤ workFuel → selectionBound ≤ selectionFuel →
      execute clear top workFuel selectionFuel code before memo = .done output after saved) ∧
    (∀ {input output : Value Symbol Guard} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
      (actual : MeasuredCall clear top cost input before memo output after saved) (selectionBound : Nat)
      (ready : CallSelectionReady selectionBound actual) (workFuel selectionFuel : Nat),
      cost ≤ workFuel → selectionBound ≤ selectionFuel →
      call clear top workFuel selectionFuel input before memo = .done output after saved) := by
  induction cost using Nat.strong_induction_on with
  | h cost ih =>
      constructor
      · intro Output code before after memo saved output actual selectionBound ready workFuel selectionFuel workEnough selectionEnough
        cases workFuel with
        | zero => cases actual <;> omega
        | succ remaining =>
            cases actual with
            | pure => rfl
            | work => rfl
            | select bound done =>
                have again := SourceCurrentMemoMergeWorkerProofs.selection_stable clear selectionBound selectionFuel _ _ _ _ ready selectionEnough
                simp only [execute, again]
            | request child => exact (ih _ (by omega)).2 child selectionBound ready remaining selectionFuel (by omega) selectionEnough
            | bind first later =>
                have firstDone := (ih _ (by omega)).1 first selectionBound ready.1 remaining selectionFuel (by omega) selectionEnough
                have laterDone := (ih _ (by omega)).1 later selectionBound ready.2 remaining selectionFuel (by omega) selectionEnough
                simpa only [execute, firstDone, Outcome.bind] using laterDone
      · intro input output before after memo saved actual selectionBound ready workFuel selectionFuel workEnough selectionEnough
        cases workFuel with
        | zero => cases actual <;> omega
        | succ remaining =>
            cases actual with
            | hit found => simp only [call, found]
            | miss absent actual =>
                have bodyDone := (ih _ (by omega)).1 actual selectionBound ready remaining selectionFuel (by omega) selectionEnough
                simp only [call, absent, bodyDone, Outcome.bind]

/-- Larger worker and shared selection fuel preserve this exact measured instruction return. -/
theorem run_replay {clear : Guard → Bool} {top : Guard} {cost : Nat} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : MeasuredRun clear top cost code before memo output after saved) (selectionBound : Nat)
    (ready : SelectionReady selectionBound actual) (workFuel selectionFuel : Nat)
    (workEnough : cost ≤ workFuel) (selectionEnough : selectionBound ≤ selectionFuel) :
    execute clear top workFuel selectionFuel code before memo = .done output after saved :=
  (replay cost).1 actual selectionBound ready workFuel selectionFuel workEnough selectionEnough

/-- Larger fuels retain the literal current winner and complete returned memo of a measured call. -/
theorem call_replay {clear : Guard → Bool} {top : Guard} {cost : Nat} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : MeasuredCall clear top cost input before memo output after saved) (selectionBound : Nat)
    (ready : CallSelectionReady selectionBound actual) (workFuel selectionFuel : Nat)
    (workEnough : cost ≤ workFuel) (selectionEnough : selectionBound ≤ selectionFuel) :
    call clear top workFuel selectionFuel input before memo = .done output after saved :=
  (replay cost).2 actual selectionBound ready workFuel selectionFuel workEnough selectionEnough

end MicroCFTA.SourceCurrentMemoMergeMeasured
