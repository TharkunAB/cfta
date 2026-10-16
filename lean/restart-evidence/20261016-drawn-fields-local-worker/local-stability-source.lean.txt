import MicroCFTA.SourceCurrentAllocatedLocalWorker
import MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability
import MicroCFTA.SourceEqualityRequiredWorkerStability

/-!
# Stability and uniqueness of successful local reduction

Successful phase equations determine the same original records, required
forest, and class return. Equality retains the full checked state, fourth
memo, and merge memo. No physical invariant or future body law is needed.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
open Language EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedLocalWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable {width : Nat} {A B : Type}

/-- Successful sequencing exposes the exact complete intermediate return. -/
theorem bind_done_iff (first : Outcome A width)
    (next : A → Checked width → Fourth → Memo → Outcome B width)
    (result : B) (after : Checked width) (fourth : Fourth) (memo : Memo) :
    first.bind next = .done result after fourth memo ↔
      ∃ value middle current warm, first = .done value middle current warm ∧
        next value middle current warm = .done result after fourth memo := by
  cases first with
  | done value checked saved current =>
      constructor
      · intro actual; exact ⟨value, checked, saved, current, rfl, actual⟩
      · rintro ⟨_, _, _, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, _, _, impossible, _⟩; cases impossible

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A successful Scan lift retains exactly its literal record return and the supplied merge memo. -/
theorem scan_done_iff {g s p h n budget : Nat} {records : List Record} {values : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    {result : SourceCurrentAllocatedRecordScanWorker.Result} :
    scan g s p h n budget records values before fourth memo = .done result after savedFourth saved ↔
      SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth =
        .done result after savedFourth ∧ saved = memo := by
  cases actual : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth <;>
    simp [scan, actual, eq_comm, and_assoc]

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- A successful required lift exposes the exact original heap result. -/
theorem required_done_iff {r h : Nat} {paths : List SourceEqualityNeeded.Path}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} :
    required r h paths values before fourth memo = .done results after savedFourth saved ↔
      ∃ heap, SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap = .done results heap ∧
        after = advanceHeap before heap ∧ savedFourth = fourth ∧ saved = memo := by
  cases actual : SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap with
  | done found heap =>
      constructor
      · intro done
        simp only [required, actual] at done
        cases done
        exact ⟨heap, rfl, rfl, rfl, rfl⟩
      · rintro ⟨otherHeap, done, sameState, sameFourth, sameMemo⟩
        obtain ⟨rfl, rfl⟩ := SourceEqualityRequiredWorker.Result.done.inj done
        cases sameState
        cases sameFourth
        cases sameMemo
        simp only [required, actual]
  | pending | unresolved | exhausted => simp [required, actual]

omit [DecidableEq (Value Symbol Guard)] in
/-- A successful class lift retains its exact forest and checked/merge return. -/
theorem pass_done_iff {e p h m c n : Nat} {records : List Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo} :
    pass e p h m c n records values before fourth memo = .done results after savedFourth saved ↔
      SourceCurrentAllocatedClassWorker.pass e p h m c n records values before memo = .done results after saved ∧
        savedFourth = fourth := by
  cases actual : SourceCurrentAllocatedClassWorker.pass e p h m c n records values before memo <;>
    simp [pass, actual, eq_comm, and_left_comm, and_comm]

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- Required executions at any successful bounds identify both the forest and complete constructor heap. -/
theorem requireAll_done_unique {r h R H : Nat} {paths : List SourceEqualityNeeded.Path}
    {values first second : List (Value Symbol Guard)} {before left right : Heap}
    (one : SourceEqualityRequiredExecution.requireAll r h paths values before = .done first left)
    (two : SourceEqualityRequiredExecution.requireAll R H paths values before = .done second right) :
    first = second ∧ left = right := by
  have leftGraph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before first left).mpr ⟨r, h, one⟩
  have rightGraph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before second right).mpr ⟨R, H, two⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at leftGraph rightGraph
      exact SourceEqualityRequiredExecution.children_unique leftGraph rightGraph

omit [DecidableEq (Value Symbol Guard)] in
/-- Required children and the following class pass have one complete successful return. -/
theorem required_pass_done_unique {r e p h m c n R E P H M C N : Nat}
    {records : List Record} {paths : List SourceEqualityNeeded.Path}
    {values first second : List (Value Symbol Guard)} {before left right : Checked width}
    {fourth leftFourth rightFourth : Fourth} {memo leftMemo rightMemo : Memo}
    (one : (required r h paths values before fourth memo).bind
      (fun results checked current warm => pass e p h m c n records results checked current warm) =
        .done first left leftFourth leftMemo)
    (two : (required R H paths values before fourth memo).bind
      (fun results checked current warm => pass E P H M C N records results checked current warm) =
        .done second right rightFourth rightMemo) :
    first = second ∧ left = right ∧ leftFourth = rightFourth ∧ leftMemo = rightMemo := by
  obtain ⟨oneValues, oneState, oneFourth, oneMemo, requiredOne, passOne⟩ := (bind_done_iff _ _ _ _ _ _).mp one
  obtain ⟨twoValues, twoState, twoFourth, twoMemo, requiredTwo, passTwo⟩ := (bind_done_iff _ _ _ _ _ _).mp two
  obtain ⟨oneHeap, lowerOne, rfl, rfl, rfl⟩ := required_done_iff.mp requiredOne
  obtain ⟨twoHeap, lowerTwo, rfl, rfl, rfl⟩ := required_done_iff.mp requiredTwo
  obtain ⟨rfl, rfl⟩ := requireAll_done_unique lowerOne lowerTwo
  obtain ⟨headOne, rfl⟩ := pass_done_iff.mp passOne
  obtain ⟨headTwo, rfl⟩ := pass_done_iff.mp passTwo
  obtain ⟨sameValues, sameState, sameMemo⟩ := SourceCurrentAllocatedClassWorkerStability.pass_done_unique headOne headTwo
  exact ⟨sameValues, sameState, rfl, sameMemo⟩

/-- Any two successful class continuations retain the same complete local return. -/
theorem classes_done_unique {g s r e p h m c n G S R E P H M C N budget : Nat}
    {records : List Record} {values first second : List (Value Symbol Guard)} {before left right : Checked width}
    {fourth leftFourth rightFourth : Fourth} {memo leftMemo rightMemo : Memo}
    (one : classes g s r e p h m c n budget records values before fourth memo = .done first left leftFourth leftMemo)
    (two : classes G S R E P H M C N budget records values before fourth memo = .done second right rightFourth rightMemo) :
    first = second ∧ left = right ∧ leftFourth = rightFourth ∧ leftMemo = rightMemo := by
  obtain ⟨oneResult, oneState, oneFourth, oneMemo, scanOne, restOne⟩ :=
    (bind_done_iff _ _ _ _ _ _).mp one
  obtain ⟨twoResult, twoState, twoFourth, twoMemo, scanTwo, restTwo⟩ :=
    (bind_done_iff _ _ _ _ _ _).mp two
  obtain ⟨lowerOne, rfl⟩ := scan_done_iff.mp scanOne
  obtain ⟨lowerTwo, rfl⟩ := scan_done_iff.mp scanTwo
  obtain ⟨rfl, rfl, rfl⟩ := SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique lowerOne lowerTwo
  cases oneResult with
  | mk outcome kept =>
      cases outcome with
      | none => exact required_pass_done_unique restOne restTwo
      | some paths =>
          cases restOne
          cases restTwo
          exact ⟨rfl, rfl, rfl, rfl⟩

/-- Successful local bounds identify the forest, full checked state, fourth memo, and merge memo. -/
theorem reduce_done_unique {g s r e p h m c n G S R E P H M C N budget : Nat}
    {loaded : Allocated} {inherited : EqValue} {values first second : List (Value Symbol Guard)}
    {before left right : Checked width} {fourth leftFourth rightFourth : Fourth} {memo leftMemo rightMemo : Memo}
    (one : reduce g s r e p h m c n budget loaded inherited values before fourth memo = .done first left leftFourth leftMemo)
    (two : reduce G S R E P H M C N budget loaded inherited values before fourth memo = .done second right rightFourth rightMemo) :
    first = second ∧ left = right ∧ leftFourth = rightFourth ∧ leftMemo = rightMemo := by
  cases actual : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message => simp only [reduce, actual] at one; cases one
  | ok branch =>
      cases branch with
      | unchanged | emptyChildren =>
          simp only [reduce, actual] at one two
          cases one
          cases two
          exact ⟨rfl, rfl, rfl, rfl⟩
      | classes records =>
          simp only [reduce, actual] at one two
          exact classes_done_unique one two

omit [DecidableEq (Value Symbol Guard)] in
/-- Larger required and class bounds retain the complete successful continuation. -/
theorem required_pass_done_stable {r e p h m c n R E P H M C N : Nat}
    {records : List Record} {paths : List SourceEqualityNeeded.Path}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo}
    (actual : (required r h paths values before fourth memo).bind
      (fun values checked current warm => pass e p h m c n records values checked current warm) =
        .done results after savedFourth saved)
    (enoughR : r ≤ R) (enoughE : e ≤ E) (enoughP : p ≤ P) (enoughH : h ≤ H)
    (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    (required R H paths values before fourth memo).bind
      (fun values checked current warm => pass E P H M C N records values checked current warm) =
        .done results after savedFourth saved := by
  obtain ⟨middleValues, middleState, middleFourth, middleMemo, requiredDone, passDone⟩ :=
    (bind_done_iff _ _ _ _ _ _).mp actual
  obtain ⟨heap, lower, rfl, rfl, rfl⟩ := required_done_iff.mp requiredDone
  obtain ⟨last, rfl⟩ := pass_done_iff.mp passDone
  have first := SourceEqualityRequiredWorkerStability.requireAll_done_stable lower enoughR enoughH
  have second := SourceCurrentAllocatedClassWorkerStability.pass_done_stable last
    enoughE enoughP enoughH enoughM enoughC enoughN
  simp only [required, first, Outcome.bind, pass, second]

/-- All larger reached phase bounds preserve the exact successful Scan continuation. -/
theorem classes_done_stable {g s r e p h m c n G S R E P H M C N budget : Nat}
    {records : List Record} {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo}
    (actual : classes g s r e p h m c n budget records values before fourth memo =
      .done results after savedFourth saved)
    (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    classes G S R E P H M C N budget records values before fourth memo = .done results after savedFourth saved := by
  obtain ⟨result, middle, current, warm, first, rest⟩ := (bind_done_iff _ _ _ _ _ _).mp actual
  obtain ⟨lower, rfl⟩ := scan_done_iff.mp first
  have stable := SourceCurrentAllocatedRecordScanWorkerStability.scan_done_stable lower enoughG enoughS enoughP enoughH enoughN
  simp only [classes, scan, stable, Outcome.bind]
  cases result with
  | mk outcome kept =>
      cases outcome with
      | none => exact required_pass_done_stable rest enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      | some => exact rest

/-- Larger bounds preserve the forest and every shared component of a successful local return. -/
theorem reduce_done_stable {g s r e p h m c n G S R E P H M C N budget : Nat}
    {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    (actual : reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .done results after savedFourth saved)
    (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    reduce G S R E P H M C N budget loaded inherited values before fourth memo = .done results after savedFourth saved := by
  cases observed : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message => simp only [reduce, observed] at actual; cases actual
  | ok branch =>
      cases branch with
      | unchanged | emptyChildren => simpa only [reduce, observed] using actual
      | classes records =>
          simp only [reduce, observed] at actual ⊢
          exact classes_done_stable actual enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

end MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
