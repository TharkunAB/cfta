import MicroCFTA.SourceEqualityRequiredExecution
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Successful required-path execution under larger bounds

Increasing the worker and head-read bounds preserves each supplied success.
The ordered values and the complete constructor heap remain exact.
The proof follows actual selected calls and rejected rows. It needs no
closedness, availability, language, or future completion premise.
-/
namespace MicroCFTA.SourceEqualityRequiredWorkerStability
open InternedConstructorTemplates SourceEqualityNeeded
open SourceEqualityRequiredWorker

private theorem bind_transport {A B : Type}
    (first other : Result Symbol Guard A)
    (next later : A → State Symbol Guard → Result Symbol Guard B)
    (firstPreserved : ∀ value state, first = .done value state → other = .done value state)
    (continuation : ∀ value state result after,
      next value state = .done result after → later value state = .done result after)
    {result : B} {after : State Symbol Guard}
    (actual : first.bind next = .done result after) : other.bind later = .done result after := by
  cases first with
  | done value state =>
      simp only [Result.bind] at actual
      simp only [firstPreserved value state rfl, Result.bind]
      exact continuation value state result after actual
  | pending | unresolved | exhausted => cases actual

/-- More read fuel preserves a completed literal head and its constructor heap. -/
theorem head_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {h H : Nat} {input result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : head h input before = .done result after) (enough : h ≤ H) :
    head H input before = .done result after := by
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges h input before with
  | done edges heap =>
      have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable h (H - h) input before
        (by simp only [exposed, MergedSourceExposure.Finished])
      rw [show h + (H - h) = H by omega] at stable
      have same := stable.trans exposed
      simp only [head, exposed, work] at actual
      simpa only [head, same, work] using actual
  | pending | unresolved | exhausted =>
      simp only [head, exposed] at actual
      cases actual

/-- Child success transport changes only selected callbacks at their actual return states. -/
theorem children_done_stable
    (recur later : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (preserves : ∀ needed value before result after,
      recur needed value before = .done result after → later needed value before = .done result after)
    (entries : List (Int × Needed)) (index : Nat) (values : List (Value Symbol Guard))
    {before after : State Symbol Guard} {results : List (Value Symbol Guard)}
    (actual : children recur entries index values before = .done results after) :
    children later entries index values before = .done results after := by
  induction values generalizing index before results after with
  | nil => exact actual
  | cons value values ih =>
      cases selected : SourceEqualityNeededMap.lookup (index : Int) entries with
      | none =>
          simp only [children, selected] at actual ⊢
          exact bind_transport _ _ _ _ (fun _ _ returned => ih _ returned)
            (fun _ _ _ _ returned => returned) actual
      | some needed =>
          simp only [children, selected] at actual ⊢
          apply bind_transport _ _ _ _ (fun _ _ returned => preserves _ _ _ _ _ returned) _ actual
          intro result middle outputs final returned
          exact bind_transport _ _ _ _ (fun _ _ done => ih _ done)
            (fun _ _ _ _ done => done) returned

/-- Row success transport preserves rejected rows and each actual raw reconstruction. -/
theorem rows_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    (recur later : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (preserves : ∀ needed value before result after,
      recur needed value before = .done result after → later needed value before = .done result after)
    (entries : List (Int × Needed)) (edges : List (EdgeValue Symbol Guard))
    {before after : State Symbol Guard} {results : List (EdgeValue Symbol Guard)}
    (actual : rows recur entries edges before = .done results after) :
    rows later entries edges before = .done results after := by
  induction edges generalizing before results after with
  | nil => exact actual
  | cons edge edges ih =>
      by_cases matching : fits (.node entries) edge.children.length = true
      · simp only [rows, matching, ite_true] at actual ⊢
        apply bind_transport _ _ _ _ (fun _ _ returned => children_done_stable recur later preserves _ _ _ returned) _ actual
        intro values middle outputs final returned
        apply bind_transport _ _ _ _ (fun _ _ done => done) _ returned
        intro result afterEdge outputs final returned
        exact bind_transport _ _ _ _ (fun _ _ done => ih done)
          (fun _ _ _ _ done => done) returned
      · simp only [rows, matching] at actual ⊢
        exact ih actual

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Larger worker and head bounds preserve a completed actual required node. -/
theorem require_done_stable {r h R H : Nat} {needed : Needed} {value result : Value Symbol Guard}
    {before after : State Symbol Guard}
    (actual : require r h needed value before = .done result after) (enoughR : r ≤ R) (enoughH : h ≤ H) :
    require R H needed value before = .done result after := by
  induction r generalizing R needed value before result after with
  | zero => cases actual
  | succ r ih =>
      cases R with
      | zero => omega
      | succ remaining =>
          cases needed with
          | node entries =>
              by_cases empty : entries.isEmpty = true
              · simpa only [require, empty, ite_true] using actual
              · cases value with
                | empty => exact actual
                | reference =>
                    simp only [require, empty] at actual
                    cases actual
                | node entry edges depth free =>
                    simp only [require, empty] at actual ⊢
                    exact bind_transport _ _ _ _ (fun _ _ returned => rows_done_stable _ _
                      (fun _ _ _ _ _ done => ih done (by omega)) _ _ returned)
                      (fun _ _ _ _ returned => returned) actual
                | mu entry body depth ordinary | union entry members depth free =>
                    simp only [require, empty] at actual ⊢
                    exact bind_transport _ _ _ _ (fun _ _ returned => head_done_stable returned enoughH)
                      (fun _ _ _ _ returned => ih returned (by omega)) actual

/-- Larger actual required-node bounds preserve the selected child sequence. -/
theorem children_require_done_stable {r h R H : Nat} {entries : List (Int × Needed)} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : children (require r h) entries index values before = .done results after)
    (enoughR : r ≤ R) (enoughH : h ≤ H) :
    children (require R H) entries index values before = .done results after :=
  children_done_stable _ _ (fun _ _ _ _ _ done => require_done_stable done enoughR enoughH) entries index values actual

/-- Larger actual required-node bounds preserve row filtering and reconstruction. -/
theorem rows_require_done_stable {r h R H : Nat} {entries : List (Int × Needed)}
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : rows (require r h) entries edges before = .done results after)
    (enoughR : r ≤ R) (enoughH : h ≤ H) :
    rows (require R H) entries edges before = .done results after :=
  rows_done_stable _ _ (fun _ _ _ _ _ done => require_done_stable done enoughR enoughH) entries edges actual

/-- Larger bounds preserve the literal source entry at its exact compiled Needed map. -/
theorem requireAll_done_stable {r h R H : Nat} {paths : List Path}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll r h paths values before = .done results after)
    (enoughR : r ≤ R) (enoughH : h ≤ H) :
    SourceEqualityRequiredExecution.requireAll R H paths values before = .done results after := by
  cases compiled : build paths with
  | node entries =>
      simp only [SourceEqualityRequiredExecution.requireAll, compiled] at actual ⊢
      exact children_require_done_stable actual enoughR enoughH

/-- Successful node bounds identify both the result and complete constructor heap. -/
theorem require_done_unique {r h R H : Nat} {needed : Needed} {value first second : Value Symbol Guard}
    {before after later : State Symbol Guard}
    (one : require r h needed value before = .done first after)
    (two : require R H needed value before = .done second later) : first = second ∧ after = later := by
  have left := require_done_stable one (Nat.le_max_left r R) (Nat.le_max_left h H)
  have right := require_done_stable two (Nat.le_max_right r R) (Nat.le_max_right h H)
  exact Result.done.inj (left.symm.trans right)

/-- Successful child bounds identify the ordered values and complete constructor heap. -/
theorem children_require_done_unique {r h R H : Nat} {entries : List (Int × Needed)} {index : Nat}
    {values first second : List (Value Symbol Guard)} {before after later : State Symbol Guard}
    (one : children (require r h) entries index values before = .done first after)
    (two : children (require R H) entries index values before = .done second later) : first = second ∧ after = later := by
  have left := children_require_done_stable one (Nat.le_max_left r R) (Nat.le_max_left h H)
  have right := children_require_done_stable two (Nat.le_max_right r R) (Nat.le_max_right h H)
  exact Result.done.inj (left.symm.trans right)

/-- Successful row bounds identify the rebuilt edges and complete constructor heap. -/
theorem rows_require_done_unique {r h R H : Nat} {entries : List (Int × Needed)}
    {edges first second : List (EdgeValue Symbol Guard)} {before after later : State Symbol Guard}
    (one : rows (require r h) entries edges before = .done first after)
    (two : rows (require R H) entries edges before = .done second later) : first = second ∧ after = later := by
  have left := rows_require_done_stable one (Nat.le_max_left r R) (Nat.le_max_left h H)
  have right := rows_require_done_stable two (Nat.le_max_right r R) (Nat.le_max_right h H)
  exact Result.done.inj (left.symm.trans right)

/-- Successful source-entry bounds identify the complete child list and constructor heap. -/
theorem requireAll_done_unique {r h R H : Nat} {paths : List Path}
    {values first second : List (Value Symbol Guard)} {before after later : State Symbol Guard}
    (one : SourceEqualityRequiredExecution.requireAll r h paths values before = .done first after)
    (two : SourceEqualityRequiredExecution.requireAll R H paths values before = .done second later) :
    first = second ∧ after = later := by
  have left := requireAll_done_stable one (Nat.le_max_left r R) (Nat.le_max_left h H)
  have right := requireAll_done_stable two (Nat.le_max_right r R) (Nat.le_max_right h H)
  exact Result.done.inj (left.symm.trans right)

end MicroCFTA.SourceEqualityRequiredWorkerStability
