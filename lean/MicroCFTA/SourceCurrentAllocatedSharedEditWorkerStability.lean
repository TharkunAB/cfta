import MicroCFTA.SourceCurrentAllocatedSharedEditWorker
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Successful checked edit execution under larger bounds

The six execution bounds can increase after a literal successful return.
The result and the entire shared state remain exact. The proof follows
the actual constructor and head-read branches. It uses no physical input
plan, language law, or future body-completion premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability
open InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph (SharedState)
open SourceCurrentAllocatedSharedEditWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem bind_transport {Input Output : Type}
    (first other : Outcome width Input)
    (next later : Input → SharedState width → Outcome width Output)
    (firstPreserved : ∀ value state, first = .done value state → other = .done value state)
    (continuation : ∀ value state result after,
      next value state = .done result after → later value state = .done result after)
    {result : Output} {after : SharedState width}
    (actual : first.bind next = .done result after) : other.bind later = .done result after := by
  cases first with
  | done value state =>
      simp only [Outcome.bind] at actual
      simp only [firstPreserved value state rfl, Outcome.bind]
      exact continuation value state result after actual
  | failed => cases actual

/-- Actual shared target and native success retain the exact lifted edit return. -/
theorem leaf_done_stable
    {p h m s n largerP largerH largerM largerS largerN : Nat}
    {record : Record} {originals : List (Value Symbol Guard)} {target : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : SharedState width}
    (actual : leaf p h m s n record originals target input before = .done result after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) (enoughM : m ≤ largerM)
    (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    leaf largerP largerH largerM largerS largerN record originals target input before = .done result after := by
  cases executed : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals target input before with
  | done value state =>
      have stable := SourceCurrentAllocatedSharedTargetWorkerStability.leaf_done_stable executed
        enoughP enoughH enoughM enoughS enoughN
      simp only [leaf, lift, executed] at actual
      simpa only [leaf, stable, lift] using actual
  | failed =>
      simp only [leaf, executed, lift] at actual
      cases actual

omit [DecidableEq Symbol] in
/-- Actual stored unfolding and node construction retain a successful head under more read fuel. -/
theorem head_done_stable {h largerH : Nat} {input result : Value Symbol Guard}
    {before after : SharedState width}
    (actual : head h input before = .done result after) (enough : h ≤ largerH) :
    head largerH input before = .done result after := by
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges h input before.checked.native.machine.heap with
  | done edges heap =>
      have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable h (largerH - h) input
        before.checked.native.machine.heap (by simp only [exposed, MergedSourceExposure.Finished])
      rw [show h + (largerH - h) = largerH by omega] at stable
      have same := stable.trans exposed
      simp only [head, SourceEqualityRequiredWorker.head, exposed, SourceEqualityRequiredWorker.work] at actual
      simpa only [head, SourceEqualityRequiredWorker.head, same, SourceEqualityRequiredWorker.work] using actual
  | pending | unresolved | exhausted =>
      simp only [head, SourceEqualityRequiredWorker.head, exposed] at actual
      cases actual

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Success transport for child scans follows only the selected actual recursive calls. -/
theorem children_done_stable
    (recur later : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width → Outcome width (Value Symbol Guard))
    (preserves : ∀ edits value before result after,
      recur edits value before = .done result after → later edits value before = .done result after)
    (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat) (values : List (Value Symbol Guard))
    {before after : SharedState width} {results : List (Value Symbol Guard)}
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
      | some edits =>
          simp only [children, selected] at actual ⊢
          apply bind_transport _ _ _ _ (fun _ _ returned => preserves _ _ _ _ _ returned) _ actual
          intro result middle outputs final returned
          exact bind_transport _ _ _ _ (fun _ _ done => ih _ done)
            (fun _ _ _ _ done => done) returned

omit [DecidableEq Symbol] in
/-- Row success retains each raw constructor request between child scans and the suffix. -/
theorem rows_done_stable
    (recur later : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width → Outcome width (Value Symbol Guard))
    (preserves : ∀ edits value before result after,
      recur edits value before = .done result after → later edits value before = .done result after)
    (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    {before after : SharedState width} {results : List (EdgeValue Symbol Guard)}
    (actual : rows recur entries edges before = .done results after) :
    rows later entries edges before = .done results after := by
  induction edges generalizing before results after with
  | nil => exact actual
  | cons edge edges ih =>
      simp only [rows] at actual ⊢
      apply bind_transport _ _ _ _ (fun _ _ returned => children_done_stable recur later preserves _ _ _ returned) _ actual
      intro values middle outputs final returned
      apply bind_transport _ _ _ _ (fun _ _ done => done) _ returned
      intro result afterEdge outputs final returned
      exact bind_transport _ _ _ _ (fun _ _ done => ih done)
        (fun _ _ _ _ done => done) returned

/-- Increasing all six bounds retains any successful node edit and its whole shared state. -/
theorem edit_done_stable
    {e p h m s n largerE largerP largerH largerM largerS largerN : Nat}
    {record : Record} {originals : List (Value Symbol Guard)}
    {edits : Edits EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : SharedState width}
    (actual : edit record originals e p h m s n edits input before = .done result after)
    (enoughE : e ≤ largerE) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    edit record originals largerE largerP largerH largerM largerS largerN edits input before = .done result after := by
  induction e generalizing largerE edits input before result after with
  | zero => cases actual
  | succ e ih =>
      cases largerE with
      | zero => omega
      | succ remaining =>
          cases edits with
          | editAt target => exact leaf_done_stable actual enoughP enoughH enoughM enoughS enoughN
          | editBelow entries =>
              cases input with
              | empty => exact actual
              | reference => cases actual
              | node entry edges depth free =>
                  simp only [edit] at actual ⊢
                  exact bind_transport _ _ _ _ (fun _ _ returned => rows_done_stable _ _
                    (fun _ _ _ _ _ done => ih done (by omega)) _ _ returned)
                    (fun _ _ _ _ returned => returned) actual
              | mu entry body depth ordinary | union entry members depth free =>
                  simp only [edit] at actual ⊢
                  exact bind_transport _ _ _ _ (fun _ _ returned => head_done_stable returned enoughH)
                    (fun _ _ _ _ returned => ih returned (by omega)) actual

/-- Larger actual edit callbacks retain every successful ordered child scan. -/
theorem children_edit_done_stable
    {e p h m s n largerE largerP largerH largerM largerS largerN : Nat}
    {record : Record} {originals values results : List (Value Symbol Guard)}
    {entries : List (Int × Edits EqualityNormalize.Path)} {index : Nat} {before after : SharedState width}
    (actual : children (edit record originals e p h m s n) entries index values before = .done results after)
    (enoughE : e ≤ largerE) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    children (edit record originals largerE largerP largerH largerM largerS largerN) entries index values before = .done results after :=
  children_done_stable _ _ (fun _ _ _ _ _ done =>
    edit_done_stable done enoughE enoughP enoughH enoughM enoughS enoughN) entries index values actual

/-- Larger actual edit callbacks retain every successful ordered raw row rebuild. -/
theorem rows_edit_done_stable
    {e p h m s n largerE largerP largerH largerM largerS largerN : Nat}
    {record : Record} {originals : List (Value Symbol Guard)} {edges results : List (EdgeValue Symbol Guard)}
    {entries : List (Int × Edits EqualityNormalize.Path)} {before after : SharedState width}
    (actual : rows (edit record originals e p h m s n) entries edges before = .done results after)
    (enoughE : e ≤ largerE) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    rows (edit record originals largerE largerP largerH largerM largerS largerN) entries edges before = .done results after :=
  rows_done_stable _ _ (fun _ _ _ _ _ done =>
    edit_done_stable done enoughE enoughP enoughH enoughM enoughS enoughN) entries edges actual

/-- Increasing all six bounds retains a successful child-list edit, including an ignored root leaf. -/
theorem editList_done_stable
    {e p h m s n largerE largerP largerH largerM largerS largerN : Nat}
    {record : Record} {originals values results : List (Value Symbol Guard)}
    {edits : Edits EqualityNormalize.Path} {before after : SharedState width}
    (actual : editList (edit record originals e p h m s n) edits values before = .done results after)
    (enoughE : e ≤ largerE) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    editList (edit record originals largerE largerP largerH largerM largerS largerN) edits values before = .done results after := by
  cases edits with
  | editAt => exact actual
  | editBelow entries =>
      exact children_done_stable _ _ (fun _ _ _ _ _ done =>
        edit_done_stable done enoughE enoughP enoughH enoughM enoughS enoughN) entries 0 values actual

/-- Literal compiled edits retain a successful list and every shared state field under larger bounds. -/
theorem editAll_done_stable
    {e p h m s n largerE largerP largerH largerM largerS largerN : Nat}
    {record : Record} {originals values results : List (Value Symbol Guard)}
    {edits : List (Path × EqualityNormalize.Path)} {before after : SharedState width}
    (actual : editAll record originals e p h m s n edits values before = .done results after)
    (enoughE : e ≤ largerE) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    editAll record originals largerE largerP largerH largerM largerS largerN edits values before = .done results after :=
  editList_done_stable actual enoughE enoughP enoughH enoughM enoughS enoughN

/-- Successful node-edit bounds identify the same result and complete shared state. -/
theorem edit_done_unique
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    {record : Record} {originals : List (Value Symbol Guard)} {edits : Edits EqualityNormalize.Path}
    {input first second : Value Symbol Guard} {before after later : SharedState width}
    (one : edit record originals e p h m s n edits input before = .done first after)
    (two : edit record originals otherE otherP otherH otherM otherS otherN edits input before = .done second later) :
    first = second ∧ after = later := by
  have firstStable := edit_done_stable one (Nat.le_max_left e otherE) (Nat.le_max_left p otherP)
    (Nat.le_max_left h otherH) (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := edit_done_stable two (Nat.le_max_right e otherE) (Nat.le_max_right p otherP)
    (Nat.le_max_right h otherH) (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Successful actual child scans identify the ordered results and whole shared state. -/
theorem children_edit_done_unique
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    {record : Record} {originals values first second : List (Value Symbol Guard)}
    {entries : List (Int × Edits EqualityNormalize.Path)} {index : Nat} {before after later : SharedState width}
    (one : children (edit record originals e p h m s n) entries index values before = .done first after)
    (two : children (edit record originals otherE otherP otherH otherM otherS otherN) entries index values before = .done second later) :
    first = second ∧ after = later := by
  have firstStable := children_edit_done_stable one (Nat.le_max_left e otherE) (Nat.le_max_left p otherP)
    (Nat.le_max_left h otherH) (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := children_edit_done_stable two (Nat.le_max_right e otherE) (Nat.le_max_right p otherP)
    (Nat.le_max_right h otherH) (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Successful actual row rebuilds identify the ordered rows and whole shared state. -/
theorem rows_edit_done_unique
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    {record : Record} {originals : List (Value Symbol Guard)} {edges first second : List (EdgeValue Symbol Guard)}
    {entries : List (Int × Edits EqualityNormalize.Path)} {before after later : SharedState width}
    (one : rows (edit record originals e p h m s n) entries edges before = .done first after)
    (two : rows (edit record originals otherE otherP otherH otherM otherS otherN) entries edges before = .done second later) :
    first = second ∧ after = later := by
  have firstStable := rows_edit_done_stable one (Nat.le_max_left e otherE) (Nat.le_max_left p otherP)
    (Nat.le_max_left h otherH) (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := rows_edit_done_stable two (Nat.le_max_right e otherE) (Nat.le_max_right p otherP)
    (Nat.le_max_right h otherH) (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Successful child-list bounds identify the same ordered values and complete shared state. -/
theorem editList_done_unique
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    {record : Record} {originals values first second : List (Value Symbol Guard)}
    {edits : Edits EqualityNormalize.Path} {before after later : SharedState width}
    (one : editList (edit record originals e p h m s n) edits values before = .done first after)
    (two : editList (edit record originals otherE otherP otherH otherM otherS otherN) edits values before = .done second later) :
    first = second ∧ after = later := by
  have firstStable := editList_done_stable one (Nat.le_max_left e otherE) (Nat.le_max_left p otherP)
    (Nat.le_max_left h otherH) (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := editList_done_stable two (Nat.le_max_right e otherE) (Nat.le_max_right p otherP)
    (Nat.le_max_right h otherH) (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Successful compiled-edit bounds identify the same ordered values and complete shared state. -/
theorem editAll_done_unique
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    {record : Record} {originals values first second : List (Value Symbol Guard)}
    {edits : List (Path × EqualityNormalize.Path)} {before after later : SharedState width}
    (one : editAll record originals e p h m s n edits values before = .done first after)
    (two : editAll record originals otherE otherP otherH otherM otherS otherN edits values before = .done second later) :
    first = second ∧ after = later :=
  editList_done_unique one two

end MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability
