import MicroCFTA.SourceCurrentMemoMergeComplete
import MicroCFTA.SourceCurrentMergeResultMemo

/-!
# Sequential publication before recursive merge forcing

The source publication table stores a captured producer before its body
is evaluated. The completed map records the evaluation status of those
producers. It is proof state, not another production result cache.

Each body sees its own published producer. A running stack records current
forcing. A force can start only outside that stack. Later proofs must derive
this condition for actual recursive requests. Concurrent evaluation and
literal GHC demand remain separate correspondence obligations.
-/
namespace MicroCFTA.SourceCurrentMemoMergePublishedGraph
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph (Code Memo Entry body)
open SourceCurrentMergeResultMemo (Producer Published Publication)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A serial source insertion retains the first published producer. -/
def publish (table : Published) (input : Value Symbol Guard) (ticket : Nat) : Published :=
  keepFirst table input.referenceOf ⟨ticket, input⟩

/-- Winner reread uses the table after publication. -/
def selected (table : Published) (input : Value Symbol Guard) (ticket : Nat) : Producer :=
  (publish table input ticket input.referenceOf).getD ⟨ticket, input⟩

/-- Publication leaves its selected captured producer present. -/
theorem selected_present (table : Published) (input : Value Symbol Guard) (ticket : Nat) :
    publish table input ticket input.referenceOf = some (selected table input ticket) := by
  obtain ⟨producer, found⟩ := keepFirst_present table input.referenceOf (Producer.mk ticket input)
  simp only [selected, publish, found, Option.getD_some]

/-- The serial prefix is an instance of the existing source lookup, insertion, and reread graph. -/
theorem publication (table : Published) (input : Value Symbol Guard) (ticket : Nat) :
    Publication table input ticket (publish table input ticket) (selected table input ticket) := by
  cases found : table input.referenceOf with
  | some producer =>
      have same : publish table input ticket = table := by simp [publish, keepFirst, found]
      simpa only [same, selected, found, Option.getD_some] using (Publication.hit (ticket := ticket) found)
  | none =>
      simpa only [SourceCurrentMergeResultMemo.publishMany, List.map_nil, updates, selected, publish]
        using (Publication.miss (ticket := ticket) found [] [])

/-- Publication does not delete any captured producer. -/
theorem publish_extends (table : Published) (input : Value Symbol Guard) (ticket : Nat) :
    Extends table (publish table input ticket) := keepFirst_extends _ _ _

mutual
  /-- Instructions thread the published producer table and completed evaluation state separately. -/
  inductive Run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
      List Producer → {Output : Type} → Code Symbol Guard Output → State Symbol Guard → Published → Memo Symbol Guard →
        Output → State Symbol Guard → Published → Memo Symbol Guard → Prop where
    | pure (active : List Producer) (value : Output) (heap : State Symbol Guard) (table : Published) (memo : Memo Symbol Guard) :
        Run clear top active (.pure value) heap table memo value heap table memo
    | work (active : List Producer) (job : Work Symbol Guard Output) (heap : State Symbol Guard) (table : Published) (memo : Memo Symbol Guard) :
        Run clear top active (.work job) heap table memo (run job heap).1 (run job heap).2 table memo
    | select (fuel : Nat) (done : SourceMergedSelection.select clear fuel inputs before = .done values after) :
        Run clear top active (.select inputs) before table memo values after table memo
    | request (actual : Call clear top active input before table memo output after saved completed) :
        Run clear top active (.request input) before table memo output after saved completed
    | bind (first : Run clear top active code before table memo value middle current evaluated)
        (later : Run clear top active (next value) middle current evaluated output after saved completed) :
        Run clear top active (.bind code next) before table memo output after saved completed

  /-- A completed hit returns directly. Other requests publish before forcing the selected captured body. -/
  inductive Call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
      List Producer → Value Symbol Guard → State Symbol Guard → Published → Memo Symbol Guard →
        Value Symbol Guard → State Symbol Guard → Published → Memo Symbol Guard → Prop where
    | hit (published : table input.referenceOf = some producer) (found : memo input.referenceOf = some entry) :
        Call clear top active input before table memo entry.result before table memo
    | force (ticket : Nat)
        (absent : memo (selected table input ticket).original.referenceOf = none)
        (idle : ∀ producer ∈ active, producer.original.referenceOf ≠ (selected table input ticket).original.referenceOf)
        (actual : Run clear top (selected table input ticket :: active)
          (body top (selected table input ticket).original) before (publish table input ticket) memo candidate after current evaluated) :
        Call clear top active input before table memo candidate after current
          (SourceCurrentMemoMergeGraph.remember evaluated (selected table input ticket).original candidate)
end

/-- No instruction removes a published producer. -/
theorem Run.published_extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {active : List Producer} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {table saved : Published} {memo completed : Memo Symbol Guard} {output : Output}
    (actual : Run clear top active code before table memo output after saved completed) : Extends table saved := by
  induction actual using Run.rec
      (motive_2 := fun _ _ _ table _ _ _ saved _ _ => Extends table saved) with
  | pure | work | select => exact extends_refl _
  | request _ ih => exact ih
  | bind _ _ first later => exact extends_trans first later
  | hit => exact extends_refl _
  | force _ _ _ _ ih => exact extends_trans (publish_extends _ _ _) ih

/-- Every source call retains the producer that won its initial publication. -/
theorem Call.published_extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {active : List Producer} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {table saved : Published} {memo completed : Memo Symbol Guard}
    (actual : Call clear top active input before table memo output after saved completed) : Extends table saved :=
  Run.published_extends (.request actual)

/-- Completion leaves every other physical key unchanged. -/
theorem remember_other (memo : Memo Symbol Guard) (input output : Value Symbol Guard) (key : InternedBinderProtocol.NodeRef)
    (different : key ≠ input.referenceOf) :
    SourceCurrentMemoMergeGraph.remember memo input output key = memo key := by
  cases found : memo input.referenceOf <;>
    simp [SourceCurrentMemoMergeGraph.remember, keepFirst, found, put, different]

/-- Instructions cannot change a completed entry at a currently running ancestor key. -/
theorem Run.active_unchanged [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {active : List Producer} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {table saved : Published} {memo completed : Memo Symbol Guard} {output : Output}
    (actual : Run clear top active code before table memo output after saved completed) :
    ∀ producer ∈ active, completed producer.original.referenceOf = memo producer.original.referenceOf := by
  exact Run.rec
      (motive_1 := fun active {_} _ _ _ memo _ _ _ completed _ =>
        ∀ producer ∈ active, completed producer.original.referenceOf = memo producer.original.referenceOf)
      (motive_2 := fun active _ _ _ memo _ _ _ completed _ =>
        ∀ producer ∈ active, completed producer.original.referenceOf = memo producer.original.referenceOf)
      (fun _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl)
      (fun _ ih => ih)
      (fun _ _ first later producer member => (later producer member).trans (first producer member))
      (fun _ _ _ _ => rfl)
      (fun _ _ idle _ ih producer member => by
        exact (remember_other _ _ _ _ (idle producer member)).trans
          (ih producer (List.mem_cons_of_mem _ member)))
      actual

/-- A recursive call retains every completed status at a running ancestor key. -/
theorem Call.active_unchanged [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {active : List Producer} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {table saved : Published} {memo completed : Memo Symbol Guard}
    (actual : Call clear top active input before table memo output after saved completed) :
    ∀ producer ∈ active, completed producer.original.referenceOf = memo producer.original.referenceOf :=
  Run.active_unchanged (.request actual)

/-- A forced body cannot complete its own running producer through a recursive request. -/
theorem force_body_absent [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {active : List Producer} {producer : Producer}
    {before after : State Symbol Guard} {table saved : Published} {memo completed : Memo Symbol Guard} {output : Value Symbol Guard}
    (actual : Run clear top (producer :: active) (body top producer.original) before table memo output after saved completed)
    (absent : memo producer.original.referenceOf = none) : completed producer.original.referenceOf = none :=
  (actual.active_unchanged producer List.mem_cons_self).trans absent

end MicroCFTA.SourceCurrentMemoMergePublishedGraph
