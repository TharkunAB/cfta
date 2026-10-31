import MicroCFTA.SourceEqualityRequiredWorkerEffects
import MicroCFTA.SourceEqualityRequiredExecution

set_option autoImplicit false
/- Physical effects of the actual compiled child-list worker. -/
namespace MicroCFTA.SourceEqualityProjectionWorkerPhysical
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceEqualityRequiredWorker (Result)
open SourceEqualityNeeded (Needed Path build)
open scoped Classical
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard A B : Type}

private def ValuePost (Guard : Type) (value : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  Available after value ∧ value.free = []
private def ValuesPost (Guard : Type) (values : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  Values after values ∧ ClosedValues values
private structure Verified (before : State Symbol Guard) (actual : Result Symbol Guard A)
    (post : A → State Symbol Guard → Prop) : Prop where
  semantic : SemanticHeap (reached actual)
  covered : Covered [] (reached actual)
  growth : Grows before (reached actual)
  history : Extends before.nodes.issued (reached actual).nodes.issued
  finished : ∀ value after, actual = .done value after → post value after

private theorem Verified.extend {before middle : State Symbol Guard} {actual : Result Symbol Guard A}
    {post : A → State Symbol Guard → Prop} (v : Verified middle actual post)
    (g : Grows before middle) (h : Extends before.nodes.issued middle.nodes.issued) : Verified before actual post :=
  ⟨v.semantic, v.covered, grows_trans g v.growth, extends_trans h v.history, v.finished⟩
private theorem pure_verified (before : State Symbol Guard) (sem : SemanticHeap before) (cov : Covered [] before)
    (value : A) {post : A → State Symbol Guard → Prop} (valid : post value before) : Verified before (.done value before) post :=
  ⟨sem, cov, grows_refl _, extends_refl _, by intro _ _ same; cases same; exact valid⟩
private theorem bind_verified {before : State Symbol Guard} {actual : Result Symbol Guard A}
    {post : A → State Symbol Guard → Prop} {next : A → State Symbol Guard → Result Symbol Guard B}
    {final : B → State Symbol Guard → Prop} (v : Verified before actual post)
    (later : ∀ value after, Verified before (.done value after) post → Verified after (next value after) final) :
    Verified before (actual.bind next) final := by
  cases actual with
  | done value after => exact (later value after v).extend v.growth v.history
  | pending key after | unresolved name after | exhausted limit after =>
      exact ⟨v.semantic, v.covered, v.growth, v.history, by intro _ _ same; cases same⟩

private theorem required (fuel readFuel : Nat) (needed : Needed) (query : Value Symbol Guard)
    (before : State Symbol Guard) (sem : SemanticHeap before) (cov : Covered [] before)
    (available : Available before query) (closed : query.free = []) :
    Verified before (SourceEqualityRequiredWorker.require fuel readFuel needed query before) (ValuePost Guard) := by
  have actual := require_effects fuel readFuel needed query before sem cov available closed
  refine ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.1, ?_⟩
  intro value after same
  simpa only [same, ValuePost] using actual.2.2.2.2
private theorem cons_values (value : Value Symbol Guard) (before : State Symbol Guard)
    (one : ValuePost Guard value before) {actual : Result Symbol Guard (List (Value Symbol Guard))}
    (tail : Verified before actual (ValuesPost Guard)) :
    Verified before (actual.bind fun values after => .done (value :: values) after) (ValuesPost Guard) := by
  apply bind_verified tail
  intro values after part
  refine pure_verified after part.semantic part.covered (value :: values) ⟨?_, ?_⟩
  · intro child member
    rcases List.mem_cons.mp member with same | member
    · subst child; exact one.1.grows before after part.growth part.history
    · exact (part.finished _ _ rfl).1 child member
  · intro child member
    rcases List.mem_cons.mp member with same | member
    · subst child; exact one.2
    · exact (part.finished _ _ rfl).2 child member

private theorem children_verified (fuel readFuel : Nat) (entries : List (Int × Needed)) (index : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (sem : SemanticHeap before) (cov : Covered [] before) (available : Values before values) (closed : ClosedValues values) :
    Verified before (SourceEqualityRequiredWorker.children (SourceEqualityRequiredWorker.require fuel readFuel)
      entries index values before) (ValuesPost Guard) := by
  induction values generalizing index before with
  | nil => exact pure_verified before sem cov [] ⟨by simp [Values], by simp [ClosedValues]⟩
  | cons value values ih =>
      have tailAvailable := fun child member => available child (List.mem_cons_of_mem _ member)
      have tailClosed := fun child member => closed child (List.mem_cons_of_mem _ member)
      cases selected : SourceEqualityNeededMap.lookup (index : Int) entries with
      | none =>
          simpa only [SourceEqualityRequiredWorker.children, selected] using
          cons_values value before ⟨available value List.mem_cons_self, closed value List.mem_cons_self⟩
            (ih (index + 1) before sem cov tailAvailable tailClosed)
      | some needed =>
          rw [SourceEqualityRequiredWorker.children, selected]
          apply bind_verified (required fuel readFuel needed value before sem cov
            (available value List.mem_cons_self) (closed value List.mem_cons_self))
          intro result middle first
          exact cons_values result middle (first.finished _ _ rfl)
            (ih (index + 1) middle first.semantic first.covered
              (fun child member => (tailAvailable child member).grows before middle first.growth first.history) tailClosed)

private theorem Verified.list_conclusion {before : State Symbol Guard}
    {actual : Result Symbol Guard (List (Value Symbol Guard))} (v : Verified before actual (ValuesPost Guard)) :
    SemanticHeap (reached actual) ∧ Covered [] (reached actual) ∧ Grows before (reached actual) ∧
      Extends before.nodes.issued (reached actual).nodes.issued ∧
      match (generalizing := false) actual with
      | .done values after => Values after values ∧ ClosedValues values
      | .pending _ _ | .unresolved _ _ | .exhausted _ _ => True := by
  refine ⟨v.semantic, v.covered, v.growth, v.history, ?_⟩
  match (generalizing := false) h : actual with
  | .done values after => exact v.finished _ _ h
  | .pending .. | .unresolved .. | .exhausted .. => trivial

/-- The actual compiled child-list entry retains all reached physical heap resources. -/
theorem requireAll_effects (fuel readFuel : Nat) (paths : List Path)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Values before values) (closed : ClosedValues values) :
    let actual := SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before
    let after := reached actual
    SemanticHeap after ∧ Covered [] after ∧ Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧
      match actual with
      | .done results returned => Values returned results ∧ ClosedValues results
      | .pending _ _ | .unresolved _ _ | .exhausted _ _ => True := by
  apply Verified.list_conclusion
  cases compiled : build paths with
  | node entries => simpa only [SourceEqualityRequiredExecution.requireAll, compiled] using
      children_verified fuel readFuel entries 0 values before semantic covered available closed

end MicroCFTA.SourceEqualityProjectionWorkerPhysical
