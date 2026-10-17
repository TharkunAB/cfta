import MicroCFTA.SourceCurrentNativePublicationNodeAlignment
import MicroCFTA.SourceCurrentLiteralFilterParts
import MicroCFTA.SourceCurrentNativeCallbackErasure
import MicroCFTA.InternedFilterSelfReference

/-!
# Actual source filtering along the root union spine

The source transformation removes the local variable only at the root
and through root unions. Ordinary children and captured records stay
unchanged. Exact literal atoms and rows account for union regrouping.
-/
namespace MicroCFTA.SourceCurrentPublicationFilterSource
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredShallowCompletion (BinderFree ManyBinderFree)
open SourceCurrentLiteralRootParts (Literal Row SameParts)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open InternedBinderProtocol (Reference)
open Language

/-- Remove the supplied local only along the root union spine. -/
def rootErase (expression : Syntax Symbol Guard) : Syntax Symbol Guard :=
  match expression with
  | .var 0 => .empty
  | .union members => .union (members.map rootErase)
  | other => other
termination_by sizeOf expression

private def RootFresh (expression : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (own : Reference) : Prop :=
  match expression with
  | .var (index + 1) => own ∉ (captures[index]?.getD .empty).free
  | .union members => ∀ child ∈ members, RootFresh child captures own
  | _ => True
termination_by sizeOf expression

private theorem support_fresh (expression : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (own : Reference)
    (fresh : own ∉ InternedFreeNameSemantics.evaluate (.binder true expression)
      (captures.map InternedRootProfile.profile) (captures.map Value.free)) :
    RootFresh expression captures own := by
  cases expression with
  | empty | node | binder => trivial
  | var index =>
      cases index with
      | zero => trivial
      | succ index =>
          simpa [RootFresh, InternedFreeNameSemantics.evaluate, InternedFreeNameSemantics.lower,
            List.getElem?_map, List.map_map, Function.comp_def] using fresh
  | union members =>
      intro child member
      apply support_fresh child captures own
      intro present
      apply fresh
      rw [InternedFreeNameSemantics.evaluate, InternedFreeNameSemantics.lower_member] at present ⊢
      rw [InternedFreeNameSemantics.evaluate]
      exact (InternedFreeNameSemantics.evaluateMany_member _ _ _ _).mpr ⟨child,member,present⟩
termination_by sizeOf expression

private theorem erased_row (own : Reference) (value : Value Symbol Guard) (row : EdgeValue Symbol Guard) :
    Row (eraseSelf own value) row ↔ Row value row := by
  cases value with
  | empty | node | union | mu => rfl
  | reference other =>
      unfold eraseSelf
      split <;> constructor <;> intro impossible <;> cases impossible

private theorem erased_literal (own : Reference) (value atom : Value Symbol Guard)
    (notBare : value ≠ .reference own) : Literal (eraseSelf own value) atom ↔ Literal value atom := by
  have different : value.referenceOf ≠ .ref own := fun same => notBare ((referenceOf_self_iff own value).mp same)
  simp only [eraseSelf,different,↓reduceIte]

/-- Filtering and bare-self erasure remove exactly the selected literal atom. -/
theorem filtered_literal [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (own : Reference) (value : Value Symbol Guard) (available : Available state value)
    (atom : Value Symbol Guard) :
    Literal (eraseSelf own (run (withoutSelfReference own value) state).1) atom ↔
      Literal value atom ∧ atom ≠ .reference own := by
  by_cases bare : value = .reference own
  · subst value
    simp only [withoutSelfReference,run,eraseSelf,Value.referenceOf,↓reduceIte]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨part,different⟩
      cases part
      exact False.elim (different rfl)
  · have notBare : (run (withoutSelfReference own value) state).1 ≠ .reference own :=
      fun same => bare ((InternedFilterSelfReference.filter_self_iff own value state
        normal.facts.coherent normal.flat available).mp same)
    rw [erased_literal own _ atom notBare,
      SourceCurrentLiteralFilterParts.literal state normal own value available atom]
    simp only [bare,false_or]

/-- Filtering and bare-self erasure preserve every exact ordinary row. -/
theorem filtered_row [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (own : Reference) (value : Value Symbol Guard) (available : Available state value)
    (row : EdgeValue Symbol Guard) :
    Row (eraseSelf own (run (withoutSelfReference own value) state).1) row ↔ Row value row := by
  rw [erased_row]
  exact SourceCurrentLiteralFilterParts.row state normal own value available row

private theorem many_free (expressions : List (Syntax Symbol Guard)) (free : ManyBinderFree expressions)
    (child : Syntax Symbol Guard) (member : child ∈ expressions) : BinderFree child := by
  induction expressions with
  | nil => cases member
  | cons expression rest ih =>
      simp only [ManyBinderFree] at free
      rcases List.mem_cons.mp member with rfl | later
      · exact free.1
      · exact ih free.2 later

/-- Root erasure preserves the static absence of source binders. -/
theorem rootErase_binder_free (expression : Syntax Symbol Guard) (free : BinderFree expression) :
    BinderFree (rootErase expression) := by
  cases expression with
  | empty | node => exact free
  | var index => cases index <;> trivial
  | binder => cases free
  | union members =>
      change ManyBinderFree (members.map rootErase)
      have every : ∀ child ∈ members, BinderFree (rootErase child) := by
        intro child member
        exact rootErase_binder_free child (many_free members free child member)
      induction members with
      | nil => trivial
      | cons child rest ih =>
          exact ⟨every child List.mem_cons_self,
            ih (fun item included => every item (List.mem_cons_of_mem _ included))⟩
termination_by sizeOf expression

end MicroCFTA.SourceCurrentPublicationFilterSource
