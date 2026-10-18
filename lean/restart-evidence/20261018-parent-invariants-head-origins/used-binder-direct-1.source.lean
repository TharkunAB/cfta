import MicroCFTA.SourceCurrentLiteralFilterParts
import MicroCFTA.SourceCurrentNativeCallbackErasure
import MicroCFTA.SourceCurrentOpenObservations

/-!
# Root alternatives through actual union construction and self filtering

References use a supplied lexical relation. Mu atoms remain opaque and
match only Mu atoms. Ordinary rows retain full fields and ordered child
relations. Root unions match by occurrences, without an order requirement.
Actual normalization and filtering produce the resulting root relation.
This module does not derive the relation for a retained Mu writer.
-/
namespace MicroCFTA.SourceCurrentUsedBinderRootAlternatives
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentOpenObservations (RowMatch)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open InternedBinderProtocol (Reference)
open Language

/-- References use their lexical relation. Complete Mu atoms use the supplied value relation. -/
def AtomMatch (references : Reference → Reference → Prop)
    (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) : Prop :=
  match first,second with
  | .reference left,.reference right => references left right
  | .mu ..,.mu .. => values first second
  | _,_ => False

/-- Immediate atoms and full ordinary rows match in both directions through root unions. -/
def RootMatch (references : Reference → Reference → Prop)
    (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) : Prop :=
  (∀ atom, Literal first atom → ∃ other, Literal second other ∧ AtomMatch references values atom other) ∧
  (∀ atom, Literal second atom → ∃ other, Literal first other ∧ AtomMatch references values other atom) ∧
  (∀ row, Row first row → ∃ other, Row second other ∧ RowMatch values row other) ∧
  (∀ row, Row second row → ∃ other, Row first other ∧ RowMatch values other row)

private theorem paired_left {α β : Type} {relation : α → β → Prop}
    {first : List α} {second : List β} (paired : All₂ relation first second)
    (value : α) (member : value ∈ first) : ∃ other ∈ second, relation value other := by
  induction paired with
  | nil => cases member
  | cons pair rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_,List.mem_cons_self,pair⟩
      · obtain ⟨other,present,matched⟩ := ih member
        exact ⟨other,List.mem_cons_of_mem _ present,matched⟩

private theorem paired_right {α β : Type} {relation : α → β → Prop}
    {first : List α} {second : List β} (paired : All₂ relation first second)
    (value : β) (member : value ∈ second) : ∃ other ∈ first, relation other value := by
  induction paired with
  | nil => cases member
  | cons pair rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_,List.mem_cons_self,pair⟩
      · obtain ⟨other,present,matched⟩ := ih member
        exact ⟨other,List.mem_cons_of_mem _ present,matched⟩

/-- Initial normal heaps and related inputs derive root matching after both actual union operations. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)]
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : List (Value Symbol Guard)) (before later : State Symbol Guard)
    (firstNormal : Normal before) (secondNormal : Normal later)
    (firstAvailable : Values before first) (secondAvailable : Values later second)
    (paired : All₂ (RootMatch references values) first second) :
    RootMatch references values (run (makeUnion first) before).1 (run (makeUnion second) later).1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro atom part
    obtain ⟨original,member,part⟩ := (SourceCurrentLiteralUnionParts.literal before firstNormal.facts
      first firstAvailable atom).mp part
    obtain ⟨other,present,matched⟩ := paired_left paired original member
    obtain ⟨output,found,matched⟩ := matched.1 atom part
    exact ⟨output,(SourceCurrentLiteralUnionParts.literal later secondNormal.facts second secondAvailable output).mpr
      ⟨other,present,found⟩,matched⟩
  · intro atom part
    obtain ⟨original,member,part⟩ := (SourceCurrentLiteralUnionParts.literal later secondNormal.facts
      second secondAvailable atom).mp part
    obtain ⟨other,present,matched⟩ := paired_right paired original member
    obtain ⟨output,found,matched⟩ := matched.2.1 atom part
    exact ⟨output,(SourceCurrentLiteralUnionParts.literal before firstNormal.facts first firstAvailable output).mpr
      ⟨other,present,found⟩,matched⟩
  · intro row part
    obtain ⟨original,member,part⟩ := (SourceCurrentLiteralUnionParts.row before firstNormal.facts firstNormal.live
      first firstAvailable row).mp part
    obtain ⟨other,present,matched⟩ := paired_left paired original member
    obtain ⟨output,found,matched⟩ := matched.2.2.1 row part
    exact ⟨output,(SourceCurrentLiteralUnionParts.row later secondNormal.facts secondNormal.live second secondAvailable output).mpr
      ⟨other,present,found⟩,matched⟩
  · intro row part
    obtain ⟨original,member,part⟩ := (SourceCurrentLiteralUnionParts.row later secondNormal.facts secondNormal.live
      second secondAvailable row).mp part
    obtain ⟨other,present,matched⟩ := paired_right paired original member
    obtain ⟨output,found,matched⟩ := matched.2.2.2 row part
    exact ⟨output,(SourceCurrentLiteralUnionParts.row before firstNormal.facts firstNormal.live first firstAvailable output).mpr
      ⟨other,present,found⟩,matched⟩

private theorem atom_self (references : Reference → Reference → Prop)
    (values : Value Symbol Guard → Value Symbol Guard → Prop) (own other : Reference)
    (compatible : ∀ first second, references first second → (first = own ↔ second = other))
    (first second : Value Symbol Guard) (matched : AtomMatch references values first second) :
    first = .reference own ↔ second = .reference other := by
  cases first <;> cases second <;> simp_all only [AtomMatch,Value.reference.injEq,
    Value.noConfusion,not_false_eq_true]

private theorem erase_literal (name : Reference) (value atom : Value Symbol Guard) :
    Literal (eraseSelf name value) atom ↔ Literal value atom ∧ atom ≠ .reference name := by
  unfold eraseSelf
  split
  · rename_i same
    have shape := (referenceOf_self_iff name value).mp same
    subst value
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨part,different⟩
      cases part
      exact False.elim (different rfl)
  · rename_i different
    constructor
    · intro part
      refine ⟨part,?_⟩
      intro same
      subst atom
      have shape : value = .reference name := by
        cases value <;> cases part
        rfl
      exact different (by rw [shape]; rfl)
    · exact And.left

private theorem erase_row (name : Reference) (value : Value Symbol Guard) (row : EdgeValue Symbol Guard) :
    Row (eraseSelf name value) row ↔ Row value row := by
  unfold eraseSelf
  split
  · rename_i same
    have shape := (referenceOf_self_iff name value).mp same
    subst value
    constructor <;> intro impossible <;> cases impossible
  · exact Iff.rfl

private theorem erased_filter_literal [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (normal : Normal state) (name : Reference)
    (value : Value Symbol Guard) (available : Available state value) (atom : Value Symbol Guard) :
    Literal (eraseSelf name (run (withoutSelfReference name value) state).1) atom ↔
      Literal value atom ∧ atom ≠ .reference name := by
  rw [erase_literal,SourceCurrentLiteralFilterParts.literal state normal name value available atom]
  constructor
  · exact fun actual => ⟨actual.1.1,actual.2⟩
  · exact fun actual => ⟨⟨actual.1,Or.inr actual.2⟩,actual.2⟩

private theorem erased_filter_row [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (normal : Normal state) (name : Reference)
    (value : Value Symbol Guard) (available : Available state value) (row : EdgeValue Symbol Guard) :
    Row (eraseSelf name (run (withoutSelfReference name value) state).1) row ↔ Row value row := by
  rw [erase_row,SourceCurrentLiteralFilterParts.row state normal name value available row]

/-- Actual root filtering followed by bare-self erasure preserves paired lexical root alternatives. -/
theorem erased_filter [DecidableEq (EdgeKey Symbol Guard)]
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (own other : Reference) (first second : Value Symbol Guard) (before later : State Symbol Guard)
    (firstNormal : Normal before) (secondNormal : Normal later)
    (firstAvailable : Available before first) (secondAvailable : Available later second)
    (matched : RootMatch references values first second)
    (compatible : ∀ left right, references left right → (left = own ↔ right = other)) :
    RootMatch references values (eraseSelf own (run (withoutSelfReference own first) before).1)
      (eraseSelf other (run (withoutSelfReference other second) later).1) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro atom part
    obtain ⟨part,different⟩ := (erased_filter_literal before firstNormal own first firstAvailable atom).mp part
    obtain ⟨output,found,pair⟩ := matched.1 atom part
    exact ⟨output,(erased_filter_literal later secondNormal other second secondAvailable output).mpr
      ⟨found,fun same => different ((atom_self references values own other compatible atom output pair).mpr same)⟩,pair⟩
  · intro atom part
    obtain ⟨part,different⟩ := (erased_filter_literal later secondNormal other second secondAvailable atom).mp part
    obtain ⟨output,found,pair⟩ := matched.2.1 atom part
    exact ⟨output,(erased_filter_literal before firstNormal own first firstAvailable output).mpr
      ⟨found,fun same => different ((atom_self references values own other compatible output atom pair).mp same)⟩,pair⟩
  · intro row part
    obtain ⟨output,found,pair⟩ := matched.2.2.1 row
      ((erased_filter_row before firstNormal own first firstAvailable row).mp part)
    exact ⟨output,(erased_filter_row later secondNormal other second secondAvailable output).mpr found,pair⟩
  · intro row part
    obtain ⟨output,found,pair⟩ := matched.2.2.2 row
      ((erased_filter_row later secondNormal other second secondAvailable row).mp part)
    exact ⟨output,(erased_filter_row before firstNormal own first firstAvailable output).mpr found,pair⟩

/-- Actual filtering preserves root alternatives when the two bare-self cases agree. -/
theorem filter [DecidableEq (EdgeKey Symbol Guard)]
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (own other : Reference) (first second : Value Symbol Guard) (before later : State Symbol Guard)
    (firstNormal : Normal before) (secondNormal : Normal later)
    (firstAvailable : Available before first) (secondAvailable : Available later second)
    (matched : RootMatch references values first second)
    (compatible : ∀ left right, references left right → (left = own ↔ right = other))
    (bare : first = .reference own ↔ second = .reference other) :
    RootMatch references values (run (withoutSelfReference own first) before).1
      (run (withoutSelfReference other second) later).1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro atom part
    obtain ⟨part,kept⟩ := (SourceCurrentLiteralFilterParts.literal before firstNormal own first firstAvailable atom).mp part
    obtain ⟨output,found,pair⟩ := matched.1 atom part
    refine ⟨output,(SourceCurrentLiteralFilterParts.literal later secondNormal other second secondAvailable output).mpr
      ⟨found,?_⟩,pair⟩
    exact kept.elim (fun same => Or.inl (bare.mp same))
      (fun different => Or.inr (fun same => different ((atom_self references values own other compatible atom output pair).mpr same)))
  · intro atom part
    obtain ⟨part,kept⟩ := (SourceCurrentLiteralFilterParts.literal later secondNormal other second secondAvailable atom).mp part
    obtain ⟨output,found,pair⟩ := matched.2.1 atom part
    refine ⟨output,(SourceCurrentLiteralFilterParts.literal before firstNormal own first firstAvailable output).mpr
      ⟨found,?_⟩,pair⟩
    exact kept.elim (fun same => Or.inl (bare.mpr same))
      (fun different => Or.inr (fun same => different ((atom_self references values own other compatible output atom pair).mp same)))
  · intro row part
    obtain ⟨output,found,pair⟩ := matched.2.2.1 row
      ((SourceCurrentLiteralFilterParts.row before firstNormal own first firstAvailable row).mp part)
    exact ⟨output,(SourceCurrentLiteralFilterParts.row later secondNormal other second secondAvailable output).mpr found,pair⟩
  · intro row part
    obtain ⟨output,found,pair⟩ := matched.2.2.2 row
      ((SourceCurrentLiteralFilterParts.row later secondNormal other second secondAvailable row).mp part)
    exact ⟨output,(SourceCurrentLiteralFilterParts.row before firstNormal own first firstAvailable output).mpr found,pair⟩

end MicroCFTA.SourceCurrentUsedBinderRootAlternatives
