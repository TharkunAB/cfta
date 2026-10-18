import MicroCFTA.SourceCurrentStoredLiteralExecutionParts
import MicroCFTA.SourceCurrentUsedBinderRootAlternatives
import MicroCFTA.SourceCurrentReaderFiniteOrdinaryStep

/-!
# Finite reconstruction from literal root matches

The observation reader and execution heap are separate. Actual warm atom
calls use the full observation depth. Ordered row-child calls use one less
depth. Mu atoms retain an explicit reconstruction induction hypothesis.
This module does not prove the general binder case or reader transport.
-/
namespace MicroCFTA.SourceCurrentFiniteRootReconstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredMuOrigins (Normal)
open InternedUnionNormalForm (Atomic)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentOpenObservations (Same ReferenceOrigin RowMatch)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentUsedBinderRootAlternatives (RootMatch AtomMatch)
open SourceCurrentStoredNodeExpansion (RowCalls)
open SourceCurrentStoredLiteralExecutionParts (LiteralOutput RowOutput)
open MergedFreshOrdinaryGraph (Origin)
open Language

/-- Actual warm calls retain finite observations at a separate fixed reader. -/
def Executions [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view common : State Symbol Guard)
    (first second : Environment Symbol Guard) (rawFirst rawSecond : Value Symbol Guard) : Prop :=
  ∀ left right, execute rawFirst first common = .done left common →
    execute rawSecond second common = .done right common → RelatedAt depth view left right

private theorem no_reference [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (name : InternedBinderProtocol.Reference) :
    ¬ ReferenceOrigin view [] name := by
  intro present
  obtain ⟨_,member,_⟩ := (SourceCurrentOpenObservations.reference_seeds view [] name).mp present
  cases member

private theorem atomic_reference [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (value : Value Symbol Guard) (atomic : Atomic value)
    (name : InternedBinderProtocol.Reference) :
    ReferenceOrigin view [value] name ↔ ∃ atom, Literal value atom ∧ ReferenceOrigin view [atom] name := by
  cases value with
  | empty =>
      have none := SourceCurrentOpenObservations.reference_expand view
        (.empty : Value Symbol Guard) (by intro name impossible; cases impossible) name
      exact iff_of_false (fun found => no_reference view name (none.mp found))
        (by rintro ⟨atom,part,_⟩; cases part)
  | node entry rows level free =>
      have none := SourceCurrentOpenObservations.reference_expand view
        (.node entry rows level free) (by intro name impossible; cases impossible) name
      exact iff_of_false (fun found => no_reference view name (none.mp found))
        (by rintro ⟨atom,part,_⟩; cases part)
  | reference own =>
      constructor
      · intro actual; exact ⟨_,.reference own,actual⟩
      · rintro ⟨atom,part,actual⟩; cases part; exact actual
  | mu entry body depth ordinary =>
      constructor
      · intro actual; exact ⟨_,.mu entry body depth ordinary,actual⟩
      · rintro ⟨atom,part,actual⟩; cases part; exact actual
  | union => cases atomic

private theorem atomic_row [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (value : Value Symbol Guard) (atomic : Atomic value)
    (row : EdgeValue Symbol Guard) :
    Origin view [value] row ↔ Row value row ∨ ∃ atom, Literal value atom ∧ Origin view [atom] row := by
  cases value with
  | empty =>
      exact iff_of_false (MergedFreshOrdinaryGraph.origin_empty view row)
        (by rintro (part | ⟨atom,part,_⟩) <;> cases part)
  | node entry rows level free =>
      constructor
      · intro actual
        exact Or.inl (.node ((MergedFreshOrdinaryGraph.origin_node view entry rows level free row).mp actual))
      · rintro (part | ⟨atom,part,_⟩)
        · cases part with
          | node member => exact (MergedFreshOrdinaryGraph.origin_node view entry rows level free row).mpr member
        · cases part
  | reference own =>
      constructor
      · intro actual; exact Or.inr ⟨_,.reference own,actual⟩
      · rintro (part | ⟨atom,part,actual⟩)
        · cases part
        · cases part; exact actual
  | mu entry body depth ordinary =>
      constructor
      · intro actual; exact Or.inr ⟨_,.mu entry body depth ordinary,actual⟩
      · rintro (part | ⟨atom,part,actual⟩)
        · cases part
        · cases part; exact actual
  | union => cases atomic

private theorem references [DecidableEq (EdgeKey Symbol Guard)]
    (common view : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value)
    (name : InternedBinderProtocol.Reference) :
    ReferenceOrigin view [value] name ↔ ∃ atom, Literal value atom ∧ ReferenceOrigin view [atom] name := by
  cases value with
  | empty | reference | node | mu => apply atomic_reference; trivial
  | union entry members level free =>
      have flat := InternedUnionNormalForm.resident_flat common normal.flat _ available.resident
      have expand := SourceCurrentOpenObservations.reference_expand view (.union entry members level free)
        (by intro name impossible; cases impossible) name
      rw [expand,SourceCurrentOpenObservations.reference_seeds]
      constructor
      · rintro ⟨member,present,actual⟩
        obtain ⟨atom,part,found⟩ := (atomic_reference view member (flat member present) name).mp actual
        exact ⟨atom,.union present part,found⟩
      · rintro ⟨atom,part,actual⟩
        obtain ⟨member,present,inside⟩ := (SourceCurrentLiteralRootParts.literal_union entry members level free atom).mp part
        exact ⟨member,present,(atomic_reference view member (flat member present) name).mpr ⟨atom,inside,actual⟩⟩

private theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    (common view : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value) (row : EdgeValue Symbol Guard) :
    Origin view [value] row ↔ Row value row ∨ ∃ atom, Literal value atom ∧ Origin view [atom] row := by
  cases value with
  | empty | reference | node | mu => apply atomic_row; trivial
  | union entry members level free =>
      have flat := InternedUnionNormalForm.resident_flat common normal.flat _ available.resident
      rw [MergedFreshOrdinaryGraph.origin_union]
      constructor
      · rintro ⟨member,present,actual⟩
        rcases (atomic_row view member (flat member present) row).mp actual with part | ⟨atom,part,found⟩
        · exact Or.inl (.union present part)
        · exact Or.inr ⟨atom,.union present part,found⟩
      · rintro (part | ⟨atom,part,actual⟩)
        · obtain ⟨member,present,inside⟩ := (SourceCurrentLiteralRootParts.row_union entry members level free row).mp part
          exact ⟨member,present,(atomic_row view member (flat member present) row).mpr (Or.inl inside)⟩
        · obtain ⟨member,present,inside⟩ := (SourceCurrentLiteralRootParts.literal_union entry members level free atom).mp part
          exact ⟨member,present,(atomic_row view member (flat member present) row).mpr (Or.inr ⟨atom,inside,actual⟩)⟩

private theorem atomic_nonempty (common : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value) (atomic : Atomic value)
    (nonempty : value.referenceOf ≠ .empty) :
    (∃ atom, Literal value atom) ∨ ∃ row, Row value row := by
  cases value with
  | empty => exact False.elim (nonempty rfl)
  | reference name => exact Or.inl ⟨_,.reference name⟩
  | mu entry body depth ordinary => exact Or.inl ⟨_,.mu entry body depth ordinary⟩
  | union => cases atomic
  | node entry rows level free =>
      have proper := InternedNonemptyRecords.resident_nonempty common normal.proper _ available.resident
      obtain ⟨row,member⟩ := List.exists_mem_of_ne_nil rows proper
      exact Or.inr ⟨row,.node member⟩

private theorem no_parts_empty (common : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value)
    (noAtoms : ∀ atom, ¬ Literal value atom) (noRows : ∀ row, ¬ Row value row) :
    value.referenceOf = .empty := by
  by_cases nonempty : value.referenceOf = .empty
  · exact nonempty
  apply False.elim
  cases value with
  | empty | reference | node | mu =>
      rcases atomic_nonempty common normal _ available trivial nonempty with ⟨atom,part⟩ | ⟨row,part⟩
      · exact noAtoms atom part
      · exact noRows row part
  | union entry members level free =>
      have proper := InternedNonemptyRecords.resident_nonempty common normal.proper _ available.resident
      have bound : 2 ≤ members.length := proper.1
      have hasMember : members ≠ [] := by intro same; simp only [same,List.length_nil] at bound; omega
      obtain ⟨member,present⟩ := List.exists_mem_of_ne_nil members hasMember
      have flat := InternedUnionNormalForm.resident_flat common normal.flat _ available.resident
      have live := InternedUnionNonemptyMembers.resident_membersNonempty common normal.members _ available.resident
      rcases atomic_nonempty common normal member (available.children member present) (flat member present)
        (live member present) with ⟨atom,part⟩ | ⟨row,part⟩
      · exact noAtoms atom (.union present part)
      · exact noRows row (.union present part)

private theorem literal_available (common : State Symbol Guard) {raw atom : Value Symbol Guard}
    (available : Available common raw) (part : Literal raw atom) : Available common atom := by
  induction part with
  | reference | mu => exact available
  | union member _ ih => exact ih (available.children _ member)

private theorem call_available [DecidableEq (EdgeKey Symbol Guard)] (common : State Symbol Guard)
    (ready : Ready common) (raw output : Value Symbol Guard) (environment : Environment Symbol Guard)
    (available : Available common raw) (replacements : Replacements common environment)
    (actual : execute raw environment common = .done output common) : Available common output := by
  obtain ⟨value,after,done,_,found,_⟩ := SourceCurrentStoredReconstruction.execute raw environment common ready available replacements
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (done.symm.trans actual)
  exact found

private theorem nonempty_parts (common : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value) (nonempty : value.referenceOf ≠ .empty) :
    (∃ atom, Literal value atom) ∨ ∃ row, Row value row := by
  classical
  by_contra absent
  exact nonempty (no_parts_empty common normal value available
    (fun atom part => absent (Or.inl ⟨atom,part⟩)) (fun row part => absent (Or.inr ⟨row,part⟩)))

private theorem part_nonempty {value : Value Symbol Guard}
    (part : (∃ atom, Literal value atom) ∨ ∃ row, Row value row) : value.referenceOf ≠ .empty := by
  intro empty
  have shape := InternedEmptyNormalization.reference_empty value |>.mp empty
  subst value
  rcases part with ⟨atom,part⟩ | ⟨row,part⟩ <;> cases part

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem atom_embed (common view : State Symbol Guard) (ready : Ready common)
    (raw result source output : Value Symbol Guard) (environment : Environment Symbol Guard)
    (rawAvailable : Available common raw) (replacements : Replacements common environment)
    (actual : execute raw environment common = .done result common)
    (part : Literal raw source) (called : execute source environment common = .done output common) :
    (output.referenceOf ≠ .empty → result.referenceOf ≠ .empty) ∧
    (∀ name, ReferenceOrigin view [output] name → ReferenceOrigin view [result] name) ∧
    ∀ row, Origin view [output] row → Origin view [result] row := by
  have normal := ready.semantic.1.normal
  have outputAvailable := call_available common ready source output environment
    (literal_available common rawAvailable part) replacements called
  have resultAvailable := call_available common ready raw result environment rawAvailable replacements actual
  have parts := SourceCurrentStoredLiteralExecutionParts.parts raw result environment common ready rawAvailable replacements actual
  have literals (atom : Value Symbol Guard) (found : Literal output atom) : Literal result atom :=
    (parts.1 atom).mpr ⟨source,part,output,called,found⟩
  have physical (row : EdgeValue Symbol Guard) (found : Row output row) : Row result row :=
    (parts.2 row).mpr (Or.inl ⟨source,part,output,called,found⟩)
  refine ⟨?_,?_,?_⟩
  · intro nonempty
    rcases nonempty_parts common normal output outputAvailable nonempty with ⟨atom,found⟩ | ⟨row,found⟩
    · exact part_nonempty (Or.inl ⟨atom,literals atom found⟩)
    · exact part_nonempty (Or.inr ⟨row,physical row found⟩)
  · intro name found
    obtain ⟨atom,inside,origin⟩ := (references common view normal output outputAvailable name).mp found
    exact (references common view normal result resultAvailable name).mpr ⟨atom,literals atom inside,origin⟩
  · intro row found
    rcases (rows common view normal output outputAvailable row).mp found with inside | ⟨atom,inside,origin⟩
    · exact (rows common view normal result resultAvailable row).mpr (Or.inl (physical row inside))
    · exact (rows common view normal result resultAvailable row).mpr (Or.inr ⟨atom,literals atom inside,origin⟩)

private theorem paired_outputs (depth : Nat) (view common : State Symbol Guard)
    (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Environment Symbol Guard)
    (children : ∀ a b, values a b → Executions depth view common first second a b)
    {left right : List (Value Symbol Guard)} (paired : All₂ values left right)
    {outputs others : List (Value Symbol Guard)}
    (called : All₂ (fun original output => execute original first common = .done output common) left outputs)
    (returned : All₂ (fun original output => execute original second common = .done output common) right others) :
    All₂ (RelatedAt depth view) outputs others := by
  induction paired generalizing outputs others with
  | nil => cases called; cases returned; exact .nil
  | cons pair tail ih =>
      cases called with
      | cons head rest =>
          cases returned with
          | cons other remaining => exact .cons (children _ _ pair _ _ head other) (ih rest remaining)

private theorem children_empty (depth : Nat) (view : State Symbol Guard)
    {first second : List (Value Symbol Guard)} (paired : All₂ (RelatedAt depth view) first second) :
    first.any (fun child => child.referenceOf == .empty) = second.any (fun child => child.referenceOf == .empty) := by
  induction paired with
  | nil => rfl
  | @cons first second rest remaining pair tail ih =>
      have head : (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
        by_cases empty : first.referenceOf = .empty
        · simp only [empty,pair.1.mp empty,beq_self_eq_true]
        · have other : second.referenceOf ≠ .empty := fun found => empty (pair.1.mpr found)
          simp only [beq_eq_false_iff_ne.mpr empty,beq_eq_false_iff_ne.mpr other]
      simp only [List.any_cons,head,ih]

private theorem rows_related (depth : Nat) (view common : State Symbol Guard) (ready : Ready common)
    (values : Value Symbol Guard → Value Symbol Guard → Prop) (first second : Environment Symbol Guard)
    (children : ∀ a b, values a b → Executions depth view common first second a b)
    {original other output rebuilt : EdgeValue Symbol Guard} (matched : RowMatch values original other)
    (called : RowCalls first common original output) (returned : RowCalls second common other rebuilt) :
    RowMatch (RelatedAt depth view) output rebuilt := by
  have valid := ready.semantic.1.normal.facts.coherent.valid
  exact ⟨called.2.2.1.trans (matched.1.trans returned.2.2.1.symm),
    called.2.2.2.1.trans (matched.2.1.trans returned.2.2.2.1.symm),
    paired_outputs depth view common values first second children matched.2.2
      (SourceCurrentStoredCallsReplay.replay called.1 common valid (grows_refl _))
      (SourceCurrentStoredCallsReplay.replay returned.1 common valid (grows_refl _))⟩

private theorem one_way (depth : Nat) (view common : State Symbol Guard)
    (values : Value Symbol Guard → Value Symbol Guard → Prop) (first second : Environment Symbol Guard)
    (raw other result rebuilt : Value Symbol Guard) (ready : Ready common)
    (available : Available common raw) (otherAvailable : Available common other)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (actual : execute raw first common = .done result common)
    (returned : execute other second common = .done rebuilt common)
    (atoms : ∀ source, Literal raw source → ∃ target, Literal other target ∧
      Executions (depth+1) view common first second source target)
    (matchedRows : ∀ row, Row raw row → ∃ target, Row other target ∧ RowMatch values row target)
    (children : ∀ a b, values a b → Executions depth view common first second a b) :
    (result.referenceOf ≠ .empty → rebuilt.referenceOf ≠ .empty) ∧
    (∀ name, ReferenceOrigin view [result] name → ReferenceOrigin view [rebuilt] name) ∧
    ∀ row, Origin view [result] row → ∃ target, Origin view [rebuilt] target ∧
      RowMatch (fun a b => Same depth view [a] [b]) row target := by
  have normal := ready.semantic.1.normal
  have resultAvailable := call_available common ready raw result first available firstReplacements actual
  have rebuiltAvailable := call_available common ready other rebuilt second otherAvailable secondReplacements returned
  have parts := SourceCurrentStoredLiteralExecutionParts.parts raw result first common ready available firstReplacements actual
  have otherParts := SourceCurrentStoredLiteralExecutionParts.parts other rebuilt second common ready otherAvailable secondReplacements returned
  have atomMatch (source output : Value Symbol Guard) (part : Literal raw source)
      (called : execute source first common = .done output common) :
      ∃ target newOutput, Literal other target ∧ execute target second common = .done newOutput common ∧
        RelatedAt (depth+1) view output newOutput := by
    obtain ⟨target,found,related⟩ := atoms source part
    obtain ⟨newOutput,done⟩ := SourceCurrentStoredLiteralExecutionParts.atom other rebuilt second common ready
      otherAvailable secondReplacements returned target found
    exact ⟨target,newOutput,found,done,related output newOutput called done⟩
  have rowMatch (source output : EdgeValue Symbol Guard) (part : Row raw source)
      (called : RowCalls first common source output)
      (live : (!(output.children.any (fun child => child.referenceOf == .empty))) = true) :
      ∃ target, Row rebuilt target ∧ RowMatch (RelatedAt depth view) output target := by
    obtain ⟨original,found,matched⟩ := matchedRows source part
    obtain ⟨target,done⟩ := SourceCurrentStoredLiteralExecutionParts.row other rebuilt second common ready
      otherAvailable secondReplacements returned original found
    have related := rows_related depth view common ready values first second children matched called done
    have otherLive : (!(target.children.any (fun child => child.referenceOf == .empty))) = true := by
      rw [← children_empty depth view related.2.2]
      exact live
    exact ⟨target,(otherParts.2 target).mpr (Or.inr ⟨original,found,done,otherLive⟩),related⟩
  have physical (row : EdgeValue Symbol Guard) (part : Row result row) :
      ∃ target, Origin view [rebuilt] target ∧ RowMatch (fun a b => Same depth view [a] [b]) row target := by
    rcases (parts.2 row).mp part with ⟨source,found,output,called,inside⟩ | ⟨source,found,called,live⟩
    · obtain ⟨target,newOutput,targetPart,done,related⟩ := atomMatch source output found called
      have origin := (rows common view normal output
        (call_available common ready source output first (literal_available common available found) firstReplacements called) row).mpr (Or.inl inside)
      obtain ⟨newRow,newOrigin,matched⟩ := related.2.2.1 row origin
      exact ⟨newRow,(atom_embed common view ready other rebuilt target newOutput second otherAvailable
        secondReplacements returned targetPart done).2.2 newRow newOrigin,matched⟩
    · obtain ⟨target,found,matched⟩ := rowMatch source row found called live
      exact ⟨target,(rows common view normal rebuilt rebuiltAvailable target).mpr (Or.inl found),
        matched.1,matched.2.1,All₂.imp (fun _ _ pair => pair.2) matched.2.2⟩
  refine ⟨?_,?_,?_⟩
  · intro nonempty
    rcases nonempty_parts common normal result resultAvailable nonempty with ⟨atom,part⟩ | ⟨row,part⟩
    · obtain ⟨source,found,output,called,inside⟩ := (parts.1 atom).mp part
      obtain ⟨target,newOutput,targetPart,done,related⟩ := atomMatch source output found called
      exact (atom_embed common view ready other rebuilt target newOutput second otherAvailable secondReplacements returned targetPart done).1
        (fun empty => part_nonempty (Or.inl ⟨atom,inside⟩) (related.1.mpr empty))
    · rcases (parts.2 row).mp part with ⟨source,found,output,called,inside⟩ | ⟨source,found,called,live⟩
      · obtain ⟨target,newOutput,targetPart,done,related⟩ := atomMatch source output found called
        exact (atom_embed common view ready other rebuilt target newOutput second otherAvailable secondReplacements returned targetPart done).1
          (fun empty => part_nonempty (Or.inr ⟨row,inside⟩) (related.1.mpr empty))
      · obtain ⟨target,found,_⟩ := rowMatch source row found called live
        exact part_nonempty (Or.inr ⟨target,found⟩)
  · intro name origin
    obtain ⟨atom,part,inside⟩ := (references common view normal result resultAvailable name).mp origin
    obtain ⟨source,found,output,called,literal⟩ := (parts.1 atom).mp part
    obtain ⟨target,newOutput,targetPart,done,related⟩ := atomMatch source output found called
    have oldOrigin := (references common view normal output
      (call_available common ready source output first (literal_available common available found) firstReplacements called) name).mpr
      ⟨atom,literal,inside⟩
    exact (atom_embed common view ready other rebuilt target newOutput second otherAvailable secondReplacements returned targetPart done).2.1 name
      ((related.2.1 name).mp oldOrigin)
  · intro row origin
    rcases (rows common view normal result resultAvailable row).mp origin with part | ⟨atom,part,inside⟩
    · exact physical row part
    · obtain ⟨source,found,output,called,literal⟩ := (parts.1 atom).mp part
      obtain ⟨target,newOutput,targetPart,done,related⟩ := atomMatch source output found called
      have oldOrigin := (rows common view normal output
        (call_available common ready source output first (literal_available common available found) firstReplacements called) row).mpr
        (Or.inr ⟨atom,literal,inside⟩)
      obtain ⟨newRow,newOrigin,matched⟩ := related.2.2.1 row oldOrigin
      exact ⟨newRow,(atom_embed common view ready other rebuilt target newOutput second otherAvailable secondReplacements returned targetPart done).2.2
        newRow newOrigin,matched⟩
private theorem reference_execute (name : Reference) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) :
    execute (.reference name) environment common = .done ((environment name).getD (.reference name)) common := by
  simp [execute,InternedStoredSubstitution.leaves,Value.free,InternedStoredSubstitution.encode,
    InternedStoredSubstitution.slot,InternedFreshOrdinaryConstruction.build,InternedStoredSubstitution.input]

private theorem flip_pairs {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) : All₂ (fun b a => relation a b) second first := by
  induction paired with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

/-- Literal atom and strict row-child execution hypotheses lift actual warm parent calls at one reader. -/
theorem reconstruct (depth : Nat) (view common : State Symbol Guard)
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Environment Symbol Guard) (rawFirst rawSecond : Value Symbol Guard)
    (ready : Ready common) (firstAvailable : Available common rawFirst) (secondAvailable : Available common rawSecond)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (matched : RootMatch references values rawFirst rawSecond)
    (resolved : ∀ a b, references a b → RelatedAt (depth+1) view
      ((first a).getD (.reference a)) ((second b).getD (.reference b)))
    (atoms : ∀ a b, Literal rawFirst a → Literal rawSecond b →
      AtomMatch (fun _ _ => False) values a b → Executions (depth+1) view common first second a b)
    (children : ∀ a b, values a b → Executions depth view common first second a b) :
    Executions (depth+1) view common first second rawFirst rawSecond := by
  classical
  have atomCalls (a b : Value Symbol Guard) (firstPart : Literal rawFirst a) (secondPart : Literal rawSecond b)
      (paired : AtomMatch references values a b) : Executions (depth+1) view common first second a b := by
    cases a <;> cases b
    all_goals try {cases paired}
    case reference.reference a b =>
      intro left right called returned
      rw [reference_execute] at called returned
      obtain ⟨rfl,_⟩ := Outcome.done.inj called
      obtain ⟨rfl,_⟩ := Outcome.done.inj returned
      exact resolved a b paired
    case mu.mu => exact atoms _ _ firstPart secondPart paired
  intro result rebuilt actual returned
  have forward := one_way depth view common values first second rawFirst rawSecond result rebuilt ready
    firstAvailable secondAvailable firstReplacements secondReplacements actual returned
    (fun source part => by
      obtain ⟨target,found,pair⟩ := matched.1 source part
      exact ⟨target,found,atomCalls source target part found pair⟩) matched.2.2.1 children
  have backward := one_way depth view common (fun b a => values a b) second first rawSecond rawFirst rebuilt result ready
    secondAvailable firstAvailable secondReplacements firstReplacements returned actual
    (fun target part => by
      obtain ⟨source,found,pair⟩ := matched.2.1 target part
      refine ⟨source,found,?_⟩
      intro right left done called
      have related := atomCalls source target found part pair left right called done
      exact ⟨related.1.symm,related.2.symm⟩)
    (fun row part => by
      obtain ⟨other,found,pair⟩ := matched.2.2.2 row part
      exact ⟨other,found,pair.1.symm,pair.2.1.symm,flip_pairs pair.2.2⟩)
    (fun b a pair right left done called => by
      have related := children a b pair left right called done
      exact ⟨related.1.symm,related.2.symm⟩)
  refine ⟨?_,?_,forward.2.2,backward.2.2⟩
  · constructor
    · intro empty
      by_contra other
      exact backward.1 other empty
    · intro empty
      by_contra other
      exact forward.1 other empty
  · intro name
    exact ⟨forward.2.1 name,backward.2.1 name⟩

end MicroCFTA.SourceCurrentFiniteRootReconstruction
