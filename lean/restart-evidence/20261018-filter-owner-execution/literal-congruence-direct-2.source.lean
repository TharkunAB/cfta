import MicroCFTA.SourceCurrentLiteralOrdinaryParts
import MicroCFTA.SourceCurrentStoredUnionLiteralParts
import MicroCFTA.SourceCurrentStoredReconstruction

/-!
# Stored reconstruction from equal literal root parts

Literal Mu values stay opaque at the root comparison. Each equal atom uses
the same actual stored call. Each equal ordinary row uses the same ordered
child calls. Union normalization can change grouping and row order.
-/
namespace MicroCFTA.SourceCurrentStoredLiteralCongruence
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceCurrentLiteralRootParts (Literal Row SameParts)
open SourceCurrentStoredNodeExpansion (RowCalls)
open Language

private def LiteralOutput [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (raw atom : Value Symbol Guard) : Prop :=
  ∃ source, Literal raw source ∧ ∃ output,
    execute source environment common = .done output common ∧ Literal output atom

private def RowOutput [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (raw : Value Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  (∃ source, Literal raw source ∧ ∃ output,
    execute source environment common = .done output common ∧ Row output row) ∨
  ∃ source, Row raw source ∧ RowCalls environment common source row ∧
    (!(row.children.any (fun child => child.referenceOf == .empty))) = true

private theorem pair_left {A B : Type} {relation : A → B → Prop}
    {first : List A} {second : List B} (paired : All₂ relation first second)
    (value : A) (member : value ∈ first) : ∃ output ∈ second, relation value output := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,head⟩
      · obtain ⟨output,included,actual⟩ := ih later
        exact ⟨output,List.mem_cons_of_mem _ included,actual⟩

private theorem pair_right {A B : Type} {relation : A → B → Prop}
    {first : List A} {second : List B} (paired : All₂ relation first second)
    (output : B) (member : output ∈ second) : ∃ value ∈ first, relation value output := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,head⟩
      · obtain ⟨value,included,actual⟩ := ih later
        exact ⟨value,List.mem_cons_of_mem _ included,actual⟩

private theorem row_unique [DecidableEq (EdgeKey Symbol Guard)]
    {environment : Environment Symbol Guard} {common : State Symbol Guard}
    {source first second : EdgeValue Symbol Guard} (valid : Valid common)
    (left : RowCalls environment common source first)
    (right : RowCalls environment common source second) : first = second := by
  have children := SourceCurrentStoredCallsReplay.same left.1 right.1 common valid valid
    (grows_refl _) (grows_refl _)
  have made := left.2.1
  rw [children] at made
  exact congrArg Prod.fst (made.symm.trans right.2.1)

private theorem ordinary_row [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (ordinary : Ordinary value) (view : State Symbol Guard)
    (row : EdgeValue Symbol Guard) : Row value row ↔ MergedFreshOrdinaryGraph.Origin view [value] row := by
  cases value with
  | empty =>
      exact iff_of_false (by intro impossible; cases impossible) (MergedFreshOrdinaryGraph.origin_empty view row)
  | node entry rows level free =>
      exact (SourceCurrentLiteralRootParts.row_node entry rows level free row).trans
        (MergedFreshOrdinaryGraph.origin_node view entry rows level free row).symm
  | reference | union | mu => cases ordinary

private theorem atom_parts [DecidableEq (EdgeKey Symbol Guard)]
    (raw result : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (actual : execute raw environment common = .done result common)
    (self : Literal raw raw) (single : ∀ atom, Literal raw atom → atom = raw)
    (noRows : ∀ row, ¬ Row raw row) :
    (∀ atom, Literal result atom ↔ LiteralOutput environment common raw atom) ∧
      ∀ row, Row result row ↔ RowOutput environment common raw row := by
  constructor
  · intro atom
    constructor
    · exact fun found => ⟨raw,self,result,actual,found⟩
    · rintro ⟨source,part,output,called,found⟩
      have same := single source part
      subst source
      obtain ⟨rfl,_⟩ := Outcome.done.inj (called.symm.trans actual)
      exact found
  · intro row
    constructor
    · exact fun found => Or.inl ⟨raw,self,result,actual,found⟩
    · rintro (⟨source,part,output,called,found⟩ | ⟨source,part,_,_⟩)
      · have same := single source part
        subst source
        obtain ⟨rfl,_⟩ := Outcome.done.inj (called.symm.trans actual)
        exact found
      · exact False.elim (noRows source part)

private theorem atomic_parts [DecidableEq (EdgeKey Symbol Guard)]
    (raw result : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (ready : Ready common) (available : Available common raw)
    (replacements : Replacements common environment) (atomic : InternedUnionNormalForm.Atomic raw)
    (actual : execute raw environment common = .done result common) :
    (∀ atom, Literal result atom ↔ LiteralOutput environment common raw atom) ∧
      ∀ row, Row result row ↔ RowOutput environment common raw row := by
  cases raw with
  | empty =>
      have same := (Outcome.done.inj (actual.symm.trans
        (SourceCurrentStoredUnionObservations.closed .empty environment common rfl))).1
      subst result
      constructor
      · intro atom
        exact iff_of_false (by intro impossible; cases impossible)
          (by rintro ⟨source,part,_,_,_⟩; cases part)
      · intro row
        exact iff_of_false (by intro impossible; cases impossible)
          (by rintro (⟨source,part,_,_,_⟩ | ⟨source,part,_,_⟩) <;> cases part)
  | reference name =>
      exact atom_parts _ _ _ _ actual (.reference name)
        (by intro atom found; cases found; rfl) (by intro row found; cases found)
  | mu entry body depth ordinary =>
      exact atom_parts _ _ _ _ actual (.mu entry body depth ordinary)
        (by intro atom found; cases found; rfl) (by intro row found; cases found)
  | union => cases atomic
  | node entry originals level free =>
      obtain ⟨outputs,paired,plain,origins⟩ := SourceCurrentStoredNodeExpansion.node_warm
        entry originals level free environment common ready.semantic.1.normal available replacements result actual
      constructor
      · intro atom
        exact iff_of_false (by cases result <;> try cases plain <;> intro impossible <;> cases impossible)
          (by rintro ⟨source,part,_,_,_⟩; cases part)
      · intro row
        rw [ordinary_row result plain common row,origins]
        constructor
        · intro retained
          obtain ⟨source,member,called⟩ := pair_right paired row (List.mem_filter.mp retained).1
          exact Or.inr ⟨source,.node member,called,(List.mem_filter.mp retained).2⟩
        · rintro (⟨source,part,_,_,_⟩ | ⟨source,part,called,live⟩)
          · cases part
          · cases part with
            | node member =>
                obtain ⟨output,included,other⟩ := pair_left paired source member
                have same := row_unique ready.semantic.1.normal.facts.coherent.valid called other
                subst output
                exact List.mem_filter.mpr ⟨included,live⟩

private theorem raw_parts [DecidableEq (EdgeKey Symbol Guard)]
    (raw result : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (ready : Ready common) (available : Available common raw)
    (replacements : Replacements common environment)
    (actual : execute raw environment common = .done result common) :
    (∀ atom, Literal result atom ↔ LiteralOutput environment common raw atom) ∧
      ∀ row, Row result row ↔ RowOutput environment common raw row := by
  cases raw with
  | empty | reference | node | mu => exact atomic_parts _ _ _ _ ready available replacements trivial actual
  | union entry originals level free =>
      obtain ⟨value,after,outputs,middle,called,calls,_,_,_,_,growth,_⟩ :=
        SourceCurrentStoredUnionObservations.complete entry originals level free environment common ready available replacements
      have same := Outcome.done.inj (called.symm.trans actual)
      have lastGrowth : Grows middle common := same.2 ▸ growth
      have paired := SourceCurrentStoredCallsReplay.replay calls common ready.semantic.1.normal.facts.coherent.valid lastGrowth
      have parts := SourceCurrentStoredUnionLiteralParts.warm entry originals level free environment common result outputs
        ready available replacements actual paired
      have flat := InternedUnionNormalForm.resident_flat common ready.semantic.1.normal.flat _ available.resident
      have each (source output : Value Symbol Guard) (member : source ∈ originals)
          (done : execute source environment common = .done output common) :=
        atomic_parts source output environment common ready (available.children source member) replacements (flat source member) done
      constructor
      · intro atom
        rw [parts.1]
        constructor
        · rintro ⟨output,member,found⟩
          obtain ⟨source,included,done⟩ := pair_right paired output member
          obtain ⟨old,literal,rebuilt,executed,part⟩ := ((each source output included done).1 atom).mp found
          exact ⟨old,.union included literal,rebuilt,executed,part⟩
        · rintro ⟨old,literal,rebuilt,executed,part⟩
          obtain ⟨source,included,inside⟩ := (SourceCurrentLiteralRootParts.literal_union entry originals level free old).mp literal
          obtain ⟨output,member,done⟩ := pair_left paired source included
          exact ⟨output,member,((each source output included done).1 atom).mpr ⟨old,inside,rebuilt,executed,part⟩⟩
      · intro row
        rw [parts.2]
        constructor
        · rintro ⟨output,member,found⟩
          obtain ⟨source,included,done⟩ := pair_right paired output member
          rcases ((each source output included done).2 row).mp found with
            ⟨old,literal,rebuilt,executed,part⟩ | ⟨old,oldRow,called,live⟩
          · exact Or.inl ⟨old,.union included literal,rebuilt,executed,part⟩
          · exact Or.inr ⟨old,.union included oldRow,called,live⟩
        · rintro (⟨old,literal,rebuilt,executed,part⟩ | ⟨old,oldRow,called,live⟩)
          · obtain ⟨source,included,inside⟩ := (SourceCurrentLiteralRootParts.literal_union entry originals level free old).mp literal
            obtain ⟨output,member,done⟩ := pair_left paired source included
            exact ⟨output,member,((each source output included done).2 row).mpr (Or.inl ⟨old,inside,rebuilt,executed,part⟩)⟩
          · obtain ⟨source,included,inside⟩ := (SourceCurrentLiteralRootParts.row_union entry originals level free old).mp oldRow
            obtain ⟨output,member,done⟩ := pair_left paired source included
            exact ⟨output,member,((each source output included done).2 row).mpr (Or.inr ⟨old,inside,called,live⟩)⟩

/-- Equal complete root parts retain equal parts through the same actual warm reconstruction. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)]
    (first second left right : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (ready : Ready common)
    (firstAvailable : Available common first) (secondAvailable : Available common second)
    (replacements : Replacements common environment) (parts : SameParts first second)
    (firstDone : execute first environment common = .done left common)
    (secondDone : execute second environment common = .done right common) : SameParts left right := by
  have firstParts := raw_parts first left environment common ready firstAvailable replacements firstDone
  have secondParts := raw_parts second right environment common ready secondAvailable replacements secondDone
  constructor
  · intro atom
    rw [firstParts.1,secondParts.1]
    constructor
    · rintro ⟨source,literal,output,called,found⟩
      exact ⟨source,(parts.1 source).mp literal,output,called,found⟩
    · rintro ⟨source,literal,output,called,found⟩
      exact ⟨source,(parts.1 source).mpr literal,output,called,found⟩
  · intro row
    rw [firstParts.2,secondParts.2]
    constructor
    · rintro (⟨source,literal,output,called,found⟩ | ⟨source,part,called,live⟩)
      · exact Or.inl ⟨source,(parts.1 source).mp literal,output,called,found⟩
      · exact Or.inr ⟨source,(parts.2 source).mp part,called,live⟩
    · rintro (⟨source,literal,output,called,found⟩ | ⟨source,part,called,live⟩)
      · exact Or.inl ⟨source,(parts.1 source).mpr literal,output,called,found⟩
      · exact Or.inr ⟨source,(parts.2 source).mpr part,called,live⟩

end MicroCFTA.SourceCurrentStoredLiteralCongruence
