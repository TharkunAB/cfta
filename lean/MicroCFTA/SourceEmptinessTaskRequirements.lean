import MicroCFTA.SourceEmptinessTaskLanguage
import MicroCFTA.SourceEmptinessTaskBodies

/-!
# Smaller witnesses for actual completed task requirements

Saved cell semantics and exact body receipts apply to the actual task read.
Normalized satisfied classes supply a common proper subtree of the original
accepted forest. Direct child tasks retain their original smaller subtree.
No final-heap projection or intersection operation is assumed here.
These results concern completed reads in the existing scoped trace model.
They do not prove completion or transfer the lazy Haskell demand schedule.
-/
namespace MicroCFTA.SourceEmptinessTaskRequirements
open Language EqualityNormalize InternedConstructorTemplates
open SourceEmptinessTasks SourceEmptinessTaskRows SourceEmptinessTaskBodies
open SourceEmptinessTaskLanguage
open InternedGuardedLanguage (meaning)
local notation "TaskState" => SourceEmptinessTasks.State

/-- A completed read at an exact body receipt has its saved common-subtree semantics. -/
theorem read_body (holds : Guard → Term Symbol → Bool)
    {state : TaskState width Symbol Guard} {body : Body Symbol Guard} {task : Task Symbol Guard}
    {value : Value Symbol Guard} (saved : Saved holds state) (receipt : BodyReceipt state body task)
    (completed : read state task = some value) : Includes holds body value := by
  obtain ⟨handle, cell, same, found, bodyEq⟩ := receipt
  subst task
  have actual : cell.result = some value := by
    simpa only [SourceEmptinessTasks.read, found, Option.bind_some] using completed
  simpa only [bodyEq] using saved handle cell value found actual

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Row" => ConservativeEmptinessRows.Row (Value Symbol Guard)

/-- A completed class task accepts the common strictly smaller subtree of its satisfied original class. -/
theorem class_witness (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    {state : TaskState width Symbol Guard} {children : List (Value Symbol Guard)} {paths : Class}
    {task : Task Symbol Guard} {value : Value Symbol Guard}
    (saved : Saved holds state) (receipt : ClassBodyReceipt children state paths task)
    (completed : read state task = some value) (active : Nontrivial paths)
    (symbol : Symbol) (terms : List (Term Symbol)) (accepted : All₂ (meaning holds ambient) children terms)
    (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ part, meaning holds ambient value part ∧ part.height < (Term.node symbol terms).height := by
  have included := read_body holds saved receipt completed
  obtain ⟨first, firstMember, other, otherMember, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstMember, other, otherMember, different⟩
  obtain ⟨part, found⟩ := class_member_exists (.node symbol terms) paths active satisfied first firstMember
  have nonroot := EqualityReduction.class_nonroot paths active (.node symbol terms) satisfied
  refine ⟨part, ?_, ?_⟩
  · apply included ambient symbol terms part
    · intro path member empty
      change path ∈ paths.map (List.map Int.ofNat) at member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact nonroot original present (List.map_eq_nil_iff.mp empty)
    · exact accepted
    · intro path member
      change path ∈ paths.map (List.map Int.ofNat) at member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨common, firstFound, otherFound⟩ :=
        class_pair_equal (.node symbol terms) paths active satisfied first original firstMember present
      have same : common = part := Option.some.inj (firstFound.symm.trans found)
      subst common
      simpa only [SourceEqualitySelectedRequired.lookup_natural] using otherFound
  · have bound := atPath_height_bound (.node symbol terms) part first found
    have positive : 0 < first.length := List.length_pos_iff.mpr (nonroot first firstMember)
    omega

private theorem paired_member {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) {value : β} (member : value ∈ second) :
    ∃ original ∈ first, relation original value := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨original, present, related⟩ := ih member
        exact ⟨original, List.mem_cons_of_mem _ present, related⟩

/-- Every actual completed row task has a strictly smaller accepted witness in its actual read result. -/
theorem row_witness (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    {state : TaskState width Symbol Guard} {row : Row} {tasks : List (Task Symbol Guard)}
    (saved : Saved holds state) (receipt : RowBodyReceipt state row tasks) (active : Active row.classes)
    (symbol : Symbol) (terms : List (Term Symbol)) (satisfied : Satisfies (.node symbol terms) row.classes)
    (accepted : All₂ (meaning holds ambient) row.children terms)
    (complete : ∀ task ∈ tasks, SourceEmptinessTaskTrace.Complete state task) :
    ∀ task ∈ tasks, ∃ value part, read state task = some value ∧ meaning holds ambient value part ∧
      part.height < (Term.node symbol terms).height := by
  obtain ⟨classes, same, receipts⟩ := receipt
  intro task member
  have original := member
  rw [same] at member
  rcases List.mem_append.mp member with direct | captured
  · obtain ⟨child, present, rfl⟩ := List.mem_map.mp direct
    obtain ⟨part, selected, acceptedPart⟩ :=
      SymbolicSmartRows.all₂_child (meaning holds ambient) row.children terms accepted child present
    refine ⟨child, part, rfl, acceptedPart, ?_⟩
    have bound := height_le_forestHeight terms part selected
    simpa only [Term.height, forestHeight] using Nat.lt_succ_of_le bound
  · obtain ⟨paths, present, body⟩ := paired_member receipts captured
    obtain ⟨value, completed, _, _⟩ := complete task original
    obtain ⟨part, acceptedPart, smaller⟩ :=
      class_witness holds ambient saved body completed (active paths present) symbol terms accepted (satisfied paths present)
    exact ⟨value, part, completed, acceptedPart, smaller⟩

end MicroCFTA.SourceEmptinessTaskRequirements
