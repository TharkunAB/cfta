import MicroCFTA.SourceCurrentLiteralUnionParts
import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.SourceCurrentStoredUnionFlattening

/-!
# Literal parts of actual stored union reconstruction

Closed roots retain their full original payload. Open roots retain the
actual ordered member calls and the literal union constructor. Both cases
retain exact literal atoms and ordinary rows at one common warm heap.
The predicates do not expose references through a Mu body.
-/
namespace MicroCFTA.SourceCurrentStoredUnionLiteralParts
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceEqualityRequiredCache (Ready)
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentLiteralRootParts (Literal Row)
open Language

private theorem paired_equal [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    {originals first second : List (Value Symbol Guard)}
    (left : All₂ (fun original output => execute original environment common = .done output common) originals first)
    (right : All₂ (fun original output => execute original environment common = .done output common) originals second) :
    first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons called rest ih =>
      cases right with
      | cons other later =>
          have head := (Outcome.done.inj (called.symm.trans other)).1
          exact congr (congrArg List.cons head) (ih later)

private theorem calls_unique [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {originals values other : List (Value Symbol Guard)} {before after final : State Symbol Guard}
    (first : Calls environment originals before values after) (second : Calls environment originals before other final) :
    values = other ∧ after = final := by
  induction first generalizing other final with
  | nil => cases second; exact ⟨rfl,rfl⟩
  | cons original originals before middle after value values actual rest ih =>
      cases second with
      | cons _ _ _ next final output outputs done later =>
          obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans done)
          obtain ⟨rfl,rfl⟩ := ih later
          exact ⟨rfl,rfl⟩

private theorem closed_pairs [DecidableEq (EdgeKey Symbol Guard)] (originals : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (closed : ∀ value ∈ originals, value.free = []) :
    All₂ (fun original output => execute original environment common = .done output common) originals originals := by
  induction originals with
  | nil => exact .nil
  | cons original originals ih =>
      exact .cons (SourceCurrentStoredUnionObservations.closed original environment common
        (closed original List.mem_cons_self))
        (ih (fun value member => closed value (List.mem_cons_of_mem _ member)))

/-- Actual warm stored union reconstruction retains exactly the literal atoms and ordinary rows of its original member returns. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (Value Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (common : State Symbol Guard) (result : Value Symbol Guard)
    (outputs : List (Value Symbol Guard)) (ready : Ready common)
    (available : Available common (.union entry originals level free))
    (replacements : Replacements common environment)
    (called : execute (.union entry originals level free) environment common = .done result common)
    (paired : All₂ (fun original output => execute original environment common = .done output common) originals outputs) :
    (∀ atom, Literal result atom ↔ ∃ output ∈ outputs, Literal output atom) ∧
      ∀ row, Row result row ↔ ∃ output ∈ outputs, Row output row := by
  have inputs : Values common originals := fun value member => available.children value member
  by_cases closed : free = []
  · have fields := InternedNormalizationFree.union_free common ready.semantic.1.normal.facts.coherent
      entry originals level free available.resident
    have closedMembers : ∀ value ∈ originals, value.free = [] := by
      intro value member
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name named
      have included := (childFree_member originals name).mpr ⟨value,member,named⟩
      rw [←fields,closed] at included
      cases included
    have outputsSame := paired_equal environment common paired (closed_pairs originals environment common closedMembers)
    have resultSame := (Outcome.done.inj (called.symm.trans
      (SourceCurrentStoredUnionObservations.closed _ environment common closed))).1
    rw [outputsSame,resultSame]
    exact ⟨fun atom => SourceCurrentLiteralRootParts.literal_union entry originals level free atom,
      fun row => SourceCurrentLiteralRootParts.row_union entry originals level free row⟩
  · have opened : free.isEmpty = false := by simpa only [List.isEmpty_eq_false_iff] using closed
    obtain ⟨values,middle,calls,made,_⟩ := SourceCurrentStoredSubstitutionOrigins.union entry originals level free
      environment common ready.semantic.1.normal available replacements opened result common called
    obtain ⟨produced,memberAfter,memberCalls,kept,outputsAvailable⟩ :=
      SourceCurrentStoredUnionObservations.members originals environment common ready inputs replacements
    obtain ⟨rfl,rfl⟩ := calls_unique calls memberCalls
    have growth : Grows middle common := by
      simpa only [made] using (run_correct (makeUnion values) middle kept.ready.semantic.1.normal.facts.coherent.valid).2
    have repeated := SourceCurrentStoredCallsReplay.replay calls common ready.semantic.1.normal.facts.coherent.valid growth
    have outputsSame := paired_equal environment common repeated paired
    constructor
    · intro atom
      have part := SourceCurrentLiteralUnionParts.literal middle kept.ready.semantic.1.normal.facts values outputsAvailable atom
      rw [made] at part
      simpa only [outputsSame] using part
    · intro row
      have part := SourceCurrentLiteralUnionParts.row middle kept.ready.semantic.1.normal.facts
        kept.ready.semantic.1.normal.live values outputsAvailable row
      rw [made] at part
      simpa only [outputsSame] using part

private theorem paired_append {α β : Type} {relation : α → β → Prop}
    (first next : List α) {outputs : List β} (paired : All₂ relation (first ++ next) outputs) :
    ∃ left right, outputs = left ++ right ∧ All₂ relation first left ∧ All₂ relation next right := by
  induction first generalizing outputs with
  | nil => exact ⟨[],outputs,rfl,.nil,paired⟩
  | cons original originals ih =>
      cases paired with
      | cons head tail =>
          obtain ⟨left,right,same,matched,remaining⟩ := ih tail
          exact ⟨_::left,right,by rw [same]; rfl,.cons head matched,remaining⟩

private theorem member_parts [DecidableEq (EdgeKey Symbol Guard)]
    (original result : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (outputs : List (Value Symbol Guard)) (ready : Ready common)
    (available : Available common original) (replacements : Replacements common environment)
    (called : execute original environment common = .done result common)
    (paired : All₂ (fun original output => execute original environment common = .done output common)
      (unionMembers original) outputs) :
    (∀ atom, Literal result atom ↔ ∃ output ∈ outputs, Literal output atom) ∧
      ∀ row, Row result row ↔ ∃ output ∈ outputs, Row output row := by
  cases original with
  | empty =>
      cases paired
      have same := (Outcome.done.inj (called.symm.trans
        (SourceCurrentStoredUnionObservations.closed .empty environment common rfl))).1
      rw [same]
      constructor
      · intro atom
        constructor
        · intro impossible; cases impossible
        · rintro ⟨_,present,_⟩; cases present
      · intro row
        constructor
        · intro impossible; cases impossible
        · rintro ⟨_,present,_⟩; cases present
  | node | reference | mu =>
      cases paired with
      | cons head tail =>
          cases tail
          have same := (Outcome.done.inj (called.symm.trans head)).1
          constructor
          · intro atom
            simp only [same,List.mem_singleton,exists_eq_left]
          · intro row
            simp only [same,List.mem_singleton,exists_eq_left]
  | union entry originals level free =>
      exact warm entry originals level free environment common result outputs ready available replacements called paired

private theorem flatten_parts [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard) (ready : Ready common)
    {originals outputs flattened : List (Value Symbol Guard)}
    (available : Values common originals) (replacements : Replacements common environment)
    (actual : All₂ (fun original output => execute original environment common = .done output common) originals outputs)
    (paired : All₂ (fun original output => execute original environment common = .done output common)
      (originals.flatMap unionMembers) flattened) :
    (∀ atom, (∃ output ∈ outputs, Literal output atom) ↔ ∃ output ∈ flattened, Literal output atom) ∧
      ∀ row, (∃ output ∈ outputs, Row output row) ↔ ∃ output ∈ flattened, Row output row := by
  induction actual generalizing flattened with
  | nil => cases paired; exact ⟨fun _ => Iff.rfl,fun _ => Iff.rfl⟩
  | @cons original output originals outputs called rest ih =>
      obtain ⟨first,last,rfl,firstCalls,lastCalls⟩ := paired_append (unionMembers original)
        (originals.flatMap unionMembers) (by simpa only [List.flatMap_cons] using paired)
      have firstParts := member_parts original output environment common first ready
        (available original List.mem_cons_self) replacements called firstCalls
      have restParts := ih (fun value member => available value (List.mem_cons_of_mem _ member)) lastCalls
      constructor
      · intro atom
        simpa only [List.mem_cons,List.mem_append,or_and_right,exists_or,exists_eq_left] using
          or_congr (firstParts.1 atom) (restParts.1 atom)
      · intro row
        simpa only [List.mem_cons,List.mem_append,or_and_right,exists_or,exists_eq_left] using
          or_congr (firstParts.2 row) (restParts.2 row)

/-- Actual flattened member calls retain exactly the literal atoms and ordinary rows of the original warm return list. -/
theorem flatten_warm [DecidableEq (EdgeKey Symbol Guard)]
    (originals outputs : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (ready : Ready common)
    (available : Values common originals) (replacements : Replacements common environment)
    (actual : All₂ (fun original output => execute original environment common = .done output common) originals outputs) :
    ∃ flattened,
      All₂ (fun original output => execute original environment common = .done output common)
        (originals.flatMap unionMembers) flattened ∧
      (∀ atom, (∃ output ∈ outputs, Literal output atom) ↔ ∃ output ∈ flattened, Literal output atom) ∧
      (∀ row, (∃ output ∈ outputs, Row output row) ↔ ∃ output ∈ flattened, Row output row) ∧
      ∀ depth view, SourceCurrentOpenObservations.Same depth view outputs flattened := by
  obtain ⟨flattened,called,observed⟩ := SourceCurrentStoredUnionFlattening.warm
    originals outputs environment common ready available replacements actual
  have parts := flatten_parts environment common ready available replacements actual called
  exact ⟨flattened,called,parts.1,parts.2,observed⟩

end MicroCFTA.SourceCurrentStoredUnionLiteralParts
