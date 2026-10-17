import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.InternedEmptyNormalization

/-!
# Physical empty results of actual stored union reconstruction

The proof uses actual stored calls and the full cached union payload.
A closed root retains its original members. An open root exposes the actual
member sequence and union constructor. Source normalization then determines
physical emptiness. Finite observation agreement is not used as a premise.
-/
namespace MicroCFTA.SourceCurrentStoredUnionEmpty
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceEqualityRequiredCache (Ready)
open InternedBinderProtocol (NodeKey Reference)
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

/-- Actual warm reconstruction of a stored union is physically empty exactly when all original member returns are physically empty. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (Value Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (common : State Symbol Guard) (result : Value Symbol Guard)
    (outputs : List (Value Symbol Guard)) (ready : Ready common)
    (available : Available common (.union entry originals level free))
    (replacements : Replacements common environment)
    (called : execute (.union entry originals level free) environment common = .done result common)
    (paired : All₂ (fun original output => execute original environment common = .done output common) originals outputs) :
    result.referenceOf = .empty ↔ ∀ output ∈ outputs, output.referenceOf = .empty := by
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
    obtain ⟨value,member,nonempty⟩ := InternedNonemptyRecords.union_has_nonempty entry originals level free
      (InternedNonemptyRecords.resident_nonempty common ready.semantic.1.normal.proper _ available.resident)
    constructor
    · intro impossible
      cases impossible
    · intro allEmpty
      exact False.elim (nonempty (allEmpty value member))
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
    have emptyIff := InternedEmptyNormalization.makeUnion_empty_iff values middle
      kept.ready.semantic.1.normal.facts.coherent kept.ready.semantic.1.normal.facts.linked
      kept.ready.semantic.1.normal.live kept.ready.semantic.1.normal.proper outputsAvailable
    simpa only [made,outputsSame] using emptyIff

end MicroCFTA.SourceCurrentStoredUnionEmpty
