import MicroCFTA.SourceEmptinessClassFoldLocal
import MicroCFTA.SourceEmptinessDecision

/-!
# Refuted equality classes from actual seeded queries

The caller's seeded fold preserves a common proper subtree of every accepted
forest that satisfies its active class. Its completed scoped emptiness table
therefore cannot report empty for such a forest. The actual seeded result
and its returned native state supply the query and exploration input.

Ordinary paths require closedness only at their selected leaves. Unvisited
siblings may remain open at several levels. Recursive heads retain a closed
input premise. The proof does not derive this domain from the secondary gate.
Exact lazy demand, checked native transfer, and completion remain open.
-/
namespace MicroCFTA.SourceRefusedClassQuery
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNativeScoped SourceEmptinessClassFold
open SourceEqualityProjectionPathDomain (ForestClosed)
open InternedGuardedLanguage (meaning)

/-- The actual seeded schedule retains a strictly smaller common subtree of a satisfied active class. -/
theorem class_witness [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (paths : Class) (active : Nontrivial paths) (values : List (Value Symbol Guard))
    {query : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values (paths.map (List.map Int.ofNat)) before query after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (closed : ∀ path ∈ paths, ForestClosed (path.map Int.ofNat) values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (accepted : All₂ (meaning holds ambient) values terms)
    (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ part, meaning holds ambient query part ∧ part.height < (Term.node symbol terms).height := by
  obtain ⟨first, firstMember, other, otherMember, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstMember, other, otherMember, different⟩
  obtain ⟨part, found⟩ := class_member_exists (.node symbol terms) paths active satisfied first firstMember
  have nonroot := EqualityReduction.class_nonroot paths active (.node symbol terms) satisfied
  refine ⟨part, ?_, ?_⟩
  · apply trace.local_included ready available
      (by intro path member; obtain ⟨original, present, rfl⟩ := List.mem_map.mp member; exact closed original present)
      (by
        intro empty
        have original : paths = [] := List.map_eq_nil_iff.mp empty
        rw [original] at firstMember
        cases firstMember)
      (by
        intro path member empty
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact nonroot original present (List.map_eq_nil_iff.mp empty))
      holds ambient conjoined symbol terms part accepted
    intro path member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨common, firstFound, otherFound⟩ := class_pair_equal (.node symbol terms) paths active satisfied first original firstMember present
    have same : common = part := Option.some.inj (firstFound.symm.trans found)
    subst common
    simpa only [SourceEqualitySelectedRequired.lookup_natural] using otherFound
  · have bound := atPath_height_bound (.node symbol terms) part first found
    have positive : 0 < first.length := List.length_pos_iff.mpr (nonroot first firstMember)
    omega

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- A true completed seeded-query decision refutes satisfaction by every accepted original forest. -/
theorem refutes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (paths : Class) (active : Nontrivial paths) (values : List (Value Symbol Guard))
    {query : Value Symbol Guard} {before middle : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat)) before query middle)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (closed : ∀ path ∈ paths, ForestClosed (path.map Int.ofNat) values)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (trace : SourceEmptinessTaskTrace.Run top conjoin budget [] [SourceEmptinessTasks.Task.value query]
      (SourceEmptinessTasks.start middle) final after)
    (empty : ConservativeEmptinessTable.provablyEmpty (SourceEmptinessTaskTrace.table after final)
      (SourceEmptinessTaskTrace.encode query) = true)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬ClassSat (.node symbol terms) paths := by
  have localClosed : ∀ path ∈ paths.map (List.map Int.ofNat), ForestClosed path values := by
    intro path member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact closed original present
  have effects := seeded.local_effects ready available localClosed
  have queryFields := SourceEmptinessClassFields.seeded_local_fields seeded ready available localClosed fields
  have excludes := SourceEmptinessTaskSoundness.initial_excludes formulas solver ambient middle effects.1 queryFields
    trace query effects.2.2.1 effects.2.2.2 empty
  intro satisfied
  obtain ⟨part, acceptedPart, _⟩ := class_witness paths active values seeded ready available closed
    (SourceEqualityPCSGuard.holds formulas solver) ambient
    (SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver) symbol terms accepted satisfied
  exact excludes part acceptedPart

/-- The source query shortcuts and actual seeded result refute the original satisfied class. -/
theorem refutes_decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (paths : Class) (active : Nontrivial paths) (values : List (Value Symbol Guard))
    {query : Value Symbol Guard} {before middle after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat)) before query middle)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (closed : ∀ path ∈ paths, ForestClosed (path.map Int.ofNat) values)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (decision : SourceEmptinessDecision.Decision query middle true after)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬ClassSat (.node symbol terms) paths := by
  have localClosed : ∀ path ∈ paths.map (List.map Int.ofNat), ForestClosed path values := by
    intro path member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact closed original present
  have effects := seeded.local_effects ready available localClosed
  have queryFields := SourceEmptinessClassFields.seeded_local_fields seeded ready available localClosed fields
  have excludes := SourceEmptinessDecision.sound formulas solver ambient decision effects.1 queryFields
    effects.2.2.1 effects.2.2.2
  intro satisfied
  obtain ⟨part, acceptedPart, _⟩ := class_witness paths active values seeded ready available closed
    (SourceEqualityPCSGuard.holds formulas solver) ambient
    (SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver) symbol terms accepted satisfied
  exact excludes part acceptedPart

end MicroCFTA.SourceRefusedClassQuery
