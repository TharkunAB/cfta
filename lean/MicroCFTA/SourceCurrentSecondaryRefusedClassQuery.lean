import MicroCFTA.SourceCurrentSecondaryClassFold
import MicroCFTA.SourceCurrentEmptinessMemo

/-!
# Refuted source classes from secondary gates and actual seeded queries

Actual false class traces supply one fixed projection anchor. Under a
satisfied active class, all paths are proper. Its actual seeded query then
retains a common accepted subtree. A true conservative emptiness decision
excludes that subtree. No static whole-forest closedness premise is needed.
Scoped native receipts and completed exploration retain their stated limits.
-/
namespace MicroCFTA.SourceCurrentSecondaryRefusedClassQuery
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityNativeScoped SourceEmptinessClassFold
open SourceCurrentSecondaryProjectionScoped SourceCurrentSecondaryClassFold
open InternedGuardedLanguage (meaning)

/-- The actual supported seeded schedule retains a strictly smaller common accepted subtree. -/
theorem class_witness [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (paths : Class) (active : Nontrivial paths) (values : List (Value Symbol Guard))
    {query : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values (paths.map (List.map Int.ofNat)) before query after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor (path.map Int.ofNat) values)
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
  · apply seeded_included unconstrained anchor anchorSemantic anchorReady trace ready available growth
      (by
        intro path member
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact supported original present)
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
    obtain ⟨common, firstFound, otherFound⟩ := class_pair_equal (.node symbol terms) paths active satisfied
      first original firstMember present
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

/-- A completed false class gate and true actual seeded-query decision refute the original class. -/
theorem refutes_decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (paths : Class) (active : Nontrivial paths)
    (values : List (Value Symbol Guard)) {initial anchor : State Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths initial false anchor)
    (initialSemantic : SemanticReady initial) (initialReady : InternedFreshOrdinaryMemoGateTrace.Ready initial)
    (initialAvailable : Values initial values)
    {query : Value Symbol Guard} {before middle after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat)) before query middle)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap) (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (decision : SourceCurrentEmptinessDecision.Decision query middle true after)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬ClassSat (.node symbol terms) paths := by
  intro satisfied
  have nonroot := EqualityReduction.class_nonroot paths active (.node symbol terms) satisfied
  have anchored := SourceCurrentSecondaryProjectionAnchor.class_anchor unconstrained gate initialSemantic initialReady initialAvailable
  have supported : ∀ path ∈ paths, PathSupport unconstrained anchor (path.map Int.ofNat) values := by
    intro path member
    exact path_support_of_false (anchored.2.2.2.2.2 path member) (nonroot path member) anchored.2.2.2.1
  have signedSupport : ∀ path ∈ paths.map (List.map Int.ofNat), PathSupport unconstrained anchor path values := by
    intro path member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact supported original present
  have effects := seeded_effects unconstrained anchor anchored.1 anchored.2.1 seeded ready available growth signedSupport
  have queryFields := SourceCurrentSecondaryClassFold.seeded_fields unconstrained anchor anchored.1 anchored.2.1
    seeded ready available growth signedSupport fields
  have excludes := SourceCurrentEmptinessDecision.sound formulas solver ambient decision effects.1 queryFields
    effects.2.2.1
  obtain ⟨part, acceptedPart, _⟩ := class_witness unconstrained anchor anchored.1 anchored.2.1 paths active values
    seeded ready available growth supported (SourceEqualityPCSGuard.holds formulas solver) ambient
    (SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver) symbol terms accepted satisfied
  exact excludes part acceptedPart

/-- A true fourth-memo hit or actual miss refutes the original class under its initial memo invariant. -/
theorem refutes_memo [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (paths : Class) (active : Nontrivial paths)
    (values : List (Value Symbol Guard)) {initial anchor : State Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths initial false anchor)
    (initialSemantic : SemanticReady initial) (initialReady : InternedFreshOrdinaryMemoGateTrace.Ready initial)
    (initialAvailable : Values initial values)
    {query : Value Symbol Guard} {before middle after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat)) before query middle)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap) (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (call : SourceCurrentEmptinessMemo.Call memo query middle true after saved)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬ClassSat (.node symbol terms) paths := by
  intro satisfied
  have nonroot := EqualityReduction.class_nonroot paths active (.node symbol terms) satisfied
  have anchored := SourceCurrentSecondaryProjectionAnchor.class_anchor unconstrained gate initialSemantic initialReady initialAvailable
  have supported : ∀ path ∈ paths, PathSupport unconstrained anchor (path.map Int.ofNat) values := by
    intro path member
    exact path_support_of_false (anchored.2.2.2.2.2 path member) (nonroot path member) anchored.2.2.2.1
  have signedSupport : ∀ path ∈ paths.map (List.map Int.ofNat), PathSupport unconstrained anchor path values := by
    intro path member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact supported original present
  have effects := seeded_effects unconstrained anchor anchored.1 anchored.2.1 seeded ready available growth signedSupport
  have queryFields := SourceCurrentSecondaryClassFold.seeded_fields unconstrained anchor anchored.1 anchored.2.1
    seeded ready available growth signedSupport fields
  have checked := SourceCurrentEmptinessMemo.verified formulas solver call effects.1 queryFields effects.2.2.1
    (SourceCurrentEmptinessMemo.grows formulas solver effects.2.1 memo correct)
  have excludes := checked.2.2.2.2.1.2 rfl ambient
  obtain ⟨part, acceptedPart, _⟩ := class_witness unconstrained anchor anchored.1 anchored.2.1 paths active values
    seeded ready available growth supported (SourceEqualityPCSGuard.holds formulas solver) ambient
    (SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver) symbol terms accepted satisfied
  exact excludes part acceptedPart

end MicroCFTA.SourceCurrentSecondaryRefusedClassQuery
