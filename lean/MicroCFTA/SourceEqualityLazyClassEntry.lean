import MicroCFTA.SourceEqualityPrecheck
import MicroCFTA.SourceEqualityGuardReadback
import MicroCFTA.SourceEqualityLazyClassSoundness

/-!
# Ordered normalized source classes at the lazy scan entry

The precheck returns the exact sort of the original physical class records.
Cached source equalities derive activity and independent satisfaction for
that ordered list. Each record keeps its original trie and path payload.

Physical record coherence and exact equality-accessor readback are explicit
premises. This module does not extract Haskell native records from a guard.
The stopped-scan theorem retains its scoped execution and runtime limits.
-/
namespace MicroCFTA.SourceEqualityLazyClassEntry
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityClassOrder SourceEqualityRequiredCache SourceEqualityNativeScoped
open SourceEqualityLazyClassPrefix
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- The exact source sort retains coherent original records, activity, and actual accessor satisfaction. -/
theorem ordered_entry (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (records : List Record) (coherent : ∀ record ∈ records, Coherent record)
    (readback : SourceCompactGuards.sourceEqualities constraint = some (records.map Record.paths)) :
    (∀ record ∈ ordered records, Coherent record) ∧ Active ((ordered records).map Record.paths) ∧
      ∀ term : Term Symbol, Satisfies term ((ordered records).map Record.paths) ↔
        SourceEqualityGuardReadback.Sat term (SourceCompactGuards.sourceEqualities constraint) := by
  have normal := SourceEqualityGuardReadback.source_cached constraint cached (records.map Record.paths) readback
  have sameMembers := (ordered_perm records).map Record.paths
  refine ⟨ordered_coherent records coherent, ?_, ?_⟩
  · intro paths member
    exact normal.1 paths (sameMembers.mem_iff.mp member)
  · intro term
    rw [readback]
    change Satisfies term ((ordered records).map Record.paths) ↔ Satisfies term (records.map Record.paths)
    constructor
    · intro satisfied paths member
      exact satisfied paths (sameMembers.mem_iff.mpr member)
    · intro satisfied paths member
      exact satisfied paths (sameMembers.mem_iff.mp member)

/-- The actual live precheck fixes the original record sort before deriving the scan's semantic entry laws. -/
theorem live_entry (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (records : List Record) (coherent : ∀ record ∈ records, Coherent record)
    (readback : SourceCompactGuards.sourceEqualities constraint = some (records.map Record.paths))
    (inherited : SourceEqualityPrecheck.Constraint) (output : List Record)
    (live : SourceEqualityPrecheck.precheck (some records) inherited = .ok (.classes output)) :
    output = ordered records ∧ (∀ record ∈ output, Coherent record) ∧ Active (output.map Record.paths) ∧
      ∀ term : Term Symbol, Satisfies term (output.map Record.paths) ↔
        SourceEqualityGuardReadback.Sat term (SourceCompactGuards.sourceEqualities constraint) := by
  obtain ⟨original, own, same, _⟩ := SourceEqualityPrecheck.live_payload (some records) inherited output live
  have originalEq : records = original := Option.some.inj own
  subst original
  refine ⟨same, ?_⟩
  rw [same]
  exact ordered_entry constraint cached records coherent readback

/-- A stopped actual scan refutes the original accessor payload after deriving its exact ordered active entry. -/
theorem stopped_refutes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (records : List Record) (coherent : ∀ record ∈ records, Coherent record)
    (readback : SourceCompactGuards.sourceEqualities constraint = some (records.map Record.paths))
    (inherited : SourceEqualityPrecheck.Constraint) (output : List Record)
    (live : SourceEqualityPrecheck.precheck (some records) inherited = .ok (.classes output))
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {selected : Constraints} {paths : Class}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Scan unconstrained reaches values (output.map Record.paths) before (some paths) selected after)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬SourceEqualityGuardReadback.Sat (.node symbol terms) (SourceCompactGuards.sourceEqualities constraint) := by
  have entry := live_entry constraint cached records coherent readback inherited output live
  have excluded := SourceEqualityLazyClassSoundness.stopped_refutes trace ready available costs fields entry.2.2.1
    formulas solver ambient symbol terms accepted
  exact fun satisfied => excluded ((entry.2.2.2 (.node symbol terms)).mpr satisfied)

end MicroCFTA.SourceEqualityLazyClassEntry
