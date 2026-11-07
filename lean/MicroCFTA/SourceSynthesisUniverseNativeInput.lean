import MicroCFTA.SourceSynthesisFirstOrderConstruction
import MicroCFTA.InternedFreshOrdinaryFirstOrderCompletion

/-!
# Completion of the repaired default synthesis universe

The actual allTypes body contains no nested binder. The repaired constructor
therefore completes from the empty cache without a supplied successful run.
The result retains its actual records and cache histories. This module does
not identify the result's constructor tag or assert native Haskell execution.
-/
namespace MicroCFTA.SourceSynthesisUniverseNativeInput
open SourceSynthesisTypeSyntax
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedStoredShallowCompletion

variable {Guard : Type}

mutual
/-- The source Boolean test detects exactly the binder-free constructor syntax. -/
theorem noBinders_iff_binderFree (expression : Expr Guard) :
    noBinders expression = true ↔ BinderFree expression := by
  cases expression with
  | empty | var => simp [noBinders, BinderFree]
  | binder => simp [noBinders, BinderFree]
  | node rows =>
      simpa only [BinderFree] using edgeNoBinders_iff_edgesBinderFree rows
  | union children =>
      simpa only [BinderFree] using childNoBinders_iff_manyBinderFree children
termination_by sizeOf expression

/-- A union wrapper exposes the private source test for ordered children. -/
theorem childNoBinders_iff_manyBinderFree (expressions : List (Expr Guard)) :
    noBinders (.union expressions) = true ↔ ManyBinderFree expressions := by
  cases expressions with
  | nil =>
      rw [ManyBinderFree]
      change true = true ↔ True
      simp
  | cons first rest =>
      rw [ManyBinderFree]
      change (noBinders first && noBinders (.union rest)) = true ↔
        BinderFree first ∧ ManyBinderFree rest
      rw [Bool.and_eq_true, noBinders_iff_binderFree first,
        childNoBinders_iff_manyBinderFree rest]
termination_by sizeOf expressions

/-- A node wrapper exposes the private source test for ordered edge children. -/
theorem edgeNoBinders_iff_edgesBinderFree (expressions : List (EdgeSyntax String Guard)) :
    noBinders (.node expressions) = true ↔ EdgesBinderFree expressions := by
  cases expressions with
  | nil =>
      rw [EdgesBinderFree]
      change true = true ↔ True
      simp
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [EdgesBinderFree]
          change (noBinders (.union children) && noBinders (.node rest)) = true ↔
            ManyBinderFree children ∧ EdgesBinderFree rest
          rw [Bool.and_eq_true, childNoBinders_iff_manyBinderFree children,
            edgeNoBinders_iff_edgesBinderFree rest]
termination_by sizeOf expressions
end

/-- The actual universe body satisfies the repaired completion theorem. -/
theorem allTypesBody_binderFree (top : Guard) (catalog : List (String × Nat)) :
    BinderFree (allTypesBody top catalog) :=
  (noBinders_iff_binderFree _).mp (allTypesBody_noBinders top catalog)

/-- The actual smart universe constructor completes in any fully covered cache. -/
theorem allTypes_complete [DecidableEq (EdgeKey String Guard)]
    (top : Guard) (catalog : List (String × Nat)) (environment : List (Value String Guard))
    (state : State String Guard) (valid : Valid state)
    (covered : InternedRecordCoherence.Covered [] state) :
    ∃ value final, InternedFreshOrdinaryConstruction.build (allTypes top catalog)
      environment state = .done value final := by
  exact InternedFreshOrdinaryFirstOrderCompletion.binder_complete true _
    (allTypesBody_binderFree top catalog) environment state valid covered

/-- The empty-cache run derives complete records, availability, and both histories. -/
theorem allTypes_closed_verified_complete [DecidableEq (EdgeKey String Guard)]
    (top : Guard) (catalog : List (String × Nat)) :
    ∃ value final, InternedFreshOrdinaryConstruction.build (allTypes top catalog)
      [] empty = .done value final ∧ Facts final ∧ Available final value ∧
      Grows empty final ∧
      Cache.Extends (empty (Symbol := String) (Guard := Guard)).nodes.issued final.nodes.issued := by
  exact InternedFreshOrdinaryFirstOrderCompletion.closed_verified_complete true _
    (allTypesBody_binderFree top catalog)

/-- Original library and query data determine a completed default universe run. -/
theorem typesOf_closed_verified_complete
    [DecidableEq (EdgeKey String SourceSynthesisGeneralizeSyntax.Guard)]
    (lib : Library) (query : Query) :
    ∃ value final,
      InternedFreshOrdinaryConstruction.build
        (SourceSynthesisFirstOrderConstruction.typesOf lib query) [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ Grows empty final ∧
      Cache.Extends
        (empty (Symbol := String) (Guard := SourceSynthesisGeneralizeSyntax.Guard)).nodes.issued
        final.nodes.issued := by
  exact allTypes_closed_verified_complete SourceSynthesisGeneralizeSyntax.top
    (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)

/-- A resident Mu determines its actual stored key, entry, and complete record. -/
theorem available_mu_key_readback (state : State String Guard) (facts : Facts state)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value String Guard)
    (available : Available state (.mu entry body depth ordinary)) :
    entry.key = muKey depth ordinary ∧
      state.nodes.table (muKey depth ordinary) = some entry ∧
      state.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) := by
  have resident := available.resident entry rfl
  obtain ⟨stored, present, fields⟩ := facts.coherent.nodes entry.key _ resident
  change entry = stored ∧ entry.key = muKey depth ordinary at fields
  rw [← fields.1] at present
  exact ⟨fields.2, fields.2 ▸ present, fields.2 ▸ resident⟩

end MicroCFTA.SourceSynthesisUniverseNativeInput
