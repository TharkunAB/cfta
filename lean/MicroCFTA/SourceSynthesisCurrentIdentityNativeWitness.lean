import MicroCFTA.SourceSynthesisCurrentTypeFieldCalls
import MicroCFTA.SourceSynthesisGeneralizeFiniteInstances

/-!
# A finite guarded instance at an actual component call

The recorded child call supplies the same native identity Type value.
The theorem retains a finite instance and its equality guard in that value.
Later reads and joint completion require separate proofs.
-/

namespace MicroCFTA.SourceSynthesisCurrentIdentityNativeWitness
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual identity component retains its finite guarded arrow instance. -/
theorem identity_component_native_member
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    {expressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
    {outputs : List (EdgeValue Symbol Guard)} {rowIndex : Nat} {symbol : Symbol}
    (original : SourceSynthesisOriginalTypeAnnotations.OriginalType lib
      (.tFun (.tVar "a") (.tVar "a")))
    (call : SourceCurrentStoredMuRetainedAlignment.RowCall
      expressions [] before outputs after heap rowIndex symbol top
      [ordinarySymbols (generalize
        (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query))
        (SourceSynthesisPr210TypeReflection.encodeTy (.tFun (.tVar "a") (.tVar "a"))))]) :
    ∃ value, call.output.children[0]? = some value ∧ Available heap value ∧
      value.free = [] ∧
      SourceEqualityAnnotationLanguage.Annotated
        (SourceSynthesisNativeTypeTrace.Origin
          (SourceSynthesisCurrentSourceGuards.encodedLibrary lib)) value ∧
      ∀ ambient : InternedGuardedLanguage.Env Symbol,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient value
          (.node (literal "->")
            [.node (literal "(->)") [], .node (literal "var1") [], .node (literal "var1") []]) := by
  let field : Expression := generalize
    (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query))
    (SourceSynthesisPr210TypeReflection.encodeTy (.tFun (.tVar "a") (.tVar "a")))
  obtain ⟨value, selected, available, closed, annotated⟩ :=
    SourceSynthesisCurrentTypeFieldCalls.component_call lib query signed whole accepted
      rootValue heap built (.tFun (.tVar "a") (.tVar "a")) original call
  obtain ⟨native, start, finish, nativeSlot, context, actual, growth, _finishGrowth⟩ :=
    SourceSynthesisOriginalProgramTypeFields.many_call [ordinarySymbols field]
      call.current call.middle heap call.context call.values call.called
      call.middle_growth 0 (ordinarySymbols field) rfl
  have slot : call.values[0]? = some value := by
    rw [← call.children_eq]
    exact selected
  have same : native = value := Option.some.inj (nativeSlot.symm.trans slot)
  subst native
  have globalHeap : InternedGuardedProbeHeap.Heap heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      InternedGuardedExecution.closed_heap (ordinarySymbols whole)
  have prefixHeap : InternedGuardedProbeHeap.Heap start := by
    intro key entry body depth ordinary present
    exact globalHeap key entry body depth ordinary (growth.nodeRecords key _ present)
  have finite : InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal field)
      (.node (literal "->")
        [.node (literal "(->)") [], .node (literal "var1") [], .node (literal "var1") []]) := by
    simpa only [field, SourceSynthesisPr210TypeReflection.encodeTy,
      SourceSynthesisGeneralizeFiniteInstances.instantiate_fun,
      SourceSynthesisGeneralizeFiniteInstances.instantiate] using
      SourceSynthesisGeneralizeFiniteInstances.generalize_member formulas solver
      (SourceSynthesisCurrentContext.constructorCatalog lib query)
      (SourceSynthesisPr210TypeReflection.encodeTy (.tFun (.tVar "a") (.tVar "a")))
      (fun _ => .node (literal "var1") []) (by
        intro _ _
        exact SourceSynthesisTypeUniverseMembership.variable_member literal
          (SourceEqualityPCSGuard.holds formulas solver)
          (SourceEqualityPCSConstructors.top_true formulas solver)
          (SourceSynthesisCurrentContext.constructorCatalog lib query) "var1" (by decide))
  refine ⟨value, selected, available, closed, annotated, ?_⟩
  intro ambient
  have language := (InternedGuardedExecution.build_language (ordinarySymbols field) []
    start context prefixHeap).result value finish actual
      (SourceEqualityPCSGuard.holds formulas solver) ambient
  rw [language]
  change InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
    (ordinarySymbols field) _
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using finite

end MicroCFTA.SourceSynthesisCurrentIdentityNativeWitness
