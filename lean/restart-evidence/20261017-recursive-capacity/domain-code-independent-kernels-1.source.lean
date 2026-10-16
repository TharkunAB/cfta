import MicroCFTA.SourceCurrentAllocatedRecursiveDomainCode

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.RecursiveDomainCodeIndependentChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedRecursiveDomainCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Two actual original Mu records derive their compiler certificate and exact new-domain membership. -/
theorem original_mu_compiler [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (first second : Interned NodeKey) (leftBody leftDepth leftOrdinary rightBody rightDepth rightOrdinary : Value Symbol Guard)
    (leftOriginal : Original leftBody) (rightOriginal : Original rightBody)
    (leftAvailable : Available source (.mu first leftBody leftDepth leftOrdinary))
    (rightAvailable : Available source (.mu second rightBody rightDepth rightOrdinary)) :
    let left : Value Symbol Guard := .mu first leftBody leftDepth leftOrdinary
    let right : Value Symbol Guard := .mu second rightBody rightDepth rightOrdinary
    let inventory := SourceRecursiveIntersectionSourceInventory.domains source
    Certified source inventory (compileMu IntersectionEmptyDomain.emptyDomain left right)
      ⟨source, Cache.emptyState⟩ (fun after value => Available after.heap value) ∧
      SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
        (SourceRecursiveIntersectionControl.pair first.identity second.identity) ∈ inventory := by
  dsimp only
  have scope := initial_scope source (.mu first leftBody leftDepth leftOrdinary) (.mu second rightBody rightDepth rightOrdinary)
    (.mu first leftBody leftDepth leftOrdinary leftOriginal) (.mu second rightBody rightDepth rightOrdinary rightOriginal)
    leftAvailable rightAvailable
  have valid : SourceRecursiveIntersectionKernel.Valid (⟨source, Cache.emptyState⟩ : Machine Symbol Guard) :=
    ⟨facts, Cache.empty_valid⟩
  have ready : NodeReady (⟨source, Cache.emptyState⟩ : Machine Symbol Guard)
      ⟨IntersectionEmptyDomain.emptyDomain, .mu first leftBody leftDepth leftOrdinary,
        .mu second rightBody rightDepth rightOrdinary⟩ :=
    ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have certificate := mu_certified source (SourceRecursiveIntersectionSourceInventory.domains source)
    (source_closed source facts) _ scope (SourceRecursiveIntersectionSourceInventory.empty_mem source) _ valid ready
  refine ⟨certificate, ?_⟩
  exact enter_member source (SourceRecursiveIntersectionSourceInventory.domains source)
    IntersectionEmptyDomain.emptyDomain (.mu first leftBody leftDepth leftOrdinary)
    (.mu second rightBody rightDepth rightOrdinary) first.identity second.identity _ _ _ certificate

/-- An actual current checked yield certifies its exact emitted code, with no Symbol equality or word premise. -/
theorem actual_checked_body [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (member : request.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains source)
    (before after : SourceEqualityNativeDemand.State width) (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    after.native = before.native ∧
      Certified source (SourceRecursiveIntersectionSourceInventory.domains source) code after.native.machine
        (fun final value => InternedEdgeResidency.EdgeResident final.heap value) := by
  constructor
  · simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request .pure before
  · exact body_certified source (SourceRecursiveIntersectionSourceInventory.domains source)
      facts request scope member before after code valid semantic ready yielded

#print axioms original_mu_compiler
#check @original_mu_compiler
#print axioms actual_checked_body
#check @actual_checked_body
end MicroCFTA.RecursiveDomainCodeIndependentChecks
