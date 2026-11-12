import MicroCFTA.SourceSynthesisCurrentCallerInitialization
import MicroCFTA.SourceSynthesisCurrentRootTyping
import MicroCFTA.InternedGuardedExecution

/-!
# Ordinary typing of the actual current native root

One current initializer constructs the native root and the full cold caller.
Every accepted native term retains the same ordinary Program and goal type.
The result retains all initialization fields and the exact component count.
It does not establish query-use coverage or enumeration completion.
-/
namespace MicroCFTA.SourceSynthesisCurrentNativeTyping
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (guards Derived)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisPr210TypeReflection (candidateRigid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]

/-- One current initializer retains its full packet and types every same-root native term. -/
theorem accepted_typed (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) initial fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
        (SourceCurrentAllocatedPartialInitialization.caller width cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (SourceCurrentAllocatedPartialInitialization.caller width cache heap).checked.operations.constraints
          (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
        ∀ ambient term,
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term →
          ∃ program body,
            term = .node (literal "filter") [candidateRigid query.queryGoal, body] ∧
            Typed lib query program query.queryGoal ∧
            term.atPath [0] = some (candidateRigid query.queryGoal) ∧
            body.atPath [0] = some (candidateRigid query.queryGoal) ∧
            Projection literal Prod.fst term program ∧
            toProgram literal Prod.fst term = program ∧
            program.components = signed.toNat := by
  obtain ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context,
      facts, available, roles, growth, issued, origins, identity, emptySame, emptyReady, closed, original⟩ :=
    SourceSynthesisCurrentCallerInitialization.accepted lib query signed expression returned
      width initial valid formulas solver
  have mappedBuilt : InternedFreshOrdinaryConstruction.build (mapSyntax literal expression)
      [] empty = .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  refine ⟨fields, cache, value, heap, built, prepared, conjunctionFields, context, facts,
    available, roles, growth, issued, origins, identity, emptySame, emptyReady, closed, original, ?_⟩
  intro ambient term accepted
  have sourceAccepted : InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver)
      [] (mapSyntax literal expression) term := by
    rw [← InternedGuardedExecution.closed_language (mapSyntax literal expression) value heap mappedBuilt
      (SourceEqualityPCSGuard.holds formulas solver) ambient]
    exact accepted
  exact SourceSynthesisCurrentRootTyping.firstOrderRaw_typed formulas solver lib query signed expression
    returned term sourceAccepted

end MicroCFTA.SourceSynthesisCurrentNativeTyping
