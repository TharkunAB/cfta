import MicroCFTA.SourceSynthesisCurrentSourceGuards
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

/-!
# Current native construction with complete guard origins

The constructor uses one actual current source expression and one native build.
Every physical edge guard retains its input-derived origin.
This does not supply Type fields, a model, or whole enumeration completion.
-/
namespace MicroCFTA.SourceSynthesisCurrentNativeGuardOrigins
open InternedConstructorTemplates
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceEqualityConstraintOrigins (Derived)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)

/-- Every physical edge in the actual current build has an input-derived guard. -/
theorem constructed {Symbol : Type} (literal : String → Symbol)
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (mapSyntax literal expression) [] empty = .done value heap) :
    SourceEqualityAnnotationHeap.Heap
      (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap := by
  have allowed := SourceEqualityConstraintOrigins.allowed
    (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin)
    (mapSyntax literal expression)
    (fun guard member => Derived.literal
      (SourceSynthesisCurrentSourceGuards.mapped_guards
        literal lib query signed expression accepted guard member))
  simpa only [built, InternedNestedConstruction.Outcome.state] using SourceEqualityAnnotationConstruction.build
    (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin)
    (mapSyntax literal expression) allowed [] empty
    (SourceEqualityAnnotationHeap.empty_heap _)

/-- A nonnegative current request produces one build and its whole physical guard invariant. -/
theorem complete {Symbol : Type} (literal : String → Symbol)
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (nonnegative : 0 ≤ signed) :
    ∃ (expression : Expression) (value : Value Symbol Guard) (heap : State Symbol Guard),
      SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression ∧
      InternedFreshOrdinaryConstruction.build
        (mapSyntax literal expression) [] empty = .done value heap ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap := by
  obtain ⟨expression, accepted⟩ :=
    SourceSynthesisCurrentConstruction.firstOrderRaw_total lib query signed nonnegative
  obtain ⟨value, heap, built⟩ :=
    InternedFreshOrdinaryClosedCompletion.closed_complete (mapSyntax literal expression)
  exact ⟨expression, value, heap, accepted, built,
    constructed literal lib query signed expression accepted value heap built⟩

end MicroCFTA.SourceSynthesisCurrentNativeGuardOrigins
