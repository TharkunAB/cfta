import MicroCFTA.SourceEqualityOriginalAllocationHistory
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Checked original entry from one causal field-allocation history

Every literal constructor in the history supplies its normalized field.
Coverage transfers these checks to the actual original construction.
The same history derives existing field loads in its final interner.
Actual closed construction derives the physical and semantic initial state.
-/
namespace MicroCFTA.SourceEqualityOriginalAllocationHistory
open InternedConstructorTemplates InternedProbeProvenance
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Guard" => SourceSymbolicIndex.Constraint

mutual
private theorem syntax_valid_of_inventory (property : Guard Formula → Prop)
    (expression : InternedNestedConstruction.Syntax Symbol (Guard Formula))
    (checked : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, property guard) :
    InternedFreshOrdinaryConstraintHeap.SyntaxValid property expression := by
  cases expression with
  | empty | var => trivial
  | node edges => exact edges_valid_of_inventory property edges checked
  | union members => exact many_valid_of_inventory property members checked
  | binder smart body => exact syntax_valid_of_inventory property body checked
termination_by sizeOf expression

private theorem many_valid_of_inventory (property : Guard Formula → Prop)
    (expressions : List (InternedNestedConstruction.Syntax Symbol (Guard Formula)))
    (checked : ∀ guard ∈ SourceEqualityConstraintOrigins.childGuards expressions, property guard) :
    InternedFreshOrdinaryConstraintHeap.ManyValid property expressions := by
  cases expressions with
  | nil => trivial
  | cons first rest =>
      exact ⟨syntax_valid_of_inventory property first
          (fun guard member => checked guard (List.mem_append_left _ member)),
        many_valid_of_inventory property rest
          (fun guard member => checked guard (List.mem_append_right _ member))⟩
termination_by sizeOf expressions

private theorem edges_valid_of_inventory (property : Guard Formula → Prop)
    (expressions : List (InternedNestedConstruction.EdgeSyntax Symbol (Guard Formula)))
    (checked : ∀ guard ∈ SourceEqualityConstraintOrigins.edgeGuards expressions, property guard) :
    InternedFreshOrdinaryConstraintHeap.EdgesValid property expressions := by
  cases expressions with
  | nil => trivial
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          exact ⟨checked guard List.mem_cons_self,
            many_valid_of_inventory property children (fun other member => checked other
              (List.mem_cons_of_mem _ (List.mem_append_left _ member))),
            edges_valid_of_inventory property rest (fun other member => checked other
              (List.mem_cons_of_mem _ (List.mem_append_right _ member)))⟩
termination_by sizeOf expressions
end

/-- Every listed literal retains the normalization check from its actual constructor event. -/
theorem History.cached {initial final : Cache.State Key} {originals : List (Guard Formula)}
    (history : History initial final originals) :
    ∀ original ∈ originals, SourceEqualityGuardReadback.Cached original.equalities := by
  induction history with
  | start => intro original member; cases member
  | construct earlier cached done ih =>
      intro original member
      rcases List.mem_append.mp member with old | newest
      · exact ih original old
      · exact List.mem_singleton.mp newest ▸ cached
  | interleave earlier steps ih => exact ih

/-- Literal coverage derives all original syntax normalization checks from the one history. -/
theorem History.cached_inventory {initial final : Cache.State Key} {originals : List (Guard Formula)}
    (history : History initial final originals)
    (expression : InternedNestedConstruction.Syntax Symbol (Guard Formula))
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals) :
    ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities :=
  fun original member => history.cached original (covered original member)

/-- The original construction plan derives its normalized-field syntax predicate from history coverage. -/
theorem History.syntax_valid {initial final : Cache.State Key} {originals : List (Guard Formula)}
    (history : History initial final originals)
    (expression : InternedNestedConstruction.Syntax Symbol (Guard Formula))
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals) :
    InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard Formula => SourceEqualityGuardReadback.Cached guard.equalities) expression :=
  syntax_valid_of_inventory _ expression (history.cached_inventory expression covered)

/-- Actual original construction derives normalized and loaded fields in the history's final cache. -/
theorem History.fields {initial final : Cache.State Key} {originals : List (Guard Formula)}
    (history : History initial final originals) (valid : Cache.Valid initial)
    [DecidableEq (EdgeKey Symbol (Guard Formula))]
    (expression : InternedNestedConstruction.Syntax Symbol (Guard Formula))
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol (Guard Formula)) (heap : State Symbol (Guard Formula))
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial final) heap := by
  let normalized := fun guard : Guard Formula => SourceEqualityGuardReadback.Cached guard.equalities
  have fields : SourceEqualityAnnotationHeap.Heap normalized heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceEqualityAnnotationConstruction.build normalized expression
        (SourceEqualityConstraintOrigins.allowed normalized expression (history.cached_inventory expression covered))
        [] empty (SourceEqualityAnnotationHeap.empty_heap normalized)
  have origins := SourceEqualityOriginalFieldOrigins.constructed final expression
    (history.inventory valid expression covered) value heap built
  intro key edge present
  have cached := fields key edge present
  obtain ⟨loaded, found, _, _, _⟩ := SourceEqualityOriginalFieldOrigins.Origin.load
    key.constraint final cached (origins key edge present)
  exact ⟨cached, loaded, found⟩

end MicroCFTA.SourceEqualityOriginalAllocationHistory

namespace MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceEqualityOriginalAllocationHistory
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Checked" => SourceEqualityNativeDemand.State

/-- One covered causal allocation history and actual build derive every original checked-entry premise. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)] (width : Nat)
    {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    SourceCurrentAllocatedNativePhysicalCompletion.Good
      (⟨SourceRecursiveIntersectionThunks.initial width ⟨heap, Cache.emptyState⟩,
        SourceEqualityConstraintMemoAllocation.initial final⟩ : Checked width) ∧
      SourceEqualityRequiredSemanticCache.SemanticReady heap ∧ Available heap value ∧ value.free = [] ∧
      SourceRecursiveIntersectionInputView.Original value := by
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using checked.facts
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value heap built
  have available := checked.result value heap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built
  have physical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width)
    (⟨heap, Cache.emptyState⟩ : Machine Symbol Guard) ⟨facts, Cache.empty_valid⟩
  exact ⟨⟨physical, semantic.ready, history.operations_valid valid,
      history.fields valid expression covered value heap built⟩,
    semantic, available, closed,
    SourceRecursiveIntersectionOriginalOutput.closed_original value heap facts.coherent available closed⟩

end MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory
