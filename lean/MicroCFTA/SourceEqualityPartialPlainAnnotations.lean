import MicroCFTA.SourceEqualityPartialPlainCompletion

/-!
# Original equality-free annotations derive the finite caller region

The actual source guard accessor defines equality freedom. Physical cache
annotations and closed availability derive the structural region. Original
source construction supplies that cache from its literal annotation checks.
No completed outer graph or language law is an input premise.
-/
namespace MicroCFTA.SourceEqualityPartialPlainAnnotations
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceObservations SourceSymbolicIndex
open SourceEqualityPartialPlainRegion SourceEqualityAnnotationLanguage
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- The actual source equality accessor returns the empty constraint set. -/
def NoEqualities (guard : Guard) : Prop := SourceCompactGuards.sourceEqualities guard = some []

/-- Empty source equality readback builds the exact empty physical payload. -/
theorem physical {guard : Guard} (plain : NoEqualities guard) :
    SourceEqualityPhysicalPayload.own guard = .ok (some []) := by
  rw [SourceEqualityPhysicalPayload.own, plain]
  rfl

/-- Pointwise structural regions give the exact ordered child-region predicate. -/
theorem children {values : List (Value Symbol Guard)} (plain : ∀ value ∈ values, Region value) : Children values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (plain _ List.mem_cons_self) (ih (fun child member => plain child (List.mem_cons_of_mem _ member)))

/-- Literal empty guards and pointwise child regions retain every original ordered edge. -/
theorem rows {edges : List (EdgeValue Symbol Guard)}
    (guards : ∀ edge ∈ edges, NoEqualities edge.entry.key.constraint)
    (plain : ∀ value ∈ edges.flatMap EdgeValue.children, Region value) : Rows edges := by
  induction edges with
  | nil => exact .nil
  | cons edge edges ih =>
      exact .cons (physical (guards _ List.mem_cons_self))
        (children (fun value member => plain value (List.mem_flatMap.mpr ⟨edge, List.mem_cons_self, member⟩)))
        (ih (fun edge member => guards edge (List.mem_cons_of_mem _ member))
          (fun value member => plain value (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr member)))

/-- Closed available annotated records derive their actual finite structural region above opaque branches. -/
theorem annotated (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (annotations : Annotated NoEqualities value) (available : Available state value) (closed : value.free = []) : Region value := by
  induction annotations with
  | empty => exact .empty
  | reference name => simp only [Value.free] at closed; cases closed
  | node entry edges depth free guards allChildren ih =>
      have childClosed := MergedColdReaderClosed.node_children_closed state facts entry edges depth free available closed
      apply Region.ordinary
      apply rows guards
      intro child member
      obtain ⟨edge, edgeMember, childMember⟩ := List.mem_flatMap.mp member
      exact ih child (List.mem_flatMap.mpr ⟨edge, edgeMember, childMember⟩)
        (available.children child (List.mem_flatMap.mpr ⟨edge, edgeMember, childMember⟩)) (childClosed edge edgeMember child childMember)
  | union => exact .union
  | mu => exact .binder

/-- The actual original closed construction derives equality-free regions from its literal source guards. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed NoEqualities expression) (value : Value Symbol Guard) (state : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) : Region value := by
  have ready := SourceEqualityRequiredCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  have heap : SourceEqualityAnnotationHeap.Heap NoEqualities state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceEqualityAnnotationConstruction.build NoEqualities expression allowed [] empty (SourceEqualityAnnotationHeap.empty_heap NoEqualities)
  have annotated := SourceEqualityAnnotationHeap.available NoEqualities state heap ready.semantic.1.normal.facts.linked value available
  exact SourceEqualityPartialPlainAnnotations.annotated state ready.semantic.1.normal.facts value annotated available closed

end MicroCFTA.SourceEqualityPartialPlainAnnotations
