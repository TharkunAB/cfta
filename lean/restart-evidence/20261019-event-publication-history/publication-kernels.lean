import MicroCFTA.SourceCurrentRequiredPublicationHistory
import MicroCFTA.SourceCurrentNativeMuIssuedHistory
import MicroCFTA.SourceEqualityRequiredHead
import MicroCFTA.SourceEqualityPCSNativeEdge

/-!
# An actual nested used Mu read retains its publications

The source builds a used outer Mu with a used inner Mu. The inner source
captures the outer local name. Actual Head exposure rebuilds the inner Mu
with the outer Mu value. This adds a new completed Mu record.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.RequiredPublicationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityProjectionRead SourceEqualityRequiredHead
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "PublicationHistory" => SourceCurrentNativeMuPublication.History
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := ⟨some [],.top⟩
private def expression : Syntax Symbol Guard := .binder false (.node [.mk ("outer",.top) plain
  [.binder false (.node [.mk ("inner",.top) plain [.var 1,.var 0]])]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def mu : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def exposed := MergedFreshOrdinaryExposure.nodeEdges 8 mu heap
private def rows : List Row := match exposed with | .done values _ => values | _ => []
private def middle : Heap := match exposed with | .done _ state => state | _ => heap
private def rebuilt := run (makeNode rows) middle
private def result : Node := rebuilt.1
private def after : Heap := rebuilt.2
private def nested : Node := (children result)[0]?.getD .empty
private def nestedEntry := match nested with | .mu entry _ _ _ => entry | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def nestedBody : Node := match nested with | .mu _ body _ _ => body | _ => .empty
private def nestedDepth : Node := match nested with | .mu _ _ depth _ => depth | _ => .empty
private def nestedOrdinary : Node := match nested with | .mu _ _ _ ordinary => ordinary | _ => .empty
private theorem built_done : built = .done mu heap := by cbv
private theorem exposed_done : exposed = .done rows middle := by cbv
private theorem nested_shape : nested = .mu nestedEntry nestedBody nestedDepth nestedOrdinary := by cbv
private theorem selected : nested ∈ children result := by cbv; exact .head _
private theorem source_used : Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) := by cbv
private theorem nested_used : InternedFreshOrdinaryDepthHeap.usesLocal nestedDepth nestedOrdinary = true := by cbv
private theorem new_record : heap.nodeRecords nestedEntry.key = none ∧
    after.nodeRecords nestedEntry.key = some nested := by cbv
private theorem changed : heap ≠ after := by
  intro same
  have records := congrArg (fun state : Heap => state.nodeRecords nestedEntry.key) same
  rw [new_record.1,new_record.2] at records
  cases records
private theorem semantic : SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression mu heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem available : Available heap mu :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result mu heap built_done
private theorem head : Head mu heap result after := .read 8 rows middle exposed_done rfl
private theorem read : Read mu heap rows middle := .done 8 exposed_done
private theorem initial_history : Nonempty (PublicationHistory empty heap) :=
  ⟨SourceCurrentNativeMuPublication.closed_history expression⟩
private theorem initial_issued : Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty heap) :=
  ⟨SourceCurrentNativeMuIssuedHistory.closed_path expression⟩

private theorem checked_witness :
    built = .done mu heap ∧ SemanticReady heap ∧ Available heap mu ∧
    Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    Nonempty (PublicationHistory empty heap) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty heap) ∧
    exposed = .done rows middle ∧ Read mu heap rows middle ∧
    Head mu heap result after ∧ heap ≠ after ∧
    nested ∈ children result ∧ nested = .mu nestedEntry nestedBody nestedDepth nestedOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal nestedDepth nestedOrdinary = true ∧
    heap.nodeRecords nestedEntry.key = none ∧ after.nodeRecords nestedEntry.key = some nested ∧
    Nonempty (PublicationHistory heap middle) ∧ Nonempty (PublicationHistory heap after) ∧
    Nonempty (PublicationHistory empty after) ∧
    SourceCurrentNativeMuPublication.Written heap nestedEntry.key nested ∧
    SourceCurrentNativeMuPublication.Written empty nestedEntry.key nested := by
  obtain ⟨initial⟩ := initial_history
  obtain ⟨readHistory⟩ := SourceCurrentRequiredPublicationHistory.read read semantic costs available
  obtain ⟨headHistory⟩ := SourceCurrentRequiredPublicationHistory.head head semantic costs available
  have finalHistory : PublicationHistory empty after := .trans initial headHistory
  have present : after.nodeRecords nestedEntry.key = some (.mu nestedEntry nestedBody nestedDepth nestedOrdinary) := by
    rw [←nested_shape]
    exact new_record.2
  have localWriter : SourceCurrentNativeMuPublication.Written heap nestedEntry.key nested := by
    rcases headHistory.writers nestedEntry.key nestedEntry nestedBody nestedDepth nestedOrdinary present with old | writer
    · rw [new_record.1] at old
      cases old
    · simpa only [←nested_shape] using writer
  have globalWriter : SourceCurrentNativeMuPublication.Written empty nestedEntry.key nested := by
    simpa only [←nested_shape] using finalHistory.from_empty nestedEntry.key nestedEntry nestedBody nestedDepth nestedOrdinary present
  exact ⟨built_done,semantic,available,source_used.1,source_used.2,⟨initial⟩,initial_issued,exposed_done,read,
    head,changed,selected,nested_shape,nested_used,new_record.1,new_record.2,⟨readHistory⟩,⟨headHistory⟩,
    ⟨finalHistory⟩,localWriter,globalWriter⟩

/-- An actual nested Mu exposure derives its initial history and a new completed Mu writer. -/
theorem nested_publication :
    built = .done mu heap ∧ SemanticReady heap ∧ Available heap mu ∧
    Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    Nonempty (PublicationHistory empty heap) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty heap) ∧
    exposed = .done rows middle ∧ Read mu heap rows middle ∧
    Head mu heap result after ∧ heap ≠ after ∧
    nested ∈ children result ∧ nested = .mu nestedEntry nestedBody nestedDepth nestedOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal nestedDepth nestedOrdinary = true ∧
    heap.nodeRecords nestedEntry.key = none ∧ after.nodeRecords nestedEntry.key = some nested ∧
    Nonempty (PublicationHistory heap middle) ∧ Nonempty (PublicationHistory heap after) ∧
    Nonempty (PublicationHistory empty after) ∧
    SourceCurrentNativeMuPublication.Written heap nestedEntry.key nested ∧
    SourceCurrentNativeMuPublication.Written empty nestedEntry.key nested := checked_witness
end MicroCFTA.RequiredPublicationKernels
