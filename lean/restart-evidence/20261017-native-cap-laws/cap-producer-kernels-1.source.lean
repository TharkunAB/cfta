import MicroCFTA.SourceCurrentConstrainedCapNativeCompile
import MicroCFTA.SourceCurrentConstrainedCapNativeEdge

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.CapNativeProducerChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentHereditaryNativeScope (Bindings)
open SourceCurrentConstrainedCapNativeCode
variable {Symbol Guard : Type}

/-- Empty row compilation produces its own exact result without invoking either recursive callback. -/
theorem empty_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard) (depth : Nat)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard) :
    Certified annotation source (fun _ => True) (compileRows IntersectionEmptyDomain.emptyDomain [] []) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value) ∧
    interpret nodes edges (compileRows IntersectionEmptyDomain.emptyDomain [] []) state = .done .empty state ∧
    Available state.heap (.empty : Value Symbol Guard) ∧ Cap annotation depth (.empty : Value Symbol Guard) := by
  have bounded := SourceCurrentConstrainedCapNativeCompile.rows_certified annotation source (fun _ => True)
    depth IntersectionEmptyDomain.emptyDomain [] [] state valid trivial (SourceCurrentHereditaryNativeScope.empty annotation source)
    (by intro edge member; cases member) (by intro edge member; cases member)
  exact ⟨bounded, rfl, empty_available _, .plain depth .empty⟩

/-- Literal full-guard row and node work construct their own positive caps without a guard predicate. -/
theorem arbitrary_guard_constructors [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard) (symbol : Symbol) (guard : Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) :
    ∃ edge heap value after,
      run (makeEdge symbol guard []) state.heap = (edge, heap) ∧
      run (makeNode [edge]) heap = (value, after) ∧
      Certified annotation source (fun _ => True) (.work (makeEdge symbol guard []) .pure) state
        (fun final result => EdgeResident final.heap result ∧ Edge annotation 1 result) ∧
      Edge annotation 1 edge ∧ Available after value ∧ Cap annotation 1 value := by
  let built := run (makeEdge symbol guard []) state.heap
  let finished := run (makeNode [built.1]) built.2
  have edgePhysical := InternedNestedFacts.edge_verified symbol guard [] state.heap valid.1 (by intro value member; cases member)
  have edgeFacts : Facts built.2 := edgePhysical.facts
  have edgeResident : EdgeResident built.2 built.1 := edgePhysical.result _ _ rfl
  have edgeCap : Edge annotation 1 built.1 := SourceCurrentConstrainedCap.makeEdge annotation 1 symbol guard [] state.heap
    valid.1.coherent valid.1.cached (by intro value member; cases member) (by intro impossible; omega) (by intro value member; cases member)
  have resident : ∀ edge ∈ [built.1], EdgeResident built.2 edge := by
    intro edge member
    exact List.mem_singleton.mp member ▸ edgeResident
  have rows : ∀ edge ∈ [built.1], Edge annotation 1 edge := by
    intro edge member
    exact List.mem_singleton.mp member ▸ edgeCap
  have nodePhysical := InternedNestedFacts.node_verified [built.1] built.2 edgeFacts resident
  have certified := edge_work annotation source (fun _ => True) 1 symbol guard [] state valid
    (by intro value member; cases member) (by intro impossible; omega) (by intro value member; cases member)
  exact ⟨built.1, built.2, finished.1, finished.2, rfl, rfl, certified, edgeCap,
    nodePhysical.result _ _ rfl, SourceCurrentConstrainedCap.makeNode annotation 1 [built.1] built.2
      edgeFacts.coherent edgeFacts.linked resident rows⟩

/-- Entering capped operands produces the exact annotated source names read after legitimate growth. -/
theorem entered_source_reads (annotation : Guard → Prop) (depth : Nat) (source current : State Symbol Guard)
    (domain : DomainKey) (known : Bindings annotation source domain) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (cache : Cache.State DomainKey) (cacheValid : Cache.Valid cache) (first second : Nat)
    (facts : Facts current) (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued) :
    ∀ name ∈ SourceRecursiveIntersectionDomain.names
        (SourceRecursiveIntersectionEnvironment.enter cache domain left right first second).1.key,
      ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Available source value ∧
        Available current value ∧ value.referenceOf = .mu name ∧ Annotated annotation value := by
  have entered := SourceCurrentConstrainedCapNativeScope.enter annotation depth source domain known left right
    leftAvailable rightAvailable leftCap rightCap cache cacheValid first second
  intro name member
  exact SourceCurrentConstrainedCapNativeScope.read annotation source current facts growth history _ entered name member

end MicroCFTA.CapNativeProducerChecks

#print axioms MicroCFTA.CapNativeProducerChecks.empty_rows
#check @MicroCFTA.CapNativeProducerChecks.empty_rows
#print axioms MicroCFTA.CapNativeProducerChecks.arbitrary_guard_constructors
#check @MicroCFTA.CapNativeProducerChecks.arbitrary_guard_constructors
#print axioms MicroCFTA.CapNativeProducerChecks.entered_source_reads
#check @MicroCFTA.CapNativeProducerChecks.entered_source_reads
