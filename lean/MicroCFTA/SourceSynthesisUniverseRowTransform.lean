import MicroCFTA.SourceSynthesisUniverseRowProducts
import MicroCFTA.InternedStoredSubstitutionRebind
import MicroCFTA.InternedGuardedExecutionLists

/-!
# Source substitution readback for actual universe self rows

The existing source substitution defines the target child records.
Actual repeated-reference and marker-self branches return those records.
The final edge constructor retains its literal key and ordered children.
It retains every actual edge-cache effect. Arrow and catalog self rows
have no EmptyNode child after this transformation.
-/
namespace MicroCFTA.SourceSynthesisUniverseRowTransform
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedNestedFacts InternedProbeProvenance InternedEdgeResidency
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionKernel

variable {Symbol Guard : Type}

/-- Target children use the existing source substitution input map. -/
def children (uId : Nat) (source : EdgeValue Symbol Guard) : List (Value Symbol Guard) :=
  source.children.map
    (InternedStoredSubstitution.input
      (InternedStoredSubstitutionRebind.replacement (.interned uId) (repeatedValue (pair uId uId))))

/-- A result has the literal transformed children, source symbol, and top guard. -/
def Readback (top : Guard) (uId : Nat) (source result : EdgeValue Symbol Guard) : Prop :=
  result.children = children uId source ∧
    result.entry.key = ⟨source.entry.key.symbol, (children uId source).map Value.referenceOf, top⟩

/-- A catalog row substitutes the actual diagonal cutoff at each source position. -/
theorem catalog_children (uId arity : Nat) (source : EdgeValue Symbol Guard)
    (sourceChildren : source.children = List.replicate arity (.reference (.interned uId))) :
    children uId source = List.replicate arity (repeatedValue (pair uId uId)) := by
  simp [children, sourceChildren, InternedStoredSubstitution.input, InternedStoredSubstitutionRebind.replacement]

/-- An arrow row retains its original marker before the two actual cutoff records. -/
theorem arrow_children (uId : Nat) (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth : Nat) (source : EdgeValue Symbol Guard)
    (sourceChildren : source.children =
      [.node entry rows depth [], .reference (.interned uId), .reference (.interned uId)]) :
    children uId source = [.node entry rows depth [], repeatedValue (pair uId uId), repeatedValue (pair uId uId)] := by
  simp [children, sourceChildren, InternedStoredSubstitution.input, InternedStoredSubstitutionRebind.replacement]

/-- Actual edge-cache readback fixes both the transformed child records and the complete literal key. -/
theorem makeEdge_readback [DecidableEq (EdgeKey Symbol Guard)]
    (top : Guard) (uId : Nat) (source : EdgeValue Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : ∀ child ∈ children uId source, Available state child) :
    Readback top uId source (run (makeEdge source.entry.key.symbol top (children uId source)) state).1 := by
  have fields := InternedGuardedExecutionLists.makeEdge_fields source.entry.key.symbol top (children uId source)
    state facts.coherent facts.cached available
  exact ⟨fields.2, fields.1⟩

/-- The two actual self-row shapes contain no empty transformed child. -/
theorem children_live (uId : Nat) (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth : Nat) (source : EdgeValue Symbol Guard)
    (shape : source.children =
        [.node entry rows depth [], .reference (.interned uId), .reference (.interned uId)] ∨
      ∃ arity, source.children = List.replicate arity (.reference (.interned uId))) :
    (children uId source).any (fun child => child.referenceOf == .empty) = false := by
  rcases shape with arrow | ⟨arity, catalog⟩
  · rw [arrow_children uId entry rows depth source arrow]
    simp [Value.referenceOf, repeatedValue]
  · rw [catalog_children uId arity source catalog]
    simp [Value.referenceOf, repeatedValue]

/-- Actual self-row execution reaches exactly the transformed source edge request. -/
theorem edge_self_work [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard top : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (domain : Interned DomainKey) (uId : Nat) (entry : Interned NodeKey)
    (rows : List (EdgeValue Symbol Guard)) (depth : Nat) (source : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (sourceTop : source.entry.key.constraint = top)
    (seen : pair uId uId ∈ domain.key.seen)
    (shape : source.children =
        [.node entry rows depth [], .reference (.interned uId), .reference (.interned uId)] ∨
      ∃ arity, source.children = List.replicate arity (.reference (.interned uId))) :
    edge emptyGuard conjoin (execute emptyGuard conjoin 8 domain) source source state =
      SourceRecursiveIntersectionKernel.work (makeEdge source.entry.key.symbol top (children uId source)) state := by
  rcases shape with arrow | ⟨arity, catalog⟩
  · rw [SourceSynthesisUniverseRowProducts.edge_arrow emptyGuard conjoin 6 domain uId entry rows depth
      source source state arrow arrow seen]
    rw [sourceTop, conjoinTop, arrow_children uId entry rows depth source arrow]
  · rw [SourceSynthesisUniverseRowProducts.edge_catalog emptyGuard conjoin 7 domain uId arity
      source source state catalog catalog seen]
    rw [sourceTop, conjoinTop, catalog_children uId arity source catalog]

/-- Actual self-row completion retains its complete caches and literal live source-substitution readback. -/
theorem edge_self_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard top : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (domain : Interned DomainKey) (uId : Nat) (entry : Interned NodeKey)
    (rows : List (EdgeValue Symbol Guard)) (depth : Nat) (source : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (markerAvailable : Available state.heap (.node entry rows depth []))
    (sourceTop : source.entry.key.constraint = top) (seen : pair uId uId ∈ domain.key.seen)
    (shape : source.children =
        [.node entry rows depth [], .reference (.interned uId), .reference (.interned uId)] ∨
      ∃ arity, source.children = List.replicate arity (.reference (.interned uId))) :
    ∃ result after,
      edge emptyGuard conjoin (execute emptyGuard conjoin 8 domain) source source state = .done result after ∧
      SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ EdgeResident after.heap result ∧
      Readback top uId source result ∧ EqualityLeafProjectionPhysical.dead result = false := by
  have cutoffAvailable : Available state.heap (repeatedValue (pair uId uId)) := by
    apply reference_available
    intro name member
    simp [Value.free] at member
  have available : ∀ child ∈ children uId source, Available state.heap child := by
    rcases shape with arrow | ⟨arity, catalog⟩
    · rw [arrow_children uId entry rows depth source arrow]
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      rcases member with rfl | rfl
      · exact markerAvailable
      · exact cutoffAvailable
    · rw [catalog_children uId arity source catalog]
      intro child member
      rw [List.eq_of_mem_replicate member]
      exact cutoffAvailable
  let made := run (makeEdge source.entry.key.symbol top (children uId source)) state.heap
  let after : Machine Symbol Guard := {state with heap := made.2}
  have workDone : SourceRecursiveIntersectionKernel.work
      (makeEdge source.entry.key.symbol top (children uId source)) state = .done made.1 after := rfl
  have checked := work_checked state valid (makeEdge source.entry.key.symbol top (children uId source)) EdgeResident
    (InternedNestedFacts.edge_verified source.entry.key.symbol top (children uId source) state.heap valid.1 available)
  have readback := makeEdge_readback top uId source state.heap valid.1 available
  refine ⟨made.1, after,
    (edge_self_work emptyGuard top conjoin conjoinTop domain uId entry rows depth source state sourceTop seen shape).trans workDone,
    ?_, ?_, checked.result _ _ workDone, readback, ?_⟩
  · simpa only [workDone, Result.state] using checked.valid
  · simpa only [workDone, Result.state] using checked.extension
  · unfold EqualityLeafProjectionPhysical.dead
    rw [readback.1]
    exact children_live uId entry rows depth source shape

end MicroCFTA.SourceSynthesisUniverseRowTransform
