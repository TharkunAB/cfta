import MicroCFTA.SourceCurrentAllocatedNativeOpenBodyQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeOpenProductReclosure

/-!
# Identity-coherent products and cached source reclosure

The finite row witness retains complete values at equal identities.
Canonical node availability then supplies every witness row's residency.
The original source probes reclose that cached product to the full stored U.
The existing weak product predicate remains unchanged.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCoherentOpenBodyResult
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (pair repeatedValue)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "Checked" => SourceEqualityNativeDemand.State

set_option autoImplicit false

/-- Equal identities select one complete row inside this finite witness list. -/
def IdentityFunctional (products : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ a ∈ products, ∀ b ∈ products, a.entry.identity = b.entry.identity → a = b

/-- The original ordered row product also retains identity coherence of its witnesses. -/
def ProductShape [DecidableEq Symbol] (sourceName cutoffLeft cutoffRight : Nat) (body value : Value Symbol Guard) : Prop :=
  ∃ (productEntry : Interned NodeKey) (products : List (EdgeValue Symbol Guard)),
    All₂ (fun (source : EdgeValue Symbol Guard) target =>
      target.children = source.children.map (input (replacement (.interned sourceName)
        (repeatedValue (pair cutoffLeft cutoffRight)))) ∧
      target.entry.key = ⟨source.entry.key.symbol,
        (source.children.map (input (replacement (.interned sourceName)
          (repeatedValue (pair cutoffLeft cutoffRight))))).map Value.referenceOf, top⟩)
      (nodeEdges body) products ∧ IdentityFunctional products ∧
    value = .node productEntry (canonicalEdges products) 0
      [.intersection (pair cutoffLeft cutoffRight).1 (pair cutoffLeft cutoffRight).2]

/-- The coherent result retains the complete existing weak product shape. -/
theorem to_product_shape [DecidableEq Symbol]
    (sourceName cutoffLeft cutoffRight : Nat) (body value : Value Symbol Guard)
    (shape : ProductShape sourceName cutoffLeft cutoffRight body value) :
    SourceCurrentAllocatedNativeOpenBodyQueryGlobalLaws.ProductShape sourceName cutoffLeft cutoffRight body value := by
  obtain ⟨productEntry, products, aligned, _functional, read⟩ := shape
  exact ⟨productEntry, products, aligned, read⟩

/-- Actual resident rows give a finite identity-functional witness. -/
theorem identity_functional_of_resident
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (products : List (EdgeValue Symbol Guard))
    (resident : ∀ row ∈ products, EdgeResident heap row) : IdentityFunctional products := by
  intro a aMember b bMember same
  exact edge_identity_unique heap facts.coherent a b (resident a aMember) (resident b bMember) same

/-- Canonicalization retains every complete row in an identity-functional witness. -/
theorem canonical_edges_retains
    (products : List (EdgeValue Symbol Guard)) (functional : IdentityFunctional products)
    (row : EdgeValue Symbol Guard) (member : row ∈ products) : row ∈ canonicalEdges products := by
  have idMember : row.entry.identity ∈ (canonicalEdges products).map (fun edge => edge.entry.identity) := by
    rw [canonicalEdges_ids]
    exact (EnumerationBuilderCaches.canonicalIds_member _ _).mpr (List.mem_map.mpr ⟨row, member, rfl⟩)
  obtain ⟨selected, selectedMember, sameIdentity⟩ := List.mem_map.mp idMember
  have same : selected = row := functional selected
    (canonicalEdges_member products selected selectedMember) row member sameIdentity
  exact same ▸ selectedMember

/-- An available canonical node supplies every identity-functional witness row's residency. -/
theorem product_rows_resident
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (productEntry : Interned NodeKey) (products : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List Reference) (functional : IdentityFunctional products)
    (available : Available heap (.node productEntry (canonicalEdges products) depth free)) :
    ∀ row ∈ products, EdgeResident heap row := by
  have canonicalResident := resident_edges heap facts.linked
    (.node productEntry (canonicalEdges products) depth free) available.resident
  intro row member
  apply canonicalResident row
  change row ∈ canonicalEdges products
  exact canonical_edges_retains products functional row member

/-- A cached coherent source product recloses to the full original stored U at the same state. -/
theorem stored_open_product_optional_reclosure
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (state : Checked width) (facts : Facts state.native.machine.heap)
    (growth : Grows sourceHeap state.native.machine.heap)
    (cutoffLeft cutoffRight : Nat) (product : Value Symbol Guard)
    (available : Available state.native.machine.heap product)
    (shape : ProductShape entry.identity cutoffLeft cutoffRight body product) :
    SourceRecursiveIntersectionMaybeMu.maybeMu (pair cutoffLeft cutoffRight) product state.native.machine.heap =
      .done (.mu entry body depth ordinary) state.native.machine.heap ∧
    SourceEqualityNativeDemand.step (.code (.optionalBinder (pair cutoffLeft cutoffRight) product .pure)) state =
      .yielded (.code (.pure (.mu entry body depth ordinary))) state ∧
    SourceEqualityNativeDemand.execute 2 (.code (.optionalBinder (pair cutoffLeft cutoffRight) product .pure)) state =
      .done (.mu entry body depth ordinary) state := by
  obtain ⟨productEntry, products, aligned, functional, read⟩ := shape
  have nodeAvailable : Available state.native.machine.heap
      (.node productEntry (canonicalEdges products) 0
        [.intersection (pair cutoffLeft cutoffRight).1 (pair cutoffLeft cutoffRight).2]) := by
    rw [← read]
    exact available
  have resident := product_rows_resident state.native.machine.heap facts productEntry products 0
    [.intersection (pair cutoffLeft cutoffRight).1 (pair cutoffLeft cutoffRight).2] functional nodeAvailable
  exact SourceCurrentAllocatedNativeOpenProductReclosure.stored_open_product_optional_reclosure
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    state facts growth (pair cutoffLeft cutoffRight) product productEntry products read available aligned resident

end MicroCFTA.SourceCurrentAllocatedNativeCoherentOpenBodyResult
