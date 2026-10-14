import MicroCFTA.SourceRecursiveIntersectionUnionOrigins
import MicroCFTA.SourceRecursiveIntersectionExposedOrigins
import MicroCFTA.SourceRecursiveIntersectionNativeBranchReadback
import MicroCFTA.SourceRecursiveIntersectionNativePrefixCoverage

/-!
# Actual native union rows and successful child representatives

Checked native completion supplies allocation-free union calls in later
valid machines. Actual repaired row extraction then gives exact complete
row membership through successful member calls and their epsilon origins.
Source domains, full guards, and ordered physical children remain explicit.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedFreshOrdinaryGraph (Origin)

/-- Actual native completion and closed row extraction give exact origins in the valid final caller machine. -/
theorem native_exposed_origins [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (request : NodeRequest Symbol Guard)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (ready : NodeReady state.machine request)
    (semantic : SemanticHeap state.machine.heap) (covered : Covered [] state.machine.heap)
    (done : execute emptyGuard conjoin fuel (.node request .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node request .pure) state) (closed : value.free = [])
    (readFuel : Nat) (edges : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (read : MergedFreshOrdinaryExposure.nodeEdges readFuel value after.machine.heap = .done edges final) :
    let view : Machine Symbol Guard := {after.machine with heap := final}
    SourceRecursiveIntersectionKernel.Valid view ∧ Extension after.machine view ∧ SemanticHeap view.heap ∧
      ∀ edge, edge ∈ edges ↔ Origin view.heap [value] edge := by
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  have bounds := evaluated.bounds_of_ranges ranges
  obtain ⟨afterValid, _, available, _⟩ := native_node_correct emptyGuard conjoin fuel request state after value valid ready done bounds
  have retained := bounds.semantic_heap (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode request.domain request.left request.right state.machine ready) valid
    (semantic_requestNode request.domain request.left request.right state.machine ready) semantic
  obtain ⟨steps, _, nativeTrace⟩ := done_trace emptyGuard conjoin fuel _ state after value done
  have afterCovered := (nativeTrace.covered emptyGuard conjoin steps _ _ state after semantic.1.normal.facts.coherent.valid covered).2
  exact exposed_origins readFuel after.machine afterValid.machine retained afterCovered value available closed edges final read

/-- Native left-union origins come exactly from successful ordered left-member calls in any later normalized machine. -/
theorem native_left_union_origins [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (other : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine ⟨domain, .union entry members depth free, other⟩)
    (selected : SourceRecursiveIntersectionControl.decision domain.key (.union entry members depth free) other = .leftUnion)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, .union entry members depth free, other⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, .union entry members depth free, other⟩ .pure) state) :
    ∃ bound, ∀ extra view, SourceRecursiveIntersectionKernel.Valid view → InternedLiveEdges.Live view.heap →
      Extension after.machine view → ∀ edge, Origin view.heap [value] edge ↔ ∃ member ∈ members, ∃ result,
        SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) domain member other view = .done result view ∧
          Origin view.heap [result] edge := by
  obtain ⟨_, earlier, bound, completed⟩ := native_node_branch_replay emptyGuard conjoin fuel _ state after value valid ready done ranges
  refine ⟨bound, ?_⟩
  intro extra view viewValid live growth edge
  have fullGrowth := earlier.trans growth
  have source := fullGrowth.available (.union entry members depth free) ready.2.1
  have returned := completed extra view growth
  simp only [onNode, selected] at returned
  exact union_call_origins _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
    domain members other true view view viewValid viewValid live (ready.1.grows domain fullGrowth)
    (fullGrowth.available other ready.2.2) (fun member present => source.children member (by simpa only [children] using present))
    value view returned (.refl _) view.heap edge

/-- Native right-union origins retain the original right-member operand order in every later normalized machine. -/
theorem native_right_union_origins [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (other : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine ⟨domain, other, .union entry members depth free⟩)
    (selected : SourceRecursiveIntersectionControl.decision domain.key other (.union entry members depth free) = .rightUnion)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, other, .union entry members depth free⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, other, .union entry members depth free⟩ .pure) state) :
    ∃ bound, ∀ extra view, SourceRecursiveIntersectionKernel.Valid view → InternedLiveEdges.Live view.heap →
      Extension after.machine view → ∀ edge, Origin view.heap [value] edge ↔ ∃ member ∈ members, ∃ result,
        SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) domain other member view = .done result view ∧
          Origin view.heap [result] edge := by
  obtain ⟨_, earlier, bound, completed⟩ := native_node_branch_replay emptyGuard conjoin fuel _ state after value valid ready done ranges
  refine ⟨bound, ?_⟩
  intro extra view viewValid live growth edge
  have fullGrowth := earlier.trans growth
  have source := fullGrowth.available (.union entry members depth free) ready.2.2
  have returned := completed extra view growth
  simp only [onNode, selected] at returned
  exact union_call_origins _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
    domain members other false view view viewValid viewValid live (ready.1.grows domain fullGrowth)
    (fullGrowth.available other ready.2.1) (fun member present => source.children member (by simpa only [children] using present))
    value view returned (.refl _) view.heap edge

/-- Actual exposed rows of a checked left-union result have exactly their successful final-cache child origins. -/
theorem native_left_union_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (other : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine ⟨domain, .union entry members depth free, other⟩)
    (selected : SourceRecursiveIntersectionControl.decision domain.key (.union entry members depth free) other = .leftUnion)
    (semantic : SemanticHeap state.machine.heap) (covered : Covered [] state.machine.heap)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, .union entry members depth free, other⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, .union entry members depth free, other⟩ .pure) state)
    (closed : value.free = []) (readFuel : Nat) (edges : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (read : MergedFreshOrdinaryExposure.nodeEdges readFuel value after.machine.heap = .done edges final) :
    ∃ bound, ∀ extra edge,
      let view : Machine Symbol Guard := {after.machine with heap := final}
      edge ∈ edges ↔ ∃ member ∈ members, ∃ result,
        SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) domain member other view = .done result view ∧
          Origin final [result] edge := by
  have exposed := native_exposed_origins emptyGuard conjoin fuel _ state after value valid ready semantic covered done ranges closed readFuel edges final read
  obtain ⟨bound, origins⟩ := native_left_union_origins emptyGuard conjoin fuel domain entry members depth free other state after value valid ready selected done ranges
  refine ⟨bound, ?_⟩
  intro extra edge
  exact (exposed.2.2.2 edge).trans (origins extra _ exposed.1 exposed.2.2.1.1.normal.live exposed.2.1 edge)

/-- Actual exposed rows of a checked right-union result retain exact right-member calls in the final cache. -/
theorem native_right_union_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (other : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine ⟨domain, other, .union entry members depth free⟩)
    (selected : SourceRecursiveIntersectionControl.decision domain.key other (.union entry members depth free) = .rightUnion)
    (semantic : SemanticHeap state.machine.heap) (covered : Covered [] state.machine.heap)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, other, .union entry members depth free⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, other, .union entry members depth free⟩ .pure) state)
    (closed : value.free = []) (readFuel : Nat) (edges : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (read : MergedFreshOrdinaryExposure.nodeEdges readFuel value after.machine.heap = .done edges final) :
    ∃ bound, ∀ extra edge,
      let view : Machine Symbol Guard := {after.machine with heap := final}
      edge ∈ edges ↔ ∃ member ∈ members, ∃ result,
        SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) domain other member view = .done result view ∧
          Origin final [result] edge := by
  have exposed := native_exposed_origins emptyGuard conjoin fuel _ state after value valid ready semantic covered done ranges closed readFuel edges final read
  obtain ⟨bound, origins⟩ := native_right_union_origins emptyGuard conjoin fuel domain entry members depth free other state after value valid ready selected done ranges
  refine ⟨bound, ?_⟩
  intro extra edge
  exact (exposed.2.2.2 edge).trans (origins extra _ exposed.1 exposed.2.2.1.1.normal.live exposed.2.1 edge)

end MicroCFTA.SourceRecursiveIntersectionNative
