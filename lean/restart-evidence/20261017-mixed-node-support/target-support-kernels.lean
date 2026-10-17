import MicroCFTA.SourceCurrentHereditaryTargetQuery
import MicroCFTA.SourceCurrentHereditaryConstruction

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.TargetSupportKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
local notation "Stored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Allowed raw construction creates its own value, causal Mu store, and source-universal fresh tables. -/
theorem constructed_tables (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed Plain expression)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    ∃ value heap,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      Annotated Plain value ∧
      Stored (⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩ : Checked width) ∧
      ∀ source, SourceCurrentHereditaryNativeCache.Stored Plain source (initial width ⟨heap, Cache.emptyState⟩) := by
  obtain ⟨value, heap, actual, constructors, annotated⟩ := SourceCurrentHereditaryConstruction.closed Plain expression allowed
  have stored := SourceCurrentHereditaryNativeUniversalStore.initial Plain (width := width)
    (⟨heap, Cache.emptyState⟩ : Machine Symbol Guard) operations constructors
  exact ⟨value, heap, actual, annotated, stored, stored.native⟩

set_option pp.explicit false in
set_option pp.proofs false in
/-- A fresh actual query publishes its result, then its literal warm repeat retains the full state. -/
theorem empty_publish_then_warm (bits : Nat) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good
      (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady machine.heap)
    (constructors : SourceCurrentHereditaryConstruction.MuStored Plain machine.heap) :
    let before : Checked (bits + 2) := ⟨initial (bits + 2) machine, operations⟩
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
    let middle : Checked (bits + 2) := {before with native := (demandNode 0 (lookupNode (bits + 2) request before.native).2).2}
    let after : Checked (bits + 2) := {middle with native := finishNode 0 .empty middle.native}
    SourceCurrentAllocatedTargetQuery.Step .empty .empty before .empty after ∧
      Stored after ∧ Annotated Plain (.empty : Value Symbol Guard) ∧
      after.native.nodes.cells 0 = some ⟨request, .returned .empty⟩ ∧
      SourceEqualityNativeDemand.execute 2 (.code (requestNode request.domain .empty .empty)) after = .done .empty after := by
  dsimp only
  let before : Checked (bits + 2) := ⟨initial (bits + 2) machine, operations⟩
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
  let middle : Checked (bits + 2) := {before with native := (demandNode 0 (lookupNode (bits + 2) request before.native).2).2}
  let after : Checked (bits + 2) := {middle with native := finishNode 0 .empty middle.native}
  have one : SourceEqualityNativeDemand.step (.code (requestNode request.domain .empty .empty)) before =
      .yielded (.code (.finishNode 0 .empty (.pure .empty))) middle := by rfl
  have owner : middle.native.nodes.cells 0 = some ⟨request, .evaluating⟩ := rfl
  have safe : SourceRecursiveIntersectionMemo.KeySafe (bits + 2) request.domain request.left request.right := by
    refine ⟨by omega, ?_, .empty, .empty, rfl, rfl, trivial, trivial⟩
    simp only [request, IntersectionEmptyDomain.emptyDomain]
    exact Nat.two_pow_pos _
  have inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
      (.code (requestNode request.domain .empty .empty)) before :=
    ⟨⟨empty_domain _, empty_available _, empty_available _⟩, fun _ _ => safe⟩
  have finishInputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
      (.code (.finishNode 0 .empty (.pure (.empty : Value Symbol Guard)))) middle :=
    ⟨request, owner, empty_available _⟩
  have two : SourceEqualityNativeDemand.step (.code (.finishNode 0 .empty (.pure (.empty : Value Symbol Guard)))) middle =
      .yielded (.code (.pure .empty)) after := rfl
  have trace := SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.cons _ _ _ _ _ _ _ inputs one
    (.cons _ _ _ _ _ _ _ finishInputs two (.refl _ _))
  have actual : SourceCurrentAllocatedTargetQuery.Step .empty .empty before .empty after := .run trace
  have stored := SourceCurrentHereditaryNativeUniversalStore.initial Plain (width := bits + 2) machine operations constructors
  have retained := SourceCurrentHereditaryTargetQuery.step actual good semantic
    (empty_available _) (empty_available _) rfl rfl stored .empty .empty
  have returned : after.native.nodes.cells 0 = some ⟨request, .returned .empty⟩ := by
    change (finishNode 0 .empty middle.native).nodes.cells 0 = some ⟨request, .returned .empty⟩
    simp only [finishNode, FlatMemoThunk.finish, owner, FlatMemoThunk.setStatus, Cache.put, ite_true]
  let key := IntersectionFlatMemoKeyDomain.flatKey (bits + 2) request.domain .empty .empty
  have encoded : SourceRecursiveIntersectionMemo.requestKey (bits + 2) request.domain request.left request.right = some key := rfl
  have table : after.native.nodes.table key = some 0 := by
    change Cache.put (fun _ => none) key 0 key = some 0
    simp only [Cache.put, ite_true]
  have selected : lookupNode (bits + 2) request after.native = (.memoized 0, after.native) := by
    simp only [lookupNode, request, encoded, FlatMemoThunk.lookup_hit key request after.native.nodes 0 table]
  have demanded : demandNode 0 after.native = (.ready .empty, after.native) := by
    simp only [demandNode, FlatMemoThunk.demand, returned]
  have warm : SourceEqualityNativeDemand.step (.code (requestNode request.domain .empty .empty)) after =
      .yielded (.code (.pure .empty)) after := by
    change SourceEqualityNativeDemand.step (.code (.node request .pure)) after = .yielded (.code (.pure .empty)) after
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
      SourceEqualityNativeDemand.lift]
  have done : SourceEqualityNativeDemand.execute 2 (.code (requestNode request.domain .empty .empty)) after =
      .done .empty after := by
    rw [SourceEqualityNativeDemand.execute, warm]
    rfl
  exact ⟨actual, retained.1, retained.2, returned, done⟩

#print axioms constructed_tables
#check @constructed_tables
#print axioms empty_publish_then_warm
#check @empty_publish_then_warm
end MicroCFTA.TargetSupportKernels
