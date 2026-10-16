import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache

/-!
# Contextual reuse from physical native cells

Physical validity identifies the original request at an actual memo hit.
The separate contextual invariant supplies that request's completed law.
A finish stores a law proved for its literal evaluating request. These
lemmas do not derive that local law or assume a completed body receipt.
They do not model GHC thunk publication or runtime key capacity.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextualPhysicalCache
open Language BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedEdgeResidency SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}
variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)

/-- Empty native tables satisfy both invariants without a completed answer. -/
theorem initial_valid (machine : Machine Symbol Guard)
    (physical : SourceRecursiveIntersectionKernel.Valid machine) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (initial width machine) ∧ Contextual view model ranked holds (initial width machine) :=
  ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine physical, initial_contextual view model ranked holds width machine⟩

/-- Actual machine growth retains physical records and the fixed contextual laws. -/
theorem advance (state : Native width Symbol Guard) (after : Machine Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (contextual : Contextual view model ranked holds state)
    (checked : SourceRecursiveIntersectionKernel.Valid after) (growth : Extension state.machine after) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (SourceRecursiveIntersectionThunks.advance state after) ∧
      Contextual view model ranked holds (SourceRecursiveIntersectionThunks.advance state after) :=
  ⟨SourceCurrentAllocatedNativePhysicalCache.advance_valid state physical after checked growth,
    advance_contextual view model ranked holds state after contextual⟩

/-- Checked node publication retains both independent invariants. -/
theorem lookupNode (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (contextual : Contextual view model ranked holds state)
    (ready : NodeReady state.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (SourceRecursiveIntersectionThunks.lookupNode width request state).2 ∧
      Contextual view model ranked holds (SourceRecursiveIntersectionThunks.lookupNode width request state).2 :=
  ⟨SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid state physical request ready safe,
    lookupNode_contextual view model ranked holds state request contextual⟩

/-- Checked edge publication retains both independent invariants. -/
theorem lookupEdge (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (contextual : Contextual view model ranked holds state)
    (ready : EdgeReady state.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (SourceRecursiveIntersectionThunks.lookupEdge width request state).2 ∧
      Contextual view model ranked holds (SourceRecursiveIntersectionThunks.lookupEdge width request state).2 :=
  ⟨SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid state physical request ready safe,
    lookupEdge_contextual view model ranked holds state request contextual⟩

/-- Node demand retains existing completed laws in every phase. -/
theorem demandNode (state : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (contextual : Contextual view model ranked holds state) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (SourceRecursiveIntersectionThunks.demandNode handle state).2 ∧
      Contextual view model ranked holds (SourceRecursiveIntersectionThunks.demandNode handle state).2 :=
  ⟨SourceCurrentAllocatedNativePhysicalCache.demandNode_valid state physical handle,
    demandNode_contextual view model ranked holds state handle contextual⟩

/-- Edge demand retains existing completed laws in every phase. -/
theorem demandEdge (state : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (contextual : Contextual view model ranked holds state) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (SourceRecursiveIntersectionThunks.demandEdge handle state).2 ∧
      Contextual view model ranked holds (SourceRecursiveIntersectionThunks.demandEdge handle state).2 :=
  ⟨SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid state physical handle,
    demandEdge_contextual view model ranked holds state handle contextual⟩

/-- A node finish stores only the law for its actual evaluating original. -/
theorem finishNode (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (contextual : Contextual view model ranked holds state)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.machine.heap result)
    (localLaw : NodeLaw view model ranked holds request result) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (SourceRecursiveIntersectionThunks.finishNode handle result state) ∧
      Contextual view model ranked holds (SourceRecursiveIntersectionThunks.finishNode handle result state) :=
  ⟨SourceCurrentAllocatedNativePhysicalCache.finishNode_valid state physical handle request result running available,
    finishNode_contextual view model ranked holds state handle request result contextual running localLaw⟩

/-- An edge finish stores only the law for its actual evaluating original. -/
theorem finishEdge (state : Native width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (contextual : Contextual view model ranked holds state)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (resident : EdgeResident state.machine.heap result)
    (localLaw : EdgeLaw view model ranked holds request result) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (SourceRecursiveIntersectionThunks.finishEdge handle result state) ∧
      Contextual view model ranked holds (SourceRecursiveIntersectionThunks.finishEdge handle result state) :=
  ⟨SourceCurrentAllocatedNativePhysicalCache.finishEdge_valid state physical handle request result running resident,
    finishEdge_contextual view model ranked holds state handle request result contextual running localLaw⟩

/-- An actual ready node lookup recovers the requested law and available result. -/
theorem node_observed_ready (request : NodeRequest Symbol Guard)
    (before chosen after : Native width Symbol Guard) (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (contextual : Contextual view model ranked holds before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : SourceRecursiveIntersectionThunks.lookupNode width request before = (.memoized handle, chosen))
    (demanded : SourceRecursiveIntersectionThunks.demandNode handle chosen = (.ready result, after)) :
    NodeLaw view model ranked holds request result ∧ Contextual view model ranked holds after ∧
      after = chosen ∧ Available after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready request before chosen after handle result physical ready safe selected demanded
  have chosenContext := lookupNode_contextual view model ranked holds before request contextual
  simp only [selected] at chosenContext
  exact ⟨chosenContext.nodes handle request result receipt.1,
    receipt.2.1 ▸ chosenContext, receipt.2⟩

/-- An actual ready edge lookup recovers the requested law and resident result. -/
theorem edge_observed_ready (request : EdgeRequest Symbol Guard)
    (before chosen after : Native width Symbol Guard) (handle : Nat) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (contextual : Contextual view model ranked holds before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : SourceRecursiveIntersectionThunks.lookupEdge width request before = (handle, chosen))
    (demanded : SourceRecursiveIntersectionThunks.demandEdge handle chosen = (.ready result, after)) :
    EdgeLaw view model ranked holds request result ∧ Contextual view model ranked holds after ∧
      after = chosen ∧ EdgeResident after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready request before chosen after handle result physical ready safe selected demanded
  have chosenContext := lookupEdge_contextual view model ranked holds before request contextual
  simp only [selected] at chosenContext
  exact ⟨chosenContext.edges handle request result receipt.1,
    receipt.2.1 ▸ chosenContext, receipt.2⟩

/-- An actual node start retains both invariants and its exact original running frame. -/
theorem node_started (request actual : NodeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (contextual : Contextual view model ranked holds before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : SourceRecursiveIntersectionThunks.lookupNode width request before = (.memoized handle, chosen))
    (demanded : SourceRecursiveIntersectionThunks.demandNode handle chosen = (.evaluate actual, running)) :
    actual = request ∧ SourceCurrentAllocatedNativePhysicalCache.Valid running ∧ Contextual view model ranked holds running ∧
      running.nodes.cells handle = some ⟨request, .evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before chosen running handle physical ready safe selected demanded
  have chosenGood := lookupNode view model ranked holds before request physical contextual ready safe
  simp only [selected] at chosenGood
  have runningGood := demandNode view model ranked holds chosen handle chosenGood.1 chosenGood.2
  simp only [demanded] at runningGood
  have cell := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningGood.1, runningGood.2, same ▸ cell⟩

/-- An actual edge start retains both invariants and its exact original running frame. -/
theorem edge_started (request actual : EdgeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (contextual : Contextual view model ranked holds before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : SourceRecursiveIntersectionThunks.lookupEdge width request before = (handle, chosen))
    (demanded : SourceRecursiveIntersectionThunks.demandEdge handle chosen = (.evaluate actual, running)) :
    actual = request ∧ SourceCurrentAllocatedNativePhysicalCache.Valid running ∧ Contextual view model ranked holds running ∧
      running.edges.cells handle = some ⟨request, .evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual before chosen running handle physical ready safe selected demanded
  have chosenGood := lookupEdge view model ranked holds before request physical contextual ready safe
  simp only [selected] at chosenGood
  have runningGood := demandEdge view model ranked holds chosen handle chosenGood.1 chosenGood.2
  simp only [demanded] at runningGood
  have cell := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningGood.1, runningGood.2, same ▸ cell⟩

end MicroCFTA.SourceCurrentAllocatedNativeContextualPhysicalCache
