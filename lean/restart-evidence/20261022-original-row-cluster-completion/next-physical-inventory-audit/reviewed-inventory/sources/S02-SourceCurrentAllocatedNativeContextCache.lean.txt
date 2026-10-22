import MicroCFTA.SourceCurrentAllocatedNativePairContexts
import MicroCFTA.SourceEqualityNativeDemandRequestExact

/-!
# Contextual laws for completed native memo cells

The input model and its ranks remain fixed across heap effects. Returned
cells retain soundness and bounded completeness in one-sided pair contexts.
Physical validity remains a separate invariant. A new completion needs its
local contextual law. This file does not derive that law for recursive Mu
bodies, prove native completion, or model GHC thunk publication.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextCache
open Language BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativePairContexts
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State

/-- Context laws apply to complete original operands in the fixed input domain. -/
def NodeInputs (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (request : NodeRequest Symbol Guard) : Prop :=
  SourceRecursiveIntersectionInputView.Original request.left ∧
    SourceRecursiveIntersectionInputView.Original request.right ∧
    model.valid (SourceRecursiveIntersectionInputView.inputOf request.left) ∧
    model.valid (SourceRecursiveIntersectionInputView.inputOf request.right)

/-- Original edge children belong to the same fixed input domain. -/
def EdgeInputs (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (request : EdgeRequest Symbol Guard) : Prop :=
  (∀ child ∈ request.left.children, SourceRecursiveIntersectionInputView.Original child ∧
    model.valid (SourceRecursiveIntersectionInputView.inputOf child)) ∧
  (∀ child ∈ request.right.children, SourceRecursiveIntersectionInputView.Original child ∧
    model.valid (SourceRecursiveIntersectionInputView.inputOf child))

/-- A physical row uses its actual symbol, complete guard, and ordered original children. -/
def RowLanguage (holds : Guard → Term Symbol → Bool) (languages : Nat → Lang Symbol)
    (edge : EdgeValue Symbol Guard) : Lang Symbol := fun term =>
  ∃ terms, term = .node edge.entry.key.symbol terms ∧
    All₂ (fun child part => IntersectSchedule.inputLanguage languages
      (SourceRecursiveIntersectionInputView.inputOf child) part) edge.children terms ∧
    holds edge.entry.key.constraint term = true

/-- One input rank bounds every child of the physical row. -/
def RowAt (holds : Guard → Term Symbol → Bool) (ranks : Nat → Nat → Lang Symbol)
    (rank : Nat) (edge : EdgeValue Symbol Guard) : Lang Symbol := fun term =>
  ∃ terms, term = .node edge.entry.key.symbol terms ∧
    All₂ (fun child part => IntersectSchedule.inputAt ranks
      (SourceRecursiveIntersectionInputView.inputOf child) rank part) edge.children terms ∧
    holds edge.entry.key.constraint term = true

/-- A returned node law uses original languages and actual request pair contexts. -/
structure NodeLaw (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) : Prop where
  sound : NodeInputs view model request → ∀ output,
    SoundPairs model.languages request.domain.key output →
    Included (InternedGuardedLanguage.meaning holds output result) (fun term =>
      IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.left) term ∧
      IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.right) term)
  complete : NodeInputs view model request → ∀ bound output,
    CompletePairs ranked.languages bound request.domain.key output → ∀ first second,
    first + second ≤ bound → ∀ term,
    IntersectSchedule.inputAt ranked.languages (SourceRecursiveIntersectionInputView.inputOf request.left) first term →
    IntersectSchedule.inputAt ranked.languages (SourceRecursiveIntersectionInputView.inputOf request.right) second term →
    InternedGuardedLanguage.meaning holds output result term

/-- A returned edge law retains both original row meanings and bounded child derivations. -/
structure EdgeLaw (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) : Prop where
  sound : EdgeInputs view model request → ∀ output,
    SoundPairs model.languages request.domain.key output →
    Included (InternedGuardedLanguage.edgeMeaning holds output result) (fun term =>
      RowLanguage holds model.languages request.left term ∧ RowLanguage holds model.languages request.right term)
  complete : EdgeInputs view model request → ∀ bound output,
    CompletePairs ranked.languages bound request.domain.key output → ∀ first second,
    first + second ≤ bound → ∀ term,
    RowAt holds ranked.languages first request.left term → RowAt holds ranked.languages second request.right term →
    InternedGuardedLanguage.edgeMeaning holds output result term

/-- Only returned phases impose a contextual result law. -/
def Returned (law : Request → Answer → Prop) (state : FlatMemoThunk.State Key Request Answer) : Prop :=
  ∀ handle request result, state.cells handle = some ⟨request, .returned result⟩ → law request result

private theorem returned_empty (law : Request → Answer → Prop) :
    Returned law (FlatMemoThunk.empty : FlatMemoThunk.State Key Request Answer) := by
  intro handle request result found
  cases found

private theorem returned_lookup [DecidableEq Key] (law : Request → Answer → Prop)
    (key : Key) (request : Request) (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state) :
    Returned law (FlatMemoThunk.lookupOrInsert key request state).2 := by
  cases found : state.table key with
  | some handle => simpa only [FlatMemoThunk.lookupOrInsert, found] using valid
  | none =>
      intro handle original result stored
      by_cases same : handle = state.next
      · subst handle
        simp [FlatMemoThunk.lookupOrInsert, found, Cache.put] at stored
      · exact valid handle original result (by
          simpa only [FlatMemoThunk.lookupOrInsert, found, Cache.put, ite_eq_right same] using stored)

private theorem returned_evaluating (law : Request → Answer → Prop) (handle : Nat)
    (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state) :
    Returned law (FlatMemoThunk.setStatus handle .evaluating state) := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.setStatus, found] using valid
  | some cell =>
      intro other request result stored
      by_cases same : other = handle
      · subst other
        simp [FlatMemoThunk.setStatus, found, Cache.put] at stored
      · exact valid other request result (by
          simpa only [FlatMemoThunk.setStatus, found, Cache.put, ite_eq_right same] using stored)

private theorem returned_demand (law : Request → Answer → Prop) (handle : Nat)
    (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state) :
    Returned law (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using valid
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | suspended => simpa only [FlatMemoThunk.demand, found] using returned_evaluating law handle state valid
          | evaluating | returned result => simpa only [FlatMemoThunk.demand, found] using valid

private theorem returned_finish (law : Request → Answer → Prop) (handle : Nat) (request : Request) (result : Answer)
    (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state)
    (running : state.cells handle = some ⟨request, .evaluating⟩) (localLaw : law request result) :
    Returned law (FlatMemoThunk.finish handle result state) := by
  intro other original value stored
  by_cases same : other = handle
  · subst other
    have equal : request = original ∧ result = value := by
      simpa [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, Cache.put] using stored
    rcases equal with ⟨rfl, rfl⟩
    exact localLaw
  · exact valid other original value (by
      simpa only [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, Cache.put, ite_eq_right same] using stored)

/-- Contextual completed-cell guarantees do not duplicate physical or key validity. -/
structure Contextual (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (state : Native width Symbol Guard) : Prop where
  nodes : Returned (NodeLaw view model ranked holds) state.nodes
  edges : Returned (EdgeLaw view model ranked holds) state.edges

section Lifecycle
variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)

/-- Empty tables need no supplied completed contextual answer. -/
theorem initial_contextual (width : Nat) (machine : Machine Symbol Guard) :
    Contextual view model ranked holds (initial width machine) :=
  ⟨returned_empty _, returned_empty _⟩

/-- The fixed original model is unchanged when only the actual machine advances. -/
theorem advance_contextual (state : Native width Symbol Guard) (after : Machine Symbol Guard)
    (valid : Contextual view model ranked holds state) : Contextual view model ranked holds (advance state after) := ⟨valid.nodes, valid.edges⟩

/-- Actual node publication adds no completed answer and retains both contextual families. -/
theorem lookupNode_contextual (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (valid : Contextual view model ranked holds state) :
    Contextual view model ranked holds (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using valid
  | some keyValue =>
      simp only [lookupNode, key]
      exact ⟨returned_lookup _ keyValue request state.nodes valid.nodes, valid.edges⟩

/-- Actual edge publication retains every already completed contextual law. -/
theorem lookupEdge_contextual (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (valid : Contextual view model ranked holds state) :
    Contextual view model ranked holds (lookupEdge width request state).2 :=
  ⟨valid.nodes, returned_lookup _ _ request state.edges valid.edges⟩

/-- Demand changes no completed node law. -/
theorem demandNode_contextual (state : Native width Symbol Guard) (handle : Nat)
    (valid : Contextual view model ranked holds state) :
    Contextual view model ranked holds (demandNode handle state).2 :=
  ⟨returned_demand _ handle state.nodes valid.nodes, valid.edges⟩

/-- Demand changes no completed edge law. -/
theorem demandEdge_contextual (state : Native width Symbol Guard) (handle : Nat)
    (valid : Contextual view model ranked holds state) :
    Contextual view model ranked holds (demandEdge handle state).2 :=
  ⟨valid.nodes, returned_demand _ handle state.edges valid.edges⟩

/-- Completion stores a locally proved law at the actual original running node request. -/
theorem finishNode_contextual (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (valid : Contextual view model ranked holds state)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (localLaw : NodeLaw view model ranked holds request result) :
    Contextual view model ranked holds (finishNode handle result state) :=
  ⟨returned_finish _ handle request result state.nodes valid.nodes running localLaw, valid.edges⟩

/-- Completion stores a locally proved law at the actual original running edge request. -/
theorem finishEdge_contextual (state : Native width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (valid : Contextual view model ranked holds state)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (localLaw : EdgeLaw view model ranked holds request result) :
    Contextual view model ranked holds (finishEdge handle result state) :=
  ⟨valid.nodes, returned_finish _ handle request result state.edges valid.edges running localLaw⟩

/-- An actual completed node hit recovers the requested contextual law without replay. -/
theorem node_ready_contextual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Native width Symbol Guard) (physical : SourceEqualityNativeDemandProvenance.Valid holds state)
    (valid : Contextual view model ranked holds state) (request original : NodeRequest Symbol Guard)
    (ready : NodeReady state.machine request) (key : IntersectionFlatMemoKeyDomain.Triple width)
    (checked : NodeKey width request key) (handle : Nat) (published : state.nodes.table key = some handle)
    (result : Value Symbol Guard) (stored : state.nodes.cells handle = some ⟨original, .returned result⟩) :
    lookupNode width request state = (.memoized handle, state) ∧ demandNode handle state = (.ready result, state) ∧
      NodeLaw view model ranked holds request result := by
  have same := SourceEqualityNativeDemandProvenance.node_request_exact state physical request ready key checked
    handle published _ stored
  change original = request at same
  subst original
  exact ⟨by simp only [lookupNode, checked.1, FlatMemoThunk.lookupOrInsert, published],
    by simp only [demandNode, FlatMemoThunk.demand, stored], valid.nodes handle request result stored⟩

/-- An actual completed edge hit recovers the exact ordered-row contextual law. -/
theorem edge_ready_contextual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Native width Symbol Guard) (physical : SourceEqualityNativeDemandProvenance.Valid holds state)
    (valid : Contextual view model ranked holds state) (request original : EdgeRequest Symbol Guard)
    (ready : EdgeReady state.machine request) (key : IntersectionFlatMemoKeyDomain.Triple width)
    (checked : EdgeKeyOf width request key) (handle : Nat) (published : state.edges.table key = some handle)
    (result : EdgeValue Symbol Guard) (stored : state.edges.cells handle = some ⟨original, .returned result⟩) :
    lookupEdge width request state = (handle, state) ∧ demandEdge handle state = (.ready result, state) ∧
      EdgeLaw view model ranked holds request result := by
  have same := SourceEqualityNativeDemandProvenance.edge_request_exact state physical request ready key checked
    handle published _ stored
  change original = request at same
  subst original
  exact ⟨by simp only [lookupEdge, checked.1, FlatMemoThunk.lookupOrInsert, published],
    by simp only [demandEdge, FlatMemoThunk.demand, stored], valid.edges handle request result stored⟩


/-- Actual node lookup and ready demand derive the requested law from current invariants. -/
theorem node_observed_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (before chosen after : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceEqualityNativeDemandProvenance.Valid holds before)
    (valid : Contextual view model ranked holds before) (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready result, after)) :
    NodeLaw view model ranked holds request result ∧ after = chosen := by
  have chosenPhysical := SourceEqualityNativeDemandProvenance.lookupNode_valid before physical request ready safe
  have chosenContext := lookupNode_contextual view model ranked holds before request valid
  simp only [selected] at chosenPhysical chosenContext
  obtain ⟨key, requested, published, machine⟩ :=
    SourceRecursiveIntersectionNative.lookupNode_memoized request before chosen handle selected
  have chosenReady : NodeReady chosen.machine request := by rw [machine]; exact ready
  obtain ⟨original, stored, same⟩ := SourceRecursiveIntersectionNative.demandNode_ready handle chosen after result demanded
  exact ⟨(node_ready_contextual view model ranked holds chosen chosenPhysical chosenContext request original chosenReady
    key ⟨requested, safe⟩ handle published result stored).2.2, same⟩

/-- Actual ordered edge lookup and ready demand derive the requested row law. -/
theorem edge_observed_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (before chosen after : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (handle : Nat) (result : EdgeValue Symbol Guard)
    (physical : SourceEqualityNativeDemandProvenance.Valid holds before)
    (valid : Contextual view model ranked holds before) (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready result, after)) :
    EdgeLaw view model ranked holds request result ∧ after = chosen := by
  have chosenPhysical := SourceEqualityNativeDemandProvenance.lookupEdge_valid before physical request ready safe
  have chosenContext := lookupEdge_contextual view model ranked holds before request valid
  simp only [selected] at chosenPhysical chosenContext
  obtain ⟨published, machine⟩ :=
    SourceRecursiveIntersectionNative.lookupEdge_selected request before chosen handle selected
  have chosenReady : EdgeReady chosen.machine request := by rw [machine]; exact ready
  obtain ⟨original, stored, same⟩ := SourceRecursiveIntersectionNative.demandEdge_ready handle chosen after result demanded
  exact ⟨(edge_ready_contextual view model ranked holds chosen chosenPhysical chosenContext request original chosenReady
    _ ⟨rfl, safe⟩ handle published result stored).2.2, same⟩

end Lifecycle
end MicroCFTA.SourceCurrentAllocatedNativeContextCache
