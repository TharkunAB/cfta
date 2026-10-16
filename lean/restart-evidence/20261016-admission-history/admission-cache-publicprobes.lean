import MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache

#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.empty
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.lookup
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.status
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.demand
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.finish
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.initial_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.advance_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.lookupNode_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.lookupEdge_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.demandNode_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.demandEdge_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.finishNode_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.finishEdge_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Covered.admitted
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Covered.seen_admitted
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.node_published
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.edge_published
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Covered.rebase
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.NodeCovered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.EdgeCovered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.empty
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.lookup
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.status
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.demand
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Requests.finish
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.initial_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.advance_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.lookupNode_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.lookupEdge_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.demandNode_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.demandEdge_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.finishNode_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.finishEdge_covered
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Covered.admitted
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Covered.seen_admitted
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.node_published
#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.edge_published

#check MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache.Covered.rebase

namespace MicroCFTA.SourceCurrentAllocatedNativeAdmissionCacheProbes
open Cache Language IntersectSchedule InternedConstructorTemplates
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeAdmissionCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat} {view : View Symbol}

-- All native cells start covered without a result premise.
example (inputs : FiniteInput view) (machine : Machine Symbol Guard) :
    Covered inputs (initial width machine) := initial_covered inputs width machine

-- An actual key hit retains the old request even when the later candidate has no supplied admission.
example {K R A : Type} [DecidableEq K] (property : R → Prop) (key : K) (candidate : R)
    (state : FlatMemoThunk.State K R A) (covered : Requests property state)
    (handle : Nat) (found : state.table key = some handle) :
    Requests property (FlatMemoThunk.lookupOrInsert key candidate state).2 := by
  simpa only [FlatMemoThunk.lookup_hit key candidate state handle found] using covered

-- Suspended cells already carry coverage before any evaluation.
example {K R A : Type} (property : R → Prop) (state : FlatMemoThunk.State K R A)
    (covered : Requests property state) (handle : Nat) (request : R)
    (stored : state.cells handle = some ⟨request, .suspended⟩) : property request := covered handle _ stored

-- Evaluating cells retain the same request coverage.
example {K R A : Type} (property : R → Prop) (state : FlatMemoThunk.State K R A)
    (covered : Requests property state) (handle : Nat) (request : R)
    (stored : state.cells handle = some ⟨request, .evaluating⟩) : property request := covered handle _ stored

-- A finish preserves request coverage without asserting any candidate-result law.
example {K R A : Type} (property : R → Prop) (state : FlatMemoThunk.State K R A)
    (covered : Requests property state) (handle : Nat) (candidate : A) :
    Requests property (FlatMemoThunk.finish handle candidate state) := Requests.finish property handle candidate state covered

-- Publishing then demanding a node derives all-phase coverage in the reached native state.
example (inputs : FiniteInput view) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (covered : Covered inputs state) (request : NodeRequest Symbol Guard) (known : NodeCovered inputs request) (handle : Nat) :
    Covered inputs (demandNode handle (lookupNode width request state).2).2 :=
  demandNode_covered inputs _ handle (lookupNode_covered inputs state request covered known)

-- Returning a node keeps both weaker invariants for its actual cells.
example (inputs : FiniteInput view) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (covered : Covered inputs state) (handle : Nat) (candidate : Value Symbol Guard) :
    SourceCurrentAllocatedNativeInputModelTransport.Admitted view (finiteInputMeaning view inputs)
      (finishNode handle candidate state) ∧
    SourceCurrentAllocatedNativeContextRebase.SeenAdmitted inputs (finishNode handle candidate state) :=
  ⟨(finishNode_covered inputs state handle candidate covered).admitted,
    (finishNode_covered inputs state handle candidate covered).seen_admitted⟩

-- Returning an edge also retains actual child admission and seen-pair coverage.
example (inputs : FiniteInput view) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (covered : Covered inputs state) (handle : Nat) (candidate : EdgeValue Symbol Guard) :
    SourceCurrentAllocatedNativeInputModelTransport.Admitted view (finiteInputMeaning view inputs)
      (finishEdge handle candidate state) ∧
    SourceCurrentAllocatedNativeContextRebase.SeenAdmitted inputs (finishEdge handle candidate state) :=
  ⟨(finishEdge_covered inputs state handle candidate covered).admitted,
    (finishEdge_covered inputs state handle candidate covered).seen_admitted⟩

-- Whole-machine changes retain all exact stored requests in both native tables.
example (inputs : FiniteInput view) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (covered : Covered inputs state) (after : Machine Symbol Guard) : Covered inputs (advance state after) :=
  advance_covered inputs state after covered

-- An actual returned node cell exposes both operand admission and seen names directly.
example (inputs : FiniteInput view) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (covered : Covered inputs state) (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (found : state.nodes.cells handle = some ⟨request, .returned result⟩) : NodeCovered inputs request :=
  covered.nodes handle _ found

-- Rebase retains actual returned admission without a new result or new request oracle.
example {oldView newView : View Symbol} {before : FiniteInput oldView} {after : FiniteInput newView}
    (agreement : SourceCurrentAllocatedNativeContextRebase.Agreement before after)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (covered : Covered before state) :
    SourceCurrentAllocatedNativeInputModelTransport.Admitted newView (finiteInputMeaning newView after) state ∧
      SourceCurrentAllocatedNativeContextRebase.SeenAdmitted after state :=
  ⟨(covered.rebase agreement).admitted, (covered.rebase agreement).seen_admitted⟩

-- A running original request remains covered across view and inventory growth.
example {oldView newView : View Symbol} {before : FiniteInput oldView} {after : FiniteInput newView}
    (agreement : SourceCurrentAllocatedNativeContextRebase.Agreement before after)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (covered : Covered before state)
    (handle : Nat) (request : NodeRequest Symbol Guard)
    (stored : state.nodes.cells handle = some ⟨request, .evaluating⟩) : NodeCovered after request :=
  (Covered.rebase agreement covered).nodes handle _ stored
end MicroCFTA.SourceCurrentAllocatedNativeAdmissionCacheProbes
