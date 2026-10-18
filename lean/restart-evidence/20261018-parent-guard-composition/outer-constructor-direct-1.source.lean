import MicroCFTA.SourceCurrentRawRebuildNumeric
import MicroCFTA.SourceCurrentMuReconstructionEffects
import MicroCFTA.SourceCurrentAllocatedPartialWorkerStability

/-!
# Physical resource bounds for non-Parent outer constructors

A resident original bounds the replacement list width by its stored mass.
Raw reconstruction retains the same finite flat guard alphabet. Literal
rows and children returns supply their exact length laws. Equality prefix
and descent leave the physical heap and domain supply unchanged. Filtered
resident Mu reconstruction returns at the unchanged full caller.
These local bounds do not provide a complete outer execution schedule.
-/
namespace MicroCFTA.SourceCurrentOuterConstructorBounds
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorkerStability (bind_done_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Known" => SourceEqualityAnnotationHeap.Heap
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
local notation "rawModify" => SourceCurrentAllocatedRawRebuild.modify
variable {width : Nat}

/-- One resident-width raw constructor has a count-independent initial envelope. -/
def profile (entry : Profile) : Profile := SourceCurrentEditFrame.constructorProfile (scalar entry) entry

/-- The constructor envelope retains every initial numeric component. -/
theorem profile_ge (entry : Profile) : Le entry (profile entry) :=
  SourceCurrentEditFrame.constructorProfile_ge _ _

/-- Larger initial bounds retain the full raw constructor envelope. -/
theorem profile_mono {first last : Profile} (increase : Le first last) : Le (profile first) (profile last) :=
  (SourceCurrentEditFrame.constructorProfile_mono (scalar first) increase).trans
    (SourceCurrentEditFrame.constructorProfile_count_mono (SourceCurrentConstrainedCapTargetForecast.scalar_mono increase) last)

private theorem scalar_fits (entry : Profile) (before : Checked width) (fits : Fits entry before) :
    SourceCurrentMemoMergeResourceControl.Fits (scalar entry) before.native.machine.heap :=
  ⟨fits.stored.mono (SourceCurrentConstrainedCapTargetForecast.scalar_mass entry),
    Nat.le_trans fits.nodes (SourceCurrentConstrainedCapTargetForecast.scalar_nodes entry),
    Nat.le_trans fits.edges (SourceCurrentConstrainedCapTargetForecast.scalar_edges entry), Nat.zero_le _⟩

private theorem edge_width (entry : Profile) (before : Checked width) (fits : Fits entry before)
    (original : Edge) (resident : EdgeResident before.native.machine.heap original) :
    original.children.length ≤ scalar entry := by
  have mass := InternedValueMassHeap.resident _ fits.stored original resident
  rw [InternedValueMass.edge_children,InternedValueMass.values_eq_length_sum] at mass
  have enough := SourceCurrentConstrainedCapTargetForecast.scalar_mass entry
  omega

private theorem node_width (entry : Profile) (before : Checked width) (fits : Fits entry before)
    (identity : Interned InternedBinderProtocol.NodeKey) (rows : List Edge) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available before.native.machine.heap (.node identity rows depth free)) :
    rows.length ≤ scalar entry := by
  have mass := InternedValueMassHeap.available _ fits.stored _ available
  simp only [InternedValueMass.value,InternedValueMass.edges_eq_length_sum] at mass
  have enough := SourceCurrentConstrainedCapTargetForecast.scalar_mass entry
  omega

/-- Indexed equality descent retains the initial physical profile and flat guard carrier. -/
theorem descend (alphabet : List Guard) (entry : Profile) (before : Caller width)
    (combined : EqValue) (index : Nat) (fits : Fits entry before.checked)
    (known : Known (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    let after := (SourceCurrentAllocatedPartialGraph.descend before combined index).2
    Fits entry after.checked ∧ Known (fun guard => guard ∈ alphabet) after.checked.native.machine.heap ∧
      after.checked.native.machine.heap = before.checked.native.machine.heap ∧
      after.checked.native.machine.domains = before.checked.native.machine.domains :=
  ⟨⟨fits.nodes,fits.edges,fits.domains,fits.stored⟩,known,rfl,rfl⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The literal inherited prefix retains the profile and flat carrier in every return branch. -/
theorem prefix_state (alphabet : List Guard) (entry : Profile) (before : Caller width)
    (original : Edge) (inherited : EqValue) (fits : Fits entry before.checked)
    (known : Known (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    let after := SourceCurrentAllocatedPartialGraph.prefixState before original inherited
    Fits entry after.checked ∧ Known (fun guard => guard ∈ alphabet) after.checked.native.machine.heap ∧
      after.checked.native.machine.heap = before.checked.native.machine.heap ∧
      after.checked.native.machine.domains = before.checked.native.machine.domains :=
  ⟨⟨fits.nodes,fits.edges,fits.domains,fits.stored⟩,known,rfl,rfl⟩

/-- A raw equal-arity edge derives its numeric envelope and retains the original full guard carrier. -/
theorem edge (alphabet : List Guard) (entry : Profile) (original : Edge) (children : List Node)
    (before : Checked width) (fits : Fits entry before)
    (known : Known (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (resident : EdgeResident before.native.machine.heap original) (available : Values before.native.machine.heap children)
    (same : children.length = original.children.length) :
    let actual := rawEdge original children before
    Fits (profile entry) actual.2 ∧ Known (fun guard => guard ∈ alphabet) actual.2.native.machine.heap ∧
      actual.2.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      actual.2.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  have length : children.length ≤ scalar entry := same ▸ edge_width entry before fits original resident
  have resources := SourceCurrentMemoMergeResourceControl.edge original.entry.key.symbol original.entry.key.constraint
    children before.native.machine.heap (scalar entry) (scalar entry) (scalar_fits entry before fits) available length
  have carrier := SourceEqualityAnnotationHeap.run (fun guard => guard ∈ alphabet)
    (makeEdge original.entry.key.symbol original.entry.key.constraint children)
    (SourceEqualityAnnotationHeap.makeEdge _ _ _ _ (known _ _ resident)) before.native.machine.heap known
  exact ⟨⟨resources.1.nodes,resources.1.edges,fits.domains,resources.1.stored⟩,carrier,resources.2.2⟩

/-- Ordered raw node reconstruction derives the same envelope on both identity branches. -/
theorem modify (alphabet : List Guard) (entry : Profile)
    (identity : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (before : Checked width)
    (fits : Fits entry before) (known : Known (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (available : Available before.native.machine.heap (.node identity oldRows depth free))
    (resident : Edges before.native.machine.heap newRows) (sameLength : newRows.length = oldRows.length) :
    let actual := rawModify (.node identity oldRows depth free) oldRows newRows before
    Fits (profile entry) actual.2 ∧ Known (fun guard => guard ∈ alphabet) actual.2.native.machine.heap ∧
      actual.2.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + 1 ∧
      actual.2.native.machine.heap.edges.next = before.native.machine.heap.edges.next := by
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
    exact ⟨fits.mono (profile_ge entry),known,Nat.le_add_right _ _,rfl⟩
  · have length : newRows.length ≤ scalar entry := sameLength ▸ node_width entry before fits identity oldRows depth free available
    have resources := SourceCurrentMemoMergeResourceControl.node newRows before.native.machine.heap
      (scalar entry) (scalar entry) (scalar_fits entry before fits) resident length
    have carrier := SourceEqualityAnnotationHeap.run (fun guard => guard ∈ alphabet) (makeNode newRows)
      (SourceEqualityAnnotationHeap.makeNode _ _) before.native.machine.heap known
    simpa only [SourceCurrentAllocatedRawRebuild.modify,SourceEqualityPartialNodeRebuild.modify,same,↓reduceIte] using
      (show Fits (profile entry) (SourceCurrentAllocatedQueryMemo.advancePhysical before
        ⟨(run (makeNode newRows) before.native.machine.heap).2,before.operations⟩) ∧
        Known (fun guard => guard ∈ alphabet) (run (makeNode newRows) before.native.machine.heap).2 ∧
        (run (makeNode newRows) before.native.machine.heap).2.nodes.next ≤ before.native.machine.heap.nodes.next+1 ∧
        (run (makeNode newRows) before.native.machine.heap).2.edges.next = before.native.machine.heap.edges.next from
        ⟨⟨resources.1.nodes,resources.1.edges,fits.domains,resources.1.stored⟩,carrier,resources.2.2⟩)

variable [DecidableEq Symbol] [DecidableEq Node]

private theorem walk_length (fuel : Nat) {g s r e p h m c n limit combined index values before results after}
    (actual : SourceCurrentAllocatedPartialWorker.walk fuel g s r e p h m c n limit combined index values before =
      .done results (after : Caller width)) : results.length = values.length := by
  induction fuel generalizing index values before results after with
  | zero =>
    cases values <;> simp only [SourceCurrentAllocatedPartialWorker.walk] at actual
    · cases actual; rfl
    · cases actual
  | succ fuel ih =>
    cases values with
    | nil => simp only [SourceCurrentAllocatedPartialWorker.walk] at actual; cases actual; rfl
    | cons value rest =>
      simp only [SourceCurrentAllocatedPartialWorker.walk] at actual
      obtain ⟨head,middle,_,later⟩ := (bind_done_iff _ _ _ _).mp actual
      obtain ⟨tail,final,called,last⟩ := (bind_done_iff _ _ _ _).mp later
      cases last
      have length := ih called
      simpa only [List.length_cons] using congrArg Nat.succ length

/-- Literal successful child traversal retains the exact original slot count. -/
theorem children_length {fuel g s r e p h m c n limit combined values before results after}
    (actual : SourceCurrentAllocatedPartialWorker.children fuel g s r e p h m c n limit combined values before =
      .done results (after : Caller width)) : results.length = values.length := by
  cases combined with
  | contradiction =>
    simp only [SourceCurrentAllocatedPartialWorker.children] at actual
    cases actual
    exact List.length_map _
  | live identity records => exact walk_length fuel actual

/-- Literal successful row traversal retains the exact original row count. -/
theorem rows_length (fuel : Nat) {g s r e p h m c n limit inherited values before results after}
    (actual : SourceCurrentAllocatedPartialWorker.rows fuel g s r e p h m c n limit inherited values before =
      .done results (after : Caller width)) : results.length = values.length := by
  induction fuel generalizing values before results after with
  | zero =>
    cases values <;> simp only [SourceCurrentAllocatedPartialWorker.rows] at actual
    · cases actual; rfl
    · cases actual
  | succ fuel ih =>
    cases values with
    | nil => simp only [SourceCurrentAllocatedPartialWorker.rows] at actual; cases actual; rfl
    | cons value rest =>
      simp only [SourceCurrentAllocatedPartialWorker.rows] at actual
      obtain ⟨narrowed,middle,_,later⟩ := (bind_done_iff _ _ _ _).mp actual
      obtain ⟨head,current,_,later⟩ := (bind_done_iff _ _ _ _).mp later
      obtain ⟨tail,final,called,last⟩ := (bind_done_iff _ _ _ _).mp later
      cases last
      have length := ih called
      simpa only [List.length_cons] using congrArg Nat.succ length

/-- Actual completed child traversal supplies the arity law for its raw descendant rebuild. -/
theorem children_rebuild (alphabet : List Guard) (entry : Profile) (original : Edge)
    {fuel g s r e p h m c n limit combined start children before}
    (actual : SourceCurrentAllocatedPartialWorker.children fuel g s r e p h m c n limit combined original.children start =
      .done children (before : Caller width))
    (fits : Fits entry before.checked) (known : Known (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap original)
    (available : Values before.checked.native.machine.heap children) :
    let rebuilt := rawEdge original children before.checked
    Fits (profile entry) rebuilt.2 ∧ Known (fun guard => guard ∈ alphabet) rebuilt.2.native.machine.heap ∧
      rebuilt.2.native.machine.heap.nodes.next = before.checked.native.machine.heap.nodes.next ∧
      rebuilt.2.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + 1 :=
  edge alphabet entry original children before.checked fits known resident available (children_length actual)

/-- Actual completed rows supply the width law for their ordinary raw node rebuild. -/
theorem rows_rebuild (alphabet : List Guard) (entry : Profile)
    (identity : Interned InternedBinderProtocol.NodeKey) (oldRows : List Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    {fuel g s r e p h m c n limit inherited start newRows before}
    (actual : SourceCurrentAllocatedPartialWorker.rows fuel g s r e p h m c n limit inherited oldRows start =
      .done newRows (before : Caller width))
    (fits : Fits entry before.checked) (known : Known (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap (.node identity oldRows depth free))
    (resident : Edges before.checked.native.machine.heap newRows) :
    let rebuilt := rawModify (.node identity oldRows depth free) oldRows newRows before.checked
    Fits (profile entry) rebuilt.2 ∧ Known (fun guard => guard ∈ alphabet) rebuilt.2.native.machine.heap ∧
      rebuilt.2.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + 1 ∧
      rebuilt.2.native.machine.heap.edges.next = before.checked.native.machine.heap.edges.next :=
  modify alphabet entry identity oldRows newRows depth free before.checked fits known available resident (rows_length fuel actual)

/-- Initial filtered resident probes complete the Mu body at the unchanged full caller and profile. -/
theorem mu_body (alphabet : List Guard) (entryProfile : Profile)
    (fuel g s r e p h m c n limit : Nat) (identity : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Node) (inherited : EqValue) (before : Caller width)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (probes : InternedFreshOrdinaryProbeHeap.Heap before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap (.mu identity body depth ordinary))
    (fits : Fits entryProfile before.checked)
    (known : Known (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    SourceCurrentAllocatedPartialWorker.nodeBody fuel g s r e p h m c n limit
      ⟨inherited,.mu identity body depth ordinary⟩ before =
      .done (cleanup (.mu identity body depth ordinary)) before ∧
    Fits entryProfile before.checked ∧ Known (fun guard => guard ∈ alphabet) before.checked.native.machine.heap ∧
      Available before.checked.native.machine.heap (cleanup (.mu identity body depth ordinary)) := by
  have completed := SourceCurrentMuReconstructionEffects.complete identity body depth ordinary
    before.checked.native.machine.heap coherent probes available
  refine ⟨?_,fits,known,completed.2⟩
  simp only [SourceCurrentAllocatedPartialWorker.nodeBody,completed.1]
  rfl

end MicroCFTA.SourceCurrentOuterConstructorBounds
