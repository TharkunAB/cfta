import MicroCFTA.EqualityLeafProjectionReads
import MicroCFTA.InternedNodeSetCongruence
import MicroCFTA.InternedErasedEdgeReplay

/-!
# Physical source normalization around projected leaf edits

Actual node readback exposes the canonical surviving edge records. Mapping
an empty-preserving child edit before or after that normalization gives the
same complete node request. Required-path filtering satisfies the same law.
-/
namespace MicroCFTA.EqualityLeafProjectionPhysical
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedNodeSetCongruence
open EqualityLeafProjectionSyntax

/-- Physical node readback retains exactly the normalized complete edge list. -/
theorem makeNode_edges [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    nodeEdges (run (makeNode edges) state).1 = canonicalEdges (surviving edges) := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · rename_i same
    simp only [run, nodeEdges, same]
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [same] using selected)
    simp only [run, exactResult, identifyNode, nodeEdges, same]

/-- Deadness is the source's literal empty-child test. -/
def dead (edge : EdgeValue Symbol Guard) : Bool :=
  edge.children.any (fun child => child.referenceOf == .empty)

/-- Normalized physical membership removes only dead rows and duplicate identities. -/
theorem normalized_member (state : State Symbol Guard) (coherent : Coherent state)
    (edges : List (EdgeValue Symbol Guard)) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (edge : EdgeValue Symbol Guard) :
    edge ∈ canonicalEdges (surviving edges) ↔ edge ∈ edges ∧ dead edge = false := by
  constructor
  · intro member
    have present := List.mem_filter.mp (canonicalEdges_member _ edge member)
    exact ⟨present.1, by simpa only [dead, Bool.not_eq_true'] using present.2⟩
  · rintro ⟨member, live⟩
    exact canonicalEdges_retains state coherent (surviving edges) edge
      (fun value member => resident value (List.mem_filter.mp member).1)
      (List.mem_filter.mpr ⟨member, by simpa only [dead, Bool.not_eq_true'] using live⟩)

/-- Child mapping and an optional required-arity filter commute with physical
normalization. The result is equality of complete constructor computations. -/
theorem mapped_normalization (before after : State Symbol Guard) (beforeCoherent : Coherent before)
    (afterCoherent : Coherent after) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (select : EdgeValue Symbol Guard → Bool) (change : EdgeValue Symbol Guard → EdgeValue Symbol Guard)
    (changedResident : ∀ edge ∈ edges, EdgeResident after (change edge))
    (preservesDead : ∀ edge ∈ edges, dead edge = true → dead (change edge) = true) :
    makeNode ((edges.filter select).map change) =
      makeNode (((canonicalEdges (surviving edges)).filter select).map change) := by
  apply makeNode_same_members after afterCoherent _ _
  · intro edge member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact changedResident original (List.mem_filter.mp present).1
  · intro edge member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact changedResident original ((normalized_member before beforeCoherent edges resident original).mp (List.mem_filter.mp present).1).1
  intro edge
  simp only [surviving, List.mem_filter, List.mem_map, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨original, ⟨member, selected⟩, same⟩, live⟩
    have originalLive : dead original = false := by
      cases deadness : dead original
      · rfl
      · have stillDead := preservesDead original member deadness
        have impossible : dead (change original) = false := by simpa only [same, dead] using live
        simp [stillDead] at impossible
    exact ⟨⟨original, ⟨(normalized_member before beforeCoherent edges resident original).mpr ⟨member, originalLive⟩, selected⟩, same⟩, live⟩
  · rintro ⟨⟨original, ⟨member, selected⟩, same⟩, live⟩
    exact ⟨⟨original, ⟨((normalized_member before beforeCoherent edges resident original).mp member).1, selected⟩, same⟩, live⟩

/-- The original occurrence rows and the actual stored node rows yield the
same mapped constructor request after recursive child results are available. -/
theorem mapped_readback [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (afterCoherent : Coherent after) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (select : EdgeValue Symbol Guard → Bool) (change : EdgeValue Symbol Guard → EdgeValue Symbol Guard)
    (changedResident : ∀ edge ∈ edges, EdgeResident after (change edge))
    (preservesDead : ∀ edge ∈ edges, dead edge = true → dead (change edge) = true) :
    makeNode ((edges.filter select).map change) =
      makeNode (((nodeEdges (run (makeNode edges) before).1).filter select).map change) := by
  rw [makeNode_edges edges before beforeCoherent linked resident]
  exact mapped_normalization before after beforeCoherent afterCoherent edges resident select change changedResident preservesDead

/-- Only EmptyNode carries the primitive empty reference. -/
theorem reference_empty (value : Value Symbol Guard) : value.referenceOf = .empty ↔ value = .empty := by
  cases value <;> simp [Value.referenceOf]

/-- An empty-preserving child map keeps every originally dead ancestor row dead. -/
theorem mapChildren_dead (change : Nat → Value Symbol Guard → Value Symbol Guard)
    (empty : ∀ index, change index .empty = .empty) (offset : Nat) (children : List (Value Symbol Guard))
    (dead : children.any (fun child => child.referenceOf == .empty) = true) :
    (mapChildren change offset children).any (fun child => child.referenceOf == .empty) = true := by
  induction children generalizing offset with
  | nil => simp at dead
  | cons child rest ih =>
      simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at dead
      rcases dead with head | tail
      · have childEmpty := (reference_empty child).mp head
        subst child
        simp [mapChildren, empty, Value.referenceOf]
      · simp only [mapChildren, List.any_cons, ih (offset + 1) tail, Bool.or_true]

/-- Dead-edge detection depends only on the actual ordered child references. -/
theorem dead_references (edge : EdgeValue Symbol Guard) (children : List (Value Symbol Guard))
    (same : edge.children.map Value.referenceOf = children.map Value.referenceOf) :
    dead edge = children.any (fun child => child.referenceOf == .empty) := by
  have mapped := congrArg (fun refs => refs.any (fun ref => ref == InternedBinderProtocol.NodeRef.empty)) same
  simpa only [List.any_map, Function.comp_def, dead] using mapped

/-- Rebuild the actual source edge key after the ordered child edits complete. -/
def rebuild [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (change : Nat → Value Symbol Guard → Value Symbol Guard) (edge : EdgeValue Symbol Guard) : EdgeValue Symbol Guard :=
  (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint (mapChildren change 0 edge.children)) state).1

/-- Actual edge interning derives dead-row preservation from empty-preserving child edits. -/
theorem rebuild_dead [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (coherent : Coherent state)
    (change : Nat → Value Symbol Guard → Value Symbol Guard) (empty : ∀ index, change index .empty = .empty)
    (edge : EdgeValue Symbol Guard) (isDead : dead edge = true) : dead (rebuild state change edge) = true := by
  have fields := InternedErasedEdgeReplay.makeEdge_references edge.entry.key.symbol edge.entry.key.constraint
    (mapChildren change 0 edge.children) state coherent
  rw [dead_references (rebuild state change edge) _ fields]
  exact mapChildren_dead change empty 0 edge.children isDead

/-- Physical path-edit lowering commutes with normalization after actual child
and edge requests complete. No complete-pass equation is a premise. -/
theorem rebuild_readback [DecidableEq (EdgeKey Symbol Guard)]
    (before built after : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (builtCoherent : Coherent built) (afterCoherent : Coherent after)
    (edges : List (EdgeValue Symbol Guard)) (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (select : EdgeValue Symbol Guard → Bool) (change : Nat → Value Symbol Guard → Value Symbol Guard)
    (empty : ∀ index, change index .empty = .empty)
    (changedResident : ∀ edge ∈ edges, EdgeResident after (rebuild built change edge)) :
    makeNode ((edges.filter select).map (rebuild built change)) =
      makeNode (((nodeEdges (run (makeNode edges) before).1).filter select).map (rebuild built change)) :=
  mapped_readback before after beforeCoherent linked afterCoherent edges resident select (rebuild built change)
    changedResident (fun edge _ => rebuild_dead built builtCoherent change empty edge)

/-- Ordered child mapping retains the source edge arity. -/
theorem mapChildren_length (change : Nat → α → α) (offset : Nat) (children : List α) :
    (mapChildren change offset children).length = children.length := by
  induction children generalizing offset with
  | nil => rfl
  | cons child rest ih => simp only [mapChildren, List.length_cons, ih]

/-- Actual parent rebuilding retains its symbol, full guard, and child arity. -/
theorem rebuild_fields [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (coherent : Coherent state)
    (change : Nat → Value Symbol Guard → Value Symbol Guard) (edge : EdgeValue Symbol Guard) :
    (rebuild state change edge).entry.key.symbol = edge.entry.key.symbol ∧
      (rebuild state change edge).entry.key.constraint = edge.entry.key.constraint ∧
      (rebuild state change edge).children.length = edge.children.length := by
  let children := mapChildren change 0 edge.children
  let key : EdgeKey Symbol Guard := ⟨edge.entry.key.symbol, children.map Value.referenceOf, edge.entry.key.constraint⟩
  let identify := fun entry => EdgeValue.mk entry children
  have correct := edgeStep_correct key identify state coherent.valid
  have after := edgeStep_coherent key identify state coherent (fun _ same => ⟨rfl, same, rfl⟩)
  have fields := (after.edges key _ correct.2.2).2
  have symbol := congrArg EdgeKey.symbol fields.1
  have constraint := congrArg EdgeKey.constraint fields.1
  refine ⟨symbol, constraint, ?_⟩
  have arity := congrArg List.length fields.2
  simpa only [rebuild, makeEdge, run, key, identify, children, List.length_map, mapChildren_length] using arity

end MicroCFTA.EqualityLeafProjectionPhysical
