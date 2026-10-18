import MicroCFTA.SourceCurrentStoredProfileComposition

/-!
# Assigned profiles through normal ordinary construction

Actual ordinary construction needs the primitive normalization invariants.
It does not need the recursive semantic heaps in Ready.
-/
namespace MicroCFTA.SourceCurrentStoredProfileNormalConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedRootProfile (Profile)
open InternedProfileSemantics (isEmpty)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Edges)
open InternedStoredMuOrigins (Normal)
open SourceCurrentStoredProfileFunction (denote)

private theorem future_survives (edge : EdgeValue Symbol Guard) (assignment : Reference → Profile)
    (future : edge.children.all (fun child => !isEmpty (denote child assignment)) = true) :
    edge.children.any (fun child => child.referenceOf == .empty) = false := by
  apply Bool.eq_false_iff.mpr
  intro selected
  obtain ⟨child,member,emptyTrue⟩ := List.any_eq_true.mp selected
  have emptyChild := (InternedEmptyNormalization.reference_empty child).mp (eq_of_beq emptyTrue)
  have later := List.all_eq_true.mp future child member
  rw [emptyChild,SourceCurrentStoredProfileFunction.empty] at later
  cases later

/-- Actual node normalization retains exactly the assigned future live-row decision. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (assignment : Reference → Profile) (state : State Symbol Guard) (normal : Normal state)
    (resident : Edges state edges) :
    denote (run (InternedConstructorTemplates.makeNode edges) state).1 assignment =
      if edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) then none else some [] := by
  have selectedResident : Edges state (canonicalEdges (surviving edges)) := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have same : (canonicalEdges (surviving edges)).any
      (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) =
      edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true,List.any_eq_true]
    constructor
    · rintro ⟨edge,member,live⟩
      exact ⟨edge,(List.mem_filter.mp (canonicalEdges_member _ edge member)).1,live⟩
    · rintro ⟨edge,member,live⟩
      have survives : edge ∈ surviving edges := by
        simp only [surviving,List.mem_filter]
        exact ⟨member,by rw [future_survives edge assignment live]; rfl⟩
      exact ⟨edge,InternedEdgeResidency.canonicalEdges_retains state normal.facts.coherent _ edge
        (fun value included => resident value (List.mem_filter.mp included).1) survives,live⟩
  have checked := InternedNestedFacts.node_verified edges state normal.facts resident
  have output := checked.result _ _ rfl
  have afterNormal : Normal (run (InternedConstructorTemplates.makeNode edges) state).2 :=
    ⟨checked.facts,
      InternedLiveEdges.makeNode_live edges state normal.live,
      InternedUnionNormalForm.makeNode_flat edges state normal.flat,
      InternedNonemptyRecords.makeNode_nonempty edges state normal.proper,
      InternedUnionNonemptyMembers.makeNode_membersNonempty edges state normal.members⟩
  cases normalized : canonicalEdges (surviving edges) with
  | nil =>
      have noRows : edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) = false := by
        simpa only [normalized,List.any_nil] using same.symm
      simp only [InternedConstructorTemplates.makeNode,normalized,run,SourceCurrentStoredProfileFunction.empty,noRows]
      rfl
  | cons first rest =>
      obtain ⟨entry,exactValue⟩ := InternedEdgeResidency.identifyNode_readback (first :: rest) state
        normal.facts.coherent normal.facts.linked (by
          intro edge member
          exact selectedResident edge (normalized ▸ member))
      have shape : (run (InternedConstructorTemplates.makeNode edges) state).1 = identifyNode (first :: rest) entry := by
        simpa only [InternedConstructorTemplates.makeNode,normalized,run] using exactValue
      have available : Available (run (InternedConstructorTemplates.makeNode edges) state).2 (identifyNode (first :: rest) entry) := shape ▸ output
      rw [shape]
      change denote (.node entry (first :: rest) _ _) assignment = _
      rw [SourceCurrentStoredProfileComposition.node entry (first :: rest) _ _ assignment _ afterNormal available]
      rw [←same,normalized]


end MicroCFTA.SourceCurrentStoredProfileNormalConstruction
