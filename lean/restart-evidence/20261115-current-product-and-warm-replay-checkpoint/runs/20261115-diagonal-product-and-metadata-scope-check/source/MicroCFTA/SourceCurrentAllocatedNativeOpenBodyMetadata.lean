import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.InternedOrdinaryUnionReadback

/-!
# Exact metadata of concrete transformed current-source rows

The accepted source build supplies the original body and retained arrow.
The finite readback gives the exact children of the supplied target rows.
Current residency retains the arrow target through canonical edge ordering.
Its reference child supplies the sole free cutoff name.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOpenBodyMetadata
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (repeatedValue)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

private theorem aligned_members {A B : Type} {relation : A → B → Prop}
    {inputs : List A} {outputs : List B} (aligned : All₂ relation inputs outputs) :
    (∀ source ∈ inputs, ∃ target ∈ outputs, relation source target) ∧
    (∀ target ∈ outputs, ∃ source ∈ inputs, relation source target) := by
  induction aligned with
  | nil => constructor <;> intro selected member <;> cases member
  | @cons source target sources targets own tail ih =>
      constructor
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨target, List.mem_cons_self, own⟩
        · obtain ⟨target, present, related⟩ := ih.1 selected later
          exact ⟨target, List.mem_cons_of_mem _ present, related⟩
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨source, List.mem_cons_self, own⟩
        · obtain ⟨source, present, related⟩ := ih.2 selected later
          exact ⟨source, List.mem_cons_of_mem _ present, related⟩

/-- Exact current-source row readback derives depth zero and the literal singleton cutoff free set. -/
theorem current_transformed_body_metadata_after_growth
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (cutoff : Nat × Nat) (targets : List (EdgeValue Symbol Guard))
    (readback : All₂ (fun (source : EdgeValue Symbol Guard) target =>
      target.children = source.children.map
        (input (replacement (.interned entry.identity) (repeatedValue cutoff))) ∧
      target.entry.key = ⟨source.entry.key.symbol,
        (source.children.map (input (replacement (.interned entry.identity)
          (repeatedValue cutoff)))).map Value.referenceOf, top⟩)
      (match body with | .node _ rows _ _ => rows | _ => []) targets)
    (resident : ∀ target ∈ targets, EdgeResident heap target) :
    maximumDepth ((canonicalEdges targets).flatMap EdgeValue.children) = 0 ∧
      childFree ((canonicalEdges targets).flatMap EdgeValue.children) = [.intersection cutoff.1 cutoff.2] := by
  obtain ⟨_bodyEntry, marker, arrow, rows, bodyEq, _bodyAvailable, markerRead, arrowChildren,
      _arrowKey, _catalog, markerClosed, _markerAvailable, _markerAtoms, kinds, arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored heap facts growth
  obtain ⟨markerEntry, markerRow, markerEq, _markerLeaf, _markerKey⟩ := markerRead
  have aligned : All₂ (fun (source : EdgeValue Symbol Guard) target =>
      target.children = source.children.map
        (input (replacement (.interned entry.identity) (repeatedValue cutoff))) ∧
      target.entry.key = ⟨source.entry.key.symbol,
        (source.children.map (input (replacement (.interned entry.identity)
          (repeatedValue cutoff)))).map Value.referenceOf, top⟩)
      (canonicalEdges (arrow :: rows)) targets := by
    cases bodyEq
    exact readback
  have members := aligned_members aligned
  have markerInput : input (replacement (.interned entry.identity) (repeatedValue cutoff)) marker = marker := by
    rw [markerEq]
    rfl
  have referenceInput : input (replacement (.interned entry.identity) (repeatedValue cutoff))
      (.reference (.interned entry.identity) : Value Symbol Guard) = repeatedValue cutoff := by
    simp [input, replacement]
  have targetChildren : ∀ target ∈ targets, ∀ child ∈ target.children,
      child = marker ∨ child = repeatedValue cutoff := by
    intro target member child present
    obtain ⟨source, included, related⟩ := members.2 target member
    rw [related.1] at present
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp present
    rcases (kinds source included).2.2 original originalMember with same | same
    · right
      rw [same]
      exact referenceInput
    · left
      rw [same.1]
      exact markerInput
  obtain ⟨arrowTarget, arrowTargetMember, arrowRead⟩ := members.1 arrow arrowRetained
  have arrowTargetChildren : arrowTarget.children = [marker, repeatedValue cutoff, repeatedValue cutoff] := by
    rw [arrowRead.1, arrowChildren]
    simp only [List.map_cons, List.map_nil, markerInput, referenceInput]
  have canonicalArrow : arrowTarget ∈ canonicalEdges targets :=
    canonicalEdges_retains heap facts.coherent targets arrowTarget resident arrowTargetMember
  have keptKinds : ∀ child ∈ (canonicalEdges targets).flatMap EdgeValue.children,
      child = marker ∨ child = repeatedValue cutoff := by
    intro child member
    obtain ⟨target, included, present⟩ := List.mem_flatMap.mp member
    exact targetChildren target (canonicalEdges_member targets target included) child present
  have zero : ∀ child ∈ (canonicalEdges targets).flatMap EdgeValue.children, child.depth = 0 := by
    intro child member
    rcases keptKinds child member with same | same
    · rw [same, markerEq]
      rfl
    · rw [same]
      rfl
  constructor
  · apply Nat.eq_zero_of_le_zero
    apply (maximumDepth_exact _ 0).mpr
    intro child member
    exact Nat.le_of_eq (zero child member)
  · unfold childFree
    apply InternedOrdinaryUnionReadback.canonicalFree_singleton _ (.intersection cutoff.1 cutoff.2)
    · refine List.mem_flatMap.mpr ⟨repeatedValue cutoff, ?_, ?_⟩
      · refine List.mem_flatMap.mpr ⟨arrowTarget, canonicalArrow, ?_⟩
        rw [arrowTargetChildren]
        simp
      · simp [repeatedValue, Value.free]
    · intro other member
      obtain ⟨child, included, named⟩ := List.mem_flatMap.mp member
      rcases keptKinds child included with same | same
      · rw [same, markerClosed] at named
        cases named
      · simpa only [same, repeatedValue, Value.free, List.mem_singleton] using named

end MicroCFTA.SourceCurrentAllocatedNativeOpenBodyMetadata

set_option warningAsError true
#check MicroCFTA.SourceCurrentAllocatedNativeOpenBodyMetadata.current_transformed_body_metadata_after_growth
#print axioms MicroCFTA.SourceCurrentAllocatedNativeOpenBodyMetadata.current_transformed_body_metadata_after_growth
