import MicroCFTA.SourceCurrentNativeNormalizedComparisonUnion
import MicroCFTA.SourceCurrentNativeNormalizedErasure
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentNativeRequestProbes

/-!
# Actual normalized source comparison and causal Mu payloads

The source comparison uses a pure law of the common record table. The
publication-history induction establishes that law before each new write.
-/
set_option maxHeartbeats 1600000
namespace MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedDeepFreeDepth InternedDepthSemantics InternedStoredMuOrigins
open SourceCurrentNativeNormalizedComparison SourceCurrentNativeNormalizedComparisonFinite
open SourceCurrentNativeNormalizedComparisonInactive SourceCurrentNativeNormalizedErasure
open SourceCurrentNativeStrippedAlternatives SourceCurrentNativeCallbackErasure
open SourceCurrentNativeNormalizationInputs (support)
open InternedBinderProtocol (Reference NodeKey)
variable {Atom : Type}

private def MuLaw (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false →
    finish true (.mu entry body depth ordinary) = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary

private def MuHeap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    MuLaw entry body depth ordinary

private theorem roots_edges (edges : List (InternedNestedConstruction.EdgeSyntax Symbol Guard))
    (environment : List (Shape Label)) : (evaluateEdges edges environment).roots = [] := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      cases edge with
      | mk symbol guard children =>
          simp only [evaluateEdges, combine, ih]
          unfold InternedDepthSemantics.edge
          split <;> rfl

private theorem empty_compared [DecidableEq (EdgeKey Symbol Guard)]
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (normal : Normal common) : Compared .empty inputs atoms firstNames secondNames common := by
  apply inactive_compared .empty inputs atoms firstNames secondNames common normal
  intro atom member
  simp only [support, InternedFreeNameSemantics.evaluate, List.not_mem_nil] at member

private theorem strip_reference (names : List Reference) (own : Reference) (selected : own ∈ names) :
    stripMany names (unionMembers (Value.reference (Symbol := Symbol) (Guard := Guard) own)) = [] := by
  have result := strip_eraseSelf names own (Value.reference (Symbol := Symbol) (Guard := Guard) own) selected
  simpa only [eraseSelf, Value.referenceOf, ↓reduceIte, unionMembers] using result.symm

private theorem var_compared [DecidableEq (EdgeKey Symbol Guard)]
    (index : Nat) (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (normal : Normal common) (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms) :
    Compared (.var index) inputs atoms firstNames secondNames common := by
  cases found : inputs[index]? with
  | none =>
      apply inactive_compared (.var index) inputs atoms firstNames secondNames common normal
      intro atom member
      simp [support, InternedFreeNameSemantics.evaluate, List.getElem?_map, found] at member
  | some selected =>
      cases selected with
      | inl value =>
          apply inactive_compared (.var index) inputs atoms firstNames secondNames common normal
          intro atom member
          simp [support, InternedFreeNameSemantics.evaluate, List.getElem?_map, found,
            SourceCurrentNativeNormalizationInputs.inputNames] at member
      | inr atom =>
          intro before later after final _context _laterContext _heap _laterHeap first second
            leftActual rightActual _growth _laterGrowth _history _laterHistory _leftFresh _rightFresh _shallow
          have selected := covered atom (List.mem_of_getElem? found)
          simp only [build, List.getElem?_map, found, Option.map_some, Option.getD_some, input,
            Outcome.done.injEq] at leftActual rightActual
          rw [← leftActual.1, ← rightActual.1,
            strip_reference _ _ (List.mem_map.mpr ⟨atom, selected, rfl⟩),
            strip_reference _ _ (List.mem_map.mpr ⟨atom, selected, rfl⟩)]

private theorem node_compared [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (InternedNestedConstruction.EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (normal : Normal common) (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms) :
    Compared (.node edges) inputs atoms firstNames secondNames common := by
  intro before later after final context laterContext heap laterHeap first second
    leftActual rightActual growth laterGrowth history laterHistory leftFresh rightFresh shallow
  by_cases live : ∃ atom, .inr atom ∈ support (.node edges) inputs
  · obtain ⟨atom, supported⟩ := live
    have selected := covered atom (support_varying_member (.node edges) inputs atom supported)
    have root := active_roots (.node edges) inputs firstNames before after context heap first leftActual
      atom supported (shallow atom selected)
    simp only [symbolic, evaluate, roots_edges, List.not_mem_nil] at root
  · exact inactive_compared (.node edges) inputs atoms firstNames secondNames common normal
      (fun atom member => live ⟨atom, member⟩) before later after final context laterContext heap laterHeap
      first second leftActual rightActual growth laterGrowth history laterHistory leftFresh rightFresh shallow

end MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
