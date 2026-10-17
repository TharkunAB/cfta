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
  | nil => simp only [evaluateEdges]
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

private theorem strip_nil (names : List Reference) : stripMany names ([] : List (Value Symbol Guard)) = [] := by
  induction names with
  | nil => rfl
  | cons name rest ih => simpa only [stripMany, InternedRootAlternativeLists.remove, List.filter_nil] using ih

private theorem strip_reference (names : List Reference) (own : Reference) (selected : own ∈ names) :
    stripMany names (unionMembers (Value.reference (Symbol := Symbol) (Guard := Guard) own)) = [] := by
  have result := strip_eraseSelf names own (Value.reference (Symbol := Symbol) (Guard := Guard) own) selected
  simpa only [eraseSelf, Value.referenceOf, ↓reduceIte, unionMembers, strip_nil] using result.symm

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

private theorem strip_callback [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (own : Reference) (before rawAfter after : State Symbol Guard)
    (context : Context before environment) (argument : Available before (.reference own))
    (raw value : Value Symbol Guard)
    (rawActual : build body (.reference own :: environment) before = .done raw rawAfter)
    (filtered : run (withoutSelfReference own raw) rawAfter = (value, after))
    (actual : callback body environment own before = .done value after)
    (unused : own ∉ deepNames value) (names : List Reference)
    (outer : ∃ name, name ≠ own ∧ Value.reference name ∈ unionMembers raw) :
    stripMany names (unionMembers (eraseSelf own value)) =
      stripMany (own :: names) (unionMembers raw) := by
  have returned := callback_result body environment own before context argument value after actual unused
  have removed := strip_absent [own] (eraseSelf own value) after returned.1.normal returned.2.1
    (by intro name member; have same := List.mem_singleton.mp member; exact same ▸ returned.2.2)
  have removeErased : InternedRootAlternativeLists.remove own (unionMembers (eraseSelf own value)) =
      unionMembers (eraseSelf own value) := by
    simpa only [stripMany] using removed
  have rawContext : Context rawAfter (.reference own :: environment) := by
    simpa only [rawActual, Outcome.state] using (context.local own argument).build body
  have rawAvailable := (build_verified body _ before context.normal.facts
    (context.local own argument).inputs).result raw rawAfter rawActual
  calc
    stripMany names (unionMembers (eraseSelf own value)) =
        stripMany (own :: names) (unionMembers (eraseSelf own value)) := by
      rw [stripMany, removeErased]
    _ = stripMany (own :: names) (unionMembers value) :=
      strip_eraseSelf (own :: names) own value List.mem_cons_self
    _ = stripMany (own :: names) (unionMembers raw) := by
      have result := SourceCurrentNativeStrippedFilter.filter (own :: names) own raw rawAfter
        rawContext.normal rawAvailable List.mem_cons_self outer
      simpa only [filtered] using result

end MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
