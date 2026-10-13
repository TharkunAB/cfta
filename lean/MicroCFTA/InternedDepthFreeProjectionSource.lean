import MicroCFTA.InternedDepthFreeProjection
import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.InternedDeepFreeNormalization

/-!
# Actual literal-environment free and ordinary-root deep observations

The full repaired executor supplies its existing profile and free-name
heap proofs. Ordinary-root deep observations follow without a recursive
depth/deep observation premise, even when children contain nested binders.
Cached-depth and general binder-heap correspondence remain separate.
-/
namespace MicroCFTA.InternedDepthFreeProjectionSource
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildEdges)
open InternedFreshOrdinaryContext
open InternedDepthSemantics (Shape evaluate)
open InternedBinderProtocol (Reference)

/-- A literal source reference has one root occurrence and no deep occurrence. -/
def literal (name : Atom) : Shape Atom := ⟨[name], [], false, 0⟩

/-- Every literal environment satisfies the pure shape representation condition. -/
theorem literals_coherent (names : List Atom) :
    InternedDepthSemanticProjections.CoherentMany (names.map literal) := by
  intro shape member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  intro _
  rfl

/-- Actual full source execution has the free-name set of its richer shape interpretation. -/
theorem build_free [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) :
    InternedFreshOrdinaryFreeRequest.Checked (build expression (names.map Value.reference) state)
      (fun value => ∀ name, name ∈ value.free ↔ name ∈ (evaluate expression (names.map literal)).free) := by
  have checked := InternedFreshOrdinaryFreeNames.build_free expression (names.map Value.reference) state
    context.normal context.inputs context.freeNames context.profiles
  refine ⟨checked.heap, ?_⟩
  intro value after completed name
  have actual := checked.result value after completed name
  have pure := InternedDepthFreeProjection.evaluate_member expression (names.map literal) (literals_coherent names) name
  apply actual.trans
  simpa only [List.map_map, Function.comp_def, literal, InternedRootProfile.profile,
    InternedDepthSemanticProjections.profile, Bool.false_eq_true, ↓reduceIte,
    Shape.free, List.append_nil, Value.free] using pure.symm

/-- A completed ordinary source root has no bare-reference contribution to its free names. -/
theorem node_deep_eq_free [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (value : Value Symbol Guard) (after : State Symbol Guard)
    (completed : build (.node edges) environment state = .done value after) :
    InternedDeepFreeDepth.deepNames value = value.free := by
  have verified := InternedFreshOrdinaryFacts.buildEdges_verified edges environment state context.normal.facts context.inputs
  have retained := context.edges edges
  rw [build] at completed
  cases built : buildEdges edges environment state with
  | pending key stopped => simp only [built, Outcome.bind] at completed; cases completed
  | done values beforeNode =>
    have beforeContext : Context beforeNode environment := by simpa only [built, Outcome.state] using retained
    have available := verified.result values beforeNode built
    have deep := InternedDeepFreeNormalization.makeNode_deep values beforeNode
      beforeContext.normal.facts.coherent beforeContext.normal.facts.linked available
    simp only [built, Outcome.bind, work, Outcome.done.injEq] at completed
    rw [←completed.1]
    exact deep

/-- An ordinary root's deep names are derived for arbitrary full nested child syntax. -/
theorem node_deep [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeSyntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (value : Value Symbol Guard) (after : State Symbol Guard)
    (completed : build (.node edges) (names.map Value.reference) state = .done value after) (name : Reference) :
    name ∈ InternedDeepFreeDepth.deepNames value ↔ name ∈ (evaluate (.node edges) (names.map literal)).deep := by
  rw [node_deep_eq_free edges _ state context value after completed]
  have free := (build_free (.node edges) names state context).result value after completed name
  simpa only [evaluate, Shape.free, InternedDepthSemanticProjections.edges_roots, List.nil_append] using free

/-- Actual callback filtering retains the derived deep names of an ordinary-root body. -/
theorem callback_node_deep [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeSyntax Symbol Guard))
    (names : List Reference) (argument : Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (available : Available state (.reference argument))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (completed : InternedFreshOrdinaryFacts.callback (.node edges) (names.map Value.reference) argument state = .done value after)
    (name : Reference) :
    name ∈ InternedDeepFreeDepth.deepNames value ↔
      name ∈ (evaluate (.node edges) ((argument :: names).map literal)).deep := by
  have localContext := context.local argument available
  have verified := InternedFreshOrdinaryFacts.build_verified (.node edges) _ state localContext.normal.facts localContext.inputs
  have retained := localContext.build (.node edges)
  unfold InternedFreshOrdinaryFacts.callback at completed
  cases built : build (.node edges) (.reference argument :: names.map Value.reference) state with
  | pending key stopped => simp only [built, Outcome.bind] at completed; cases completed
  | done body beforeFilter =>
    have beforeContext : Context beforeFilter (.reference argument :: names.map Value.reference) := by
      simpa only [built, Outcome.state] using retained
    have bodyAvailable := verified.result body beforeFilter built
    simp only [built, Outcome.bind, work, Outcome.done.injEq] at completed
    rw [←completed.1, InternedDeepFreeNormalization.filter_deep argument name body beforeFilter beforeContext.normal bodyAvailable]
    exact node_deep edges (argument :: names) state localContext body beforeFilter built name

end MicroCFTA.InternedDepthFreeProjectionSource
