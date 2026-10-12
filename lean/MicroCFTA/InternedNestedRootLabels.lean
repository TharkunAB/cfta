import MicroCFTA.InternedNestedProvenance
import MicroCFTA.InternedErasedEdgeReplay

/-!
# Preserved source root markers in nested constructor execution

Successful edge construction retains its source symbol and arity.
A nullary marker edge survives node normalization. Complete canonical
readback therefore exposes the same marker on the resulting node.
-/
namespace MicroCFTA.InternedNestedRootLabels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedFreshProbeKeys

/-- The complete source edge signature includes its symbol and actual child count. -/
def signature (edge : EdgeValue Symbol Guard) : Symbol × Nat := (edge.entry.key.symbol, edge.children.length)

/-- The source syntax fixes each edge's symbol and ordered child count before execution. -/
def declared : EdgeSyntax Symbol Guard → Symbol × Nat
  | .mk symbol _ children => (symbol, children.length)

/-- Canonical edge readback retains both its requested source symbol and child arity. -/
theorem makeEdge_signature [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) :
    signature (run (makeEdge symbol constraint values) state).1 = (symbol, values.length) := by
  have correct := edgeStep_correct ⟨symbol, values.map Value.referenceOf, constraint⟩
    (fun entry => .mk entry values) state coherent.valid
  have after := edgeStep_coherent ⟨symbol, values.map Value.referenceOf, constraint⟩
    (fun entry => .mk entry values) state coherent (fun _ key => ⟨rfl, key, rfl⟩)
  have fields := (after.edges _ _ correct.2.2).2
  apply Prod.ext
  · exact congrArg EdgeKey.symbol fields.1
  · simpa only [signature, makeEdge, run, List.length_map] using congrArg List.length fields.2

/-- Child execution returns exactly one record for each original child expression. -/
theorem buildMany_length [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (values : List (Value Symbol Guard))
    (final : State Symbol Guard) (completed : buildMany expressions environment state = .done values final) :
    values.length = expressions.length := by
  cases expressions with
  | nil =>
      simp only [buildMany, Outcome.done.injEq] at completed
      obtain ⟨rfl, rfl⟩ := completed
      rfl
  | cons first rest =>
      simp only [buildMany] at completed
      cases head : build first environment state with
      | pending key after => simp [head, Outcome.bind] at completed
      | done value after =>
          simp only [head, Outcome.bind] at completed
          cases tail : buildMany rest environment after with
          | pending key later => simp [tail] at completed
          | done remaining later =>
              simp only [tail, Outcome.done.injEq] at completed
              obtain ⟨rfl, rfl⟩ := completed
              exact congrArg Nat.succ (buildMany_length rest environment after remaining later tail)
termination_by expressions.length

/-- Actual returned edge signatures match the source edge declarations in order. -/
theorem buildEdges_signatures [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (edges : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (completed : buildEdges expressions environment state = .done edges final) :
    edges.map signature = expressions.map declared := by
  cases expressions with
  | nil =>
      simp only [buildEdges, Outcome.done.injEq] at completed
      obtain ⟨rfl, rfl⟩ := completed
      rfl
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges] at completed
          have childrenVerified := buildMany_verified children environment state facts inputs
          cases childrenResult : buildMany children environment state with
          | pending key after => simp [childrenResult, Outcome.bind] at completed
          | done values after =>
              have afterFacts : Facts after := by simpa only [childrenResult, Outcome.state] using childrenVerified.facts
              have valuesAvailable := childrenVerified.result values after childrenResult
              have edgeVerified := edge_verified symbol constraint values after afterFacts valuesAvailable
              let edge := run (makeEdge symbol constraint values) after
              have edgeFacts : Facts edge.2 := edgeVerified.facts
              have laterInputs : Values edge.2 environment := by
                intro value member
                have available : Available after value := by
                  simpa only [childrenResult, Outcome.state] using childrenVerified.available value (inputs value member)
                exact edgeVerified.available value available
              simp only [childrenResult, Outcome.bind, work] at completed
              cases restResult : buildEdges rest environment edge.2 with
              | pending key later =>
                  change (buildEdges rest environment edge.2).bind _ = _ at completed
                  simp [restResult, Outcome.bind] at completed
              | done remaining later =>
                  change (buildEdges rest environment edge.2).bind _ = _ at completed
                  simp only [restResult, Outcome.bind, Outcome.done.injEq] at completed
                  obtain ⟨rfl, rfl⟩ := completed
                  have headSignature := makeEdge_signature symbol constraint values after afterFacts.coherent
                  have arity := buildMany_length children environment state values after childrenResult
                  have tailSignature := buildEdges_signatures rest environment edge.2 edgeFacts laterInputs remaining later restResult
                  simp only [List.map_cons, declared]
                  rw [headSignature, arity, tailSignature]
termination_by expressions.length

/-- A root marker is visible in a nonempty ordinary node's complete canonical edge payloads. -/
def Root (marker : Symbol) : Value Symbol Guard → Prop
  | .node _ edges _ _ => edges ≠ [] ∧ ∀ edge ∈ edges, edge.entry.key.symbol = marker
  | _ => False

/-- One complete ordinary record cannot have two different root markers. -/
theorem root_unique (value : Value Symbol Guard) (first second : Symbol)
    (left : Root first value) (right : Root second value) : first = second := by
  cases value <;> simp only [Root] at left right
  case node entry edges depth free =>
    cases edges with
    | nil => exact False.elim (left.1 rfl)
    | cons edge rest => exact (left.2 edge List.mem_cons_self).symm.trans (right.2 edge List.mem_cons_self)
  all_goals contradiction

/-- A declared marker has at least one nullary edge, and every root edge uses its exact symbol. -/
def Marked (marker : Symbol) (edges : List (EdgeSyntax Symbol Guard)) : Prop :=
  (marker, 0) ∈ edges.map declared ∧ ∀ signature ∈ edges.map declared, signature.1 = marker

/-- A nullary marker survives empty-child removal, canonical sorting, and complete node readback. -/
theorem makeNode_root [DecidableEq (EdgeKey Symbol Guard)] (marker : Symbol)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (resident : Edges state edges)
    (nullary : ∃ edge ∈ edges, edge.children = [])
    (symbols : ∀ edge ∈ edges, edge.entry.key.symbol = marker) : Root marker (run (makeNode edges) state).1 := by
  obtain ⟨witness, present, noChildren⟩ := nullary
  have survives : witness ∈ surviving edges := by simp [surviving, present, noChildren]
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have kept := canonicalEdges_retains state facts.coherent (surviving edges) witness
    (fun edge member => resident edge (List.mem_filter.mp member).1) survives
  unfold makeNode
  dsimp only
  split
  · rename_i none
    simp [none] at kept
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa only [same] using selected)
    simp only [run, readback, identifyNode, Root]
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    intro edge member
    exact symbols edge (List.mem_filter.mp (canonicalEdges_member (surviving edges) edge (by simpa only [same] using member))).1

/-- Successful execution of a marked source body exposes its declared marker in the actual complete root. -/
theorem build_marked_root [DecidableEq (EdgeKey Symbol Guard)] (marker : Symbol)
    (expressions : List (EdgeSyntax Symbol Guard)) (marked : Marked marker expressions)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : build (.node expressions) environment state = .done value final) : Root marker value := by
  have verified := buildEdges_verified expressions environment state facts inputs
  cases produced : buildEdges expressions environment state with
  | pending key after => simp [build, produced, Outcome.bind] at completed
  | done edges after =>
      have afterFacts : Facts after := by simpa only [produced, Outcome.state] using verified.facts
      have resident := verified.result edges after produced
      have signatures := buildEdges_signatures expressions environment state facts inputs edges after produced
      have nullary : ∃ edge ∈ edges, edge.children = [] := by
        obtain ⟨edge, member, same⟩ := List.mem_map.mp (signatures.symm ▸ marked.1)
        refine ⟨edge, member, List.eq_nil_of_length_eq_zero ?_⟩
        exact congrArg Prod.snd same
      have symbols : ∀ edge ∈ edges, edge.entry.key.symbol = marker := by
        intro edge member
        exact marked.2 (signature edge) (signatures ▸ List.mem_map.mpr ⟨edge, member, rfl⟩)
      have root := makeNode_root marker edges after afterFacts resident nullary symbols
      simp only [build, produced, Outcome.bind, work, Outcome.done.injEq] at completed
      exact completed.1 ▸ root

/-- The current self-union filter leaves an actual marked ordinary root and state unchanged. -/
theorem root_filter [DecidableEq (EdgeKey Symbol Guard)] (marker : Symbol) (value : Value Symbol Guard)
    (root : Root marker value) (name : InternedBinderProtocol.Reference) (state : State Symbol Guard) :
    run (withoutSelfReference name value) state = (value, state) := by
  cases value <;> simp only [Root] at root <;> try contradiction
  rfl

/-- Distinct declared root markers force distinct exact Mu keys through canonical resident readback. -/
theorem marked_keys_different (state : State Symbol Guard) (facts : Facts state)
    (firstMarker secondMarker : Symbol) (different : firstMarker ≠ secondMarker)
    (firstDepth firstOrdinary secondDepth secondOrdinary : Value Symbol Guard)
    (firstResident : Resident state firstDepth) (secondResident : Resident state secondDepth)
    (firstRoot : Root firstMarker firstDepth) (secondRoot : Root secondMarker secondDepth) :
    muKey firstDepth firstOrdinary ≠ muKey secondDepth secondOrdinary := by
  intro same
  have references : firstDepth.referenceOf = secondDepth.referenceOf ∧ firstOrdinary.referenceOf = secondOrdinary.referenceOf := by
    simpa [muKey, InternedBinderProtocol.MuKey.mk.injEq] using same
  have equal := resident_reference_injective state facts.coherent firstDepth secondDepth firstResident secondResident references.1
  exact different (root_unique secondDepth firstMarker secondMarker (equal ▸ firstRoot) secondRoot)

end MicroCFTA.InternedNestedRootLabels
