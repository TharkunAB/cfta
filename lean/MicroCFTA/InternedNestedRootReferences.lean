import MicroCFTA.InternedNestedRootLabels
import MicroCFTA.InternedNormalizationFree

/-!
# Dedicated source reference edges survive actual nested construction

A unary variable edge is live when its input is a recursive reference.
Canonical edge sorting, deduplication, and node readback retain its free
name. Other source edges can contain arbitrary nested computations.
-/
namespace MicroCFTA.InternedNestedRootReferences
open InternedConstructorTemplates InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency InternedNormalizationFree
open InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeRef)

/-- A successful edge traversal retains the exact child reference of every declared unary variable edge. -/
theorem buildEdges_reference [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (edges : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (completed : buildEdges expressions environment state = .done edges final)
    (symbol : Symbol) (constraint : Guard) (index : Nat)
    (declared : .mk symbol constraint [.var index] ∈ expressions) :
    ∃ edge ∈ edges, edge.children.map Value.referenceOf = [(environment[index]?.getD .empty).referenceOf] := by
  cases expressions with
  | nil => cases declared
  | cons first rest =>
      cases first with
      | mk own guard children =>
          have childVerified := buildMany_verified children environment state facts inputs
          cases childResult : buildMany children environment state with
          | pending key after => simp [buildEdges, childResult, Outcome.bind] at completed
          | done values after =>
              have afterFacts : Facts after := by simpa only [childResult, Outcome.state] using childVerified.facts
              have available := childVerified.result values after childResult
              have edgeVerified := edge_verified own guard values after afterFacts available
              let firstResult := run (makeEdge own guard values) after
              have firstFacts : Facts firstResult.2 := edgeVerified.facts
              have laterInputs : Values firstResult.2 environment := by
                intro value member
                have intermediate : Available after value := by
                  simpa only [childResult, Outcome.state] using childVerified.available value (inputs value member)
                exact edgeVerified.available value intermediate
              simp only [buildEdges, childResult, Outcome.bind, work] at completed
              change (buildEdges rest environment firstResult.2).bind _ = _ at completed
              cases restResult : buildEdges rest environment firstResult.2 with
              | pending key later => simp [restResult, Outcome.bind] at completed
              | done remaining later =>
                  simp only [restResult, Outcome.bind, Outcome.done.injEq] at completed
                  obtain ⟨rfl, rfl⟩ := completed
                  rcases List.mem_cons.mp declared with same | inRest
                  · cases same
                    have original : [(environment[index]?.getD .empty)] = values ∧ state = after := by
                      simpa only [buildMany, build, Outcome.bind, Outcome.done.injEq] using childResult
                    have refs := InternedErasedEdgeReplay.makeEdge_references symbol constraint values after afterFacts.coherent
                    exact ⟨firstResult.1, List.mem_cons_self, by simpa only [firstResult, ← original.1, List.map_cons, List.map_nil] using refs⟩
                  · obtain ⟨edge, member, refs⟩ := buildEdges_reference rest environment firstResult.2 firstFacts laterInputs
                      remaining later restResult symbol constraint index inRest
                    exact ⟨edge, List.mem_cons_of_mem _ member, refs⟩
termination_by expressions.length

/-- A dedicated reference edge survives normalization and contributes its name to actual node metadata. -/
theorem makeNode_reference [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : Edges state edges)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (name : Reference)
    (refs : edge.children.map Value.referenceOf = [.ref name]) :
    name ∈ (run (makeNode edges) state).1.free := by
  have live : edge.children.any (fun child => child.referenceOf == .empty) = false := by
    apply List.any_eq_false.mpr
    intro child included
    have selected : child.referenceOf ∈ [.ref name] := refs ▸ List.mem_map.mpr ⟨child, included, rfl⟩
    have same : child.referenceOf = .ref name := by simpa using selected
    simp [same]
  have survives : edge ∈ surviving edges := by simp [surviving, member, live]
  have selected := canonicalEdges_retains state facts.coherent (surviving edges) edge
    (fun current present => resident current (List.mem_filter.mp present).1) survives
  have self : NodeRef.ref name ∈ edge.children.map Value.referenceOf := by rw [refs]; simp
  obtain ⟨child, included, same⟩ := List.mem_map.mp self
  have childSame := (referenceOf_self_iff name child).mp same
  rw [makeNode_free edges state facts.coherent facts.linked resident]
  exact (childFree_member _ name).mpr ⟨child, List.mem_flatMap.mpr ⟨edge, selected, included⟩,
    by simp [childSame, Value.free]⟩

/-- A declared unary variable edge establishes actual free-reference retention after the full source body runs. -/
theorem build_node_reference [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : build (.node expressions) environment state = .done value final)
    (symbol : Symbol) (constraint : Guard) (index : Nat) (name : Reference)
    (declared : .mk symbol constraint [.var index] ∈ expressions)
    (lookup : environment[index]?.getD .empty = .reference name) : name ∈ value.free := by
  have verified := buildEdges_verified expressions environment state facts inputs
  cases produced : buildEdges expressions environment state with
  | pending key after => simp [build, produced, Outcome.bind] at completed
  | done edges after =>
      have afterFacts : Facts after := by simpa only [produced, Outcome.state] using verified.facts
      have resident := verified.result edges after produced
      obtain ⟨edge, member, refs⟩ := buildEdges_reference expressions environment state facts inputs edges after produced
        symbol constraint index declared
      rw [lookup] at refs
      have retained := makeNode_reference edges after afterFacts resident edge member name refs
      simp only [build, produced, Outcome.bind, work, Outcome.done.injEq] at completed
      exact completed.1 ▸ retained

/-- Actual ordinary-node output is either empty or an ordinary record, so root self filtering has no effect. -/
theorem makeNode_filter [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : Edges state edges)
    (name : Reference) (after : State Symbol Guard) :
    run (withoutSelfReference name (run (makeNode edges) state).1) after = ((run (makeNode edges) state).1, after) := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · rfl
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa only [same] using selected)
    simp only [run, readback, identifyNode, withoutSelfReference]

/-- Every successful source node body passes through self filtering without changing its value or state. -/
theorem build_node_filter [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : build (.node expressions) environment state = .done value final)
    (name : Reference) (after : State Symbol Guard) : run (withoutSelfReference name value) after = (value, after) := by
  have verified := buildEdges_verified expressions environment state facts inputs
  cases produced : buildEdges expressions environment state with
  | pending key later => simp [build, produced, Outcome.bind] at completed
  | done edges later =>
      have laterFacts : Facts later := by simpa only [produced, Outcome.state] using verified.facts
      have result := makeNode_filter edges later laterFacts (verified.result edges later produced) name after
      simp only [build, produced, Outcome.bind, work, Outcome.done.injEq] at completed
      exact completed.1 ▸ result

end MicroCFTA.InternedNestedRootReferences
