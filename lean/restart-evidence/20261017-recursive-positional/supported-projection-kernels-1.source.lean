import MicroCFTA.SourceCurrentConstrainedCapSupportedProjection

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace SupportedProjectionChecks
open MicroCFTA
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredHead
open SourceEqualityProjectionGraph SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPaths (Supported ForestSupported)
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}

/-- The cap wrapper is two literal constructor requests with their exact intermediate heap. -/
def Wrap [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  ∃ edge middle, run (makeEdge symbol guard [value]) before = (edge, middle) ∧
    run (makeNode [edge]) middle = (result, after)

private theorem wrap [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (symbol : Symbol) (guard : Guard) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = [])
    (stored : MuStored valid before) (bounded : Cap valid depth value) :
    ∃ result after, Wrap symbol guard value before result after ∧ Keeps before after ∧ SemanticReady after ∧
      Available after result ∧ result.free = [] ∧ MuStored valid after ∧ Cap valid (depth + 1) result := by
  have inputs : Values before [value] := fun child member => (List.mem_singleton.mp member) ▸ available
  let edge := (run (makeEdge symbol guard [value]) before).1
  let middle := (run (makeEdge symbol guard [value]) before).2
  have edgeEffects := SourceEqualityRequiredCache.edge symbol guard [value] before semantic.ready inputs
  have edgeSemantic := SourceEqualityRequiredSemanticCache.edge symbol guard [value] before semantic inputs
  have middleStored : MuStored valid middle := stored.makeEdge symbol guard [value]
  have edgeBound : SourceCurrentConstrainedCap.Edge valid (depth + 1) edge :=
    SourceCurrentConstrainedCap.makeEdge valid (depth + 1) symbol guard [value] before
      semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.cached inputs
      (by intro zero; omega) (by intro child member; simpa only [Nat.add_sub_cancel] using (List.mem_singleton.mp member) ▸ bounded)
  have resident : Edges middle [edge] := fun row member => (List.mem_singleton.mp member) ▸ edgeEffects.2.1
  have edgeClosed : ClosedEdges [edge] := by
    intro row member child inside
    cases List.mem_singleton.mp member
    rw [edgeEffects.2.2] at inside
    exact (List.mem_singleton.mp inside) ▸ closed
  have nodeEffects := SourceEqualityRequiredCache.node [edge] middle edgeEffects.1.ready resident edgeClosed
  have nodeSemantic := SourceEqualityRequiredSemanticCache.node [edge] middle edgeSemantic resident edgeClosed
  have resultBound := SourceCurrentConstrainedCap.makeNode valid (depth + 1) [edge] middle
    edgeSemantic.ready.semantic.1.normal.facts.coherent edgeSemantic.ready.semantic.1.normal.facts.linked resident
    (fun row member => (List.mem_singleton.mp member) ▸ edgeBound)
  exact ⟨_, _, ⟨edge, middle, rfl, rfl⟩, edgeEffects.1.trans nodeEffects.1, nodeSemantic,
    nodeEffects.2.1, nodeEffects.2.2.1, middleStored.makeNode [edge], resultBound⟩

/-- A short path enters a plain Mu despite an independently built deeper constrained branch. -/
theorem short_recursive_endpoint [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (symbol : Symbol) (guard : Guard) (entry) (body depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before (.mu entry body depth ordinary))
    (closed : (Value.mu entry body depth ordinary : Value Symbol Guard).free = [])
    (bodyPlain : Annotated valid body) (stored : MuStored valid before) :
    ∃ inner middle cap capState result after,
      Wrap symbol guard (.mu entry body depth ordinary) before inner middle ∧
      Wrap symbol guard inner middle cap capState ∧
      Cap valid 2 cap ∧
      Forest [1, 0] [cap, .mu entry body depth ordinary] capState result after ∧
      (∃ exposed headState, Head (.mu entry body depth ordinary) capState exposed headState ∧
        Project [0] exposed headState result after) ∧
      MuStored valid after ∧ Annotated valid result := by
  let atom : Value Symbol Guard := .mu entry body depth ordinary
  have atomPlain : Annotated valid atom := .mu entry body depth ordinary bodyPlain
  obtain ⟨inner, middle, firstWrap, firstKeeps, firstSemantic, firstAvailable, firstClosed, firstStored, firstBound⟩ :=
    wrap valid 0 symbol guard atom before semantic available closed stored (.plain 0 atomPlain)
  obtain ⟨cap, capState, secondWrap, secondKeeps, secondSemantic, capAvailable, capClosed, capStored, capBound⟩ :=
    wrap valid 1 symbol guard inner middle firstSemantic firstAvailable firstClosed firstStored firstBound
  have atomAvailable : Available capState atom := secondKeeps.available atom (firstKeeps.available atom available)
  have inputs : Values capState [cap, atom] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact capAvailable
    · exact (List.mem_singleton.mp later) ▸ atomAvailable
  have inputClosed : ClosedValues [cap, atom] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact capClosed
    · exact (List.mem_singleton.mp later) ▸ closed
  have mask : ForestSupported valid [1, 0] [cap, atom] := by
    intro value found
    have same : atom = value := by simpa [select] using found
    cases same
    exact .plain [0] atomPlain
  obtain ⟨result, after, actual, _, _, _, _, afterStored, resultPlain⟩ :=
    SourceCurrentConstrainedCapSupportedProjection.forest_complete valid [1, 0] [cap, atom] capState
      secondSemantic inputs inputClosed capStored mask
  have entered : ∃ exposed headState, Head atom capState exposed headState ∧ Project [0] exposed headState result after := by
    cases actual with
    | missing absent => simp [select] at absent
    | selected found projected =>
        have same : atom = _ := by simpa [select] using found
        cases same
        cases projected with
        | recursive recursive head remaining => exact ⟨_, _, head, remaining⟩
  exact ⟨inner, middle, cap, capState, result, after, firstWrap, secondWrap, capBound,
    actual, entered, afterStored, resultPlain⟩

end SupportedProjectionChecks

#print axioms SupportedProjectionChecks.Wrap
#check @SupportedProjectionChecks.Wrap
#print axioms SupportedProjectionChecks.short_recursive_endpoint
#check @SupportedProjectionChecks.short_recursive_endpoint
