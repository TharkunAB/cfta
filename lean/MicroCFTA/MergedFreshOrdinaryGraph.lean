import MicroCFTA.MergedFreshOrdinaryColdReplay
import MicroCFTA.MergedSourceExposureCoverage

/-!
# The actual repaired physical epsilon graph

Union references follow their stored members. Mu references follow the
actual repaired stored executor. Constructor rows retain source symbols,
guards, and ordered physical children. Cache-independent source meaning
remains a separate correspondence target.
-/
namespace MicroCFTA.MergedFreshOrdinaryGraph
open InternedConstructorTemplates InternedNestedProvenance
open Language Productivity

/-- Follow actual repaired stored unfolding and explicit union alternatives. -/
def successors [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) :
    Value Symbol Guard → List (Value Symbol Guard)
  | .union _ members _ _ => members
  | value@(.mu ..) =>
      match InternedFreshOrdinaryStoredSubstitution.unfold value state with
      | .done result _ => [result]
      | .pending .. => []
  | _ => []

/-- Read complete guards and child order from actual constructor records. -/
def graph [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) : EpsilonUnion.Graph (Value Symbol Guard) Symbol :=
  ⟨successors state, MergedPhysicalComparison.constructorRows meaning⟩

/-- An original constructor edge is reachable through actual repaired epsilon steps. -/
def Origin [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (roots : List (Value Symbol Guard)) (edge : EdgeValue Symbol Guard) : Prop :=
  ∃ value, Reachable (successors state) roots value ∧ edge ∈ InternedEdgeResidency.nodeEdges value

/-- Replacing seeds by known repaired paths preserves each constructor origin. -/
theorem Origin.from_seeds [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (before after : List (Value Symbol Guard)) (included : ∀ value ∈ before, Reachable (successors state) after value)
    (edge : EdgeValue Symbol Guard) (origin : Origin state before edge) : Origin state after edge := by
  obtain ⟨value, reached, member⟩ := origin
  exact ⟨value, EpsilonUnion.change_seeds _ before after included value reached, member⟩

/-- A complete source edge accepts its ordered child terms and its full guard. -/
def EdgeAccepts [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) (term : Term Symbol) : Prop :=
  ∃ terms, term = .node edge.entry.key.symbol terms ∧
    All₂ (EpsilonUnion.Accepts (graph view meaning)) edge.children terms ∧
    meaning edge.entry.key.constraint term = true

/-- Literal EmptyNode has no finite accepting run. -/
theorem empty_rejects [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    ¬ EpsilonUnion.Accepts (graph view meaning) .empty term := by
  intro accepted
  cases accepted with
  | reference member => simp [graph, successors] at member
  | node edge children member => simp [graph, MergedPhysicalComparison.constructorRows] at member

/-- An ordinary complete record accepts exactly one of its stored edges. -/
theorem node_exact [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (term : Term Symbol) :
    EpsilonUnion.Accepts (graph view meaning) (.node entry edges depth free) term ↔
      ∃ edge ∈ edges, EdgeAccepts view meaning edge term := by
  constructor
  · intro accepted
    cases accepted with
    | reference member => simp [graph, successors] at member
    | node edge terms member subtrees guard =>
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact ⟨original, present, terms, rfl, subtrees, guard⟩
  · rintro ⟨edge, member, terms, rfl, subtrees, guard⟩
    exact .node ⟨edge.entry.key.symbol, edge.children, meaning edge.entry.key.constraint⟩ terms
      (List.mem_map.mpr ⟨edge, member, rfl⟩) subtrees guard


end MicroCFTA.MergedFreshOrdinaryGraph
