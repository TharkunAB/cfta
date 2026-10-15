import MicroCFTA.SourceMergedColumnCompletion

/-!
# Stable finite general merge rows

Small rows complete each child in order. Large rows complete each actual
filtered column in order. Literal edge construction then retains the
complete closed child payload and all actual semantic cache effects.
-/
namespace MicroCFTA.SourceMergedEdgeCompletion
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedColdMerge (Action small)
open MergedOrdinaryHeight
open SourceMergedCompleteEffects SourceMergedColumnCompletion
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Small rows have stable finite execution after every actual smaller child call. -/
theorem small_complete (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (smaller : ∀ value, height value ≤ limit → ∀ before, SemanticReady before → Available before value → value.free = [] →
      Complete (fun fuel => recurse fuel value) before ValueReady)
    (edge : EdgeValue Symbol Guard) (bounded : ∀ value ∈ edge.children, height value ≤ limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (ready : EdgeReady before edge) :
    Complete (fun fuel => small (recurse fuel) edge) before EdgeReady := by
  have children := map_complete recurse ValueReady ValueReady value_grows value_grows edge.children
    (fun value member state semantic input => smaller value (bounded value member) state semantic input.1 input.2)
    before semantic (fun value member => ⟨semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge ready.1 value member, ready.2 value member⟩)
  apply bind_complete _ _ before _ EdgeReady children
  intro values after effects available
  exact edge_complete edge.entry.key.symbol edge.entry.key.constraint values after effects.2 available

/-- Large rows have stable finite execution through the actual repaired ordered columns. -/
theorem large_complete [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat) (clear : Guard → Bool) (top : Guard)
    (smaller : ∀ value, height value ≤ limit → ∀ before, SemanticReady before → Available before value → value.free = [] →
      Complete (fun fuel => recurse fuel value) before ValueReady)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (bounded : ∀ edge ∈ first :: rest, ∀ value ∈ edge.children, height value ≤ limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (ready : ∀ edge ∈ first :: rest, EdgeReady before edge) :
    Complete (fun fuel => SourceMergedWorker.large (recurse fuel) clear fuel top first rest) before EdgeReady := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  have children := map_complete (fun fuel => SourceMergedWorker.column (recurse fuel) clear fuel)
    (fun state values => ∀ value ∈ values, ValueReady state value) ValueReady
    (fun before after effects _ inputs value member => value_grows before after effects value (inputs value member)) value_grows columns
    (fun column member state semantic inputs => column_complete recurse limit clear smaller column state semantic
      (fun value included => (inputs value included).1) (fun value included => (inputs value included).2)
      (fun value included => by obtain ⟨edge, outer, inner⟩ := original column member value included; exact bounded edge outer value inner))
    before semantic (by
      intro column member value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact ⟨semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (ready edge outer).1 value inner,
        (ready edge outer).2 value inner⟩)
  apply bind_complete _ _ before _ EdgeReady children
  intro values after effects available
  exact edge_complete first.entry.key.symbol top values after effects.2 available

end MicroCFTA.SourceMergedEdgeCompletion
