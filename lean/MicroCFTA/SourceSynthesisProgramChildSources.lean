import MicroCFTA.SourceSynthesisProgramChildScope

/-!
# Raw variable sources of actual Program-child buckets

The prior scope law identifies the same bucket as fresh own-class descents.
Trie descent preserves each source variable. The variables stay in the exact
consecutive suspension interval. Raw bounds alone do not prove UF separation.
-/
namespace MicroCFTA.SourceSynthesisProgramChildSources
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- The same scopeResult Program child retains only variables from its own-class interval. -/
theorem program_child_sources
    (valid : Constraint → Prop) (edge : EdgeValue Symbol Constraint)
    (fields : SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge)
    (scs : List EnumerationState.Suspended) (start : Nat)
    (inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (index : Nat) (incoming : Node) (bucket : List EnumerationState.Suspended)
    (selected : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket))
    (programIndex :
      (edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
      (edge.entry.key.symbol = literal "filter" ∧ index = 1)) :
    (SourceSynthesisHereditaryProgramFields.ValueFields valid literal incoming ∧
      EnumerationState.descendScs index scs = [] ∧
      bucket = EnumerationState.descendScs index (EnumerationCorrectness.suspendedVars start tries) ∧
      ∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) ∧
      ∀ sc ∈ bucket, start ≤ sc.var ∧ sc.var < start + tries.length := by
  have scopeResult := SourceSynthesisProgramChildScope.program_child_scope valid edge fields scs start
    inherited tries residual projected index incoming bucket selected programIndex
  refine ⟨scopeResult, ?_⟩
  intro sc member
  rw [scopeResult.2.2.1] at member
  simp only [descendScs, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨original, included, rfl⟩, _retained⟩ := member
  change start ≤ original.var ∧ original.var < start + tries.length
  have listed : original.var ∈ (suspendedVars start tries).map EqualityTrie.Suspended.var :=
    List.mem_map.mpr ⟨original, included, rfl⟩
  rw [suspendedVars_variables] at listed
  obtain ⟨offset, inside, same⟩ := List.mem_range'.mp listed
  omega

end MicroCFTA.SourceSynthesisProgramChildSources
