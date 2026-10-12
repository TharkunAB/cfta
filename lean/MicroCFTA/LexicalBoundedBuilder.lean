import MicroCFTA.LexicalExposureLanguage
import MicroCFTA.EnumerationBuilderRuntime

/-!
# Lexical languages through the concrete bounded builder

Structural row readback connects runtime identities to closed lexical
instances. The existing builder then supplies the memo, edge-cache,
node-cache, empty-child cleanup, and terminal-entry results.
-/
namespace MicroCFTA.LexicalBoundedBuilder
open Language Binding BinderLanguage
open EnumerationInternedRows EnumerationSemantics EnumerationCorrectness

/-- Structural readback derives the runtime constructor graph's lexical language. -/
theorem source_language [DecidableEq (Shape (Payload Symbol))]
    (environment : Env Symbol) (source : Nat → RowKey Symbol Guard)
    (guardMeaning : Guard → Term Symbol → Prop) (read : Nat → Shape (Payload Symbol))
    (copied : SymbolicGraphView.RowsCorrespond
      (fun node => (source node).map (EnumerationLanguage.edgeView guardMeaning))
      LexicalExposureLanguage.automaton read)
    (node : Nat) (closed : free (read node) = []) (term : Term Symbol) :
    Accepts (fun node => (source node).map (EnumerationLanguage.edgeView guardMeaning)) node term ↔
      meaning environment (read node) term := by
  rw [← SymbolicGraphView.rowsCorrespond_exact _ _ read copied node term]
  exact LexicalExposureLanguage.automaton_exact environment (read node) closed term

/-- Memoized construction from read-back source rows retains exactly the bounded lexical language. -/
theorem requested_exact [DecidableEq (Shape (Payload Symbol))]
    [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (environment : Env Symbol) (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (guardMeaning : Guard → Term Symbol → Prop) (read : Nat → Shape (Payload Symbol))
    (copied : SymbolicGraphView.RowsCorrespond
      (fun node => (source node).map (EnumerationLanguage.edgeView guardMeaning))
      LexicalExposureLanguage.automaton read)
    (requests : List EnumerationBuilder.Key) (meet : Nat → Nat → Nat)
    (key : EnumerationBuilder.Key) (member : key ∈ requests)
    (closed : free (read key.2) = []) (term : Term Symbol) :
    Accepted (EnumerationBuilderRuntime.graph (EnumerationBuilderRuntime.buildAll source requests) meet)
      guardMeaning (EnumerationBuilderRuntime.encode (EnumerationBuilderRuntime.buildAll source requests) key) term ↔
      meaning environment (read key.2) term ∧ term.height ≤ key.1 := by
  rw [EnumerationBuilderRuntime.requested_accepted_exact source sourceValid requests meet guardMeaning key member term,
    source_language environment source guardMeaning read copied key.2 closed term]

/-- Source terminal-entry elision also retains exactly the bounded lexical language. -/
theorem elided_requested_exact [DecidableEq (Shape (Payload Symbol))]
    [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (environment : Env Symbol) (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (guardMeaning : Guard → Term Symbol → Prop) (read : Nat → Shape (Payload Symbol))
    (copied : SymbolicGraphView.RowsCorrespond
      (fun node => (source node).map (EnumerationLanguage.edgeView guardMeaning))
      LexicalExposureLanguage.automaton read)
    (requests : List EnumerationBuilder.Key) (meet : Nat → Nat → Nat)
    (key : EnumerationBuilder.Key) (member : key ∈ requests)
    (closed : free (read key.2) = []) (term : Term Symbol) :
    Accepted
      (EnumerationBuilderRuntime.graph
        (EnumerationBuilderRuntime.elide source (EnumerationBuilderRuntime.buildAll source requests)) meet)
      guardMeaning
      (EnumerationBuilderRuntime.encode
        (EnumerationBuilderRuntime.elide source (EnumerationBuilderRuntime.buildAll source requests)) key) term ↔
      meaning environment (read key.2) term ∧ term.height ≤ key.1 := by
  rw [EnumerationBuilderRuntime.elided_requested_exact source sourceValid requests meet guardMeaning key member term,
    source_language environment source guardMeaning read copied key.2 closed term]

end MicroCFTA.LexicalBoundedBuilder
