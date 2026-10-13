import MicroCFTA.SourceDenotationRanked
import MicroCFTA.SourceFiniteRebuild

/-!
# Exact reconstruction after bounded denotation

A ranked source graph gives one arity to every constructor in every accepted
term. Successful denotation therefore supplies a valid finite-term rebuild.
The rebuilt graph has the same bounded language and a derived finite plain
count and decoder sequence. No successful-build premise is required.
-/
namespace MicroCFTA.SourceDenotationRebuild
open Language EnumerationState EnumerationCorrectness EnumerationSemantics
open SourceDenotationEnumeration

/-- Every source constructor agrees with the same alphabet arity assignment. -/
def Ranked (graph : Graph Symbol Guard) (assignment : Symbol → Nat) : Prop :=
  ∀ node edges, graph.node node = .alternatives edges →
    ∀ edge ∈ edges, assignment edge.symbol = edge.children.length

/-- The source graph and its language view use identical constructor arities. -/
theorem view_ranked (graph : Graph Symbol Guard) (assignment : Symbol → Nat)
    (ranked : Ranked graph assignment) (meaning : Guard → Term Symbol → Prop) :
    ∀ state edge, edge ∈ EnumerationLanguage.automaton graph meaning state →
      assignment edge.label = edge.children.length := by
  intro state edge member
  unfold EnumerationLanguage.automaton at member
  cases view : graph.node state with
  | empty | recursive | unresolved => simp [view] at member
  | alternatives edges =>
      rw [view] at member
      obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
      exact ranked state edges view source present

/-- Successful source denotation always rebuilds when the source alphabet is ranked. -/
theorem rebuild [DecidableEq Symbol] [Ord (Term Symbol)] [Ord (Option (Term Symbol))]
    (graph : Graph Symbol Guard) (assignment : Symbol → Nat) (ranked : Ranked graph assignment)
    (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (marker : Symbol) (fuel root : Nat) (sufficient : Sufficient graph meaning marker root fuel)
    (holds : Guard × Term Symbol → Bool)
    (semantic : ∀ obligation, holds obligation = true ↔ meaning obligation.1 obligation.2)
    (evaluates : Guard × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (adequate : SourceDenotationEffects.Adequate evaluates holds)
    (output : List (Term Symbol)) (work : Nat)
    (run : SourceDenotationRuns.Run evaluates (rows graph marker fuel root) (.ok output) work) :
    ∃ table, SourceFromTerms.build output = .ok table ∧
      (∀ term, Accepts (FTAValidation.rowFor table) none term ↔ Accepted graph meaning root term) ∧
      (∀ bound, forestHeight output < bound →
        Decoder.countAt (FTAValidation.rowFor table) bound none = (SourceFromTerms.ordered output).length ∧
        ∀ rank, Decoder.decode (Decoder.normalize
          (Decoder.compileAt (FTAValidation.rowFor table) bound none)) rank =
            (SourceFromTerms.ordered output)[rank]?) := by
  have language := successful_exact graph meaning complete correct marker fuel root sufficient
    holds semantic evaluates adequate output work run
  have built := SourceDenotationRanked.rebuild_succeeds (EnumerationLanguage.automaton graph meaning)
    assignment (view_ranked graph assignment ranked meaning) output
    (fun term member => ⟨root, (EnumerationLanguage.accepted_iff graph meaning complete root term).mp
      ((language term).mp member)⟩)
  let table := FTAValidation.normalizeRows (SourceFromTerms.rows output)
  refine ⟨table, built, ?_, ?_⟩
  · intro term
    exact (SourceFromTerms.build_exact output table built term).trans (language term)
  · intro bound enough
    have same : FTAValidation.rowFor table = SourceFromTerms.graph output :=
      funext (SourceFromTerms.build_rows output table built)
    rw [same]
    exact ⟨SourceFiniteRebuild.count_exact output bound enough,
      fun rank => SourceFiniteRebuild.decode_exact output bound rank enough⟩

end MicroCFTA.SourceDenotationRebuild
