import MicroCFTA.SourceCompileImportExecution
import MicroCFTA.SourceDenotationRanked
import MicroCFTA.SourceDenotationPlain
import MicroCFTA.SourceFiniteRebuildDriver

/-!
# Bounded liquid denotation and finite import compilation

The completed liquid denotation supplies the original bounded language.
Ranked source rows guarantee that finite reconstruction succeeds. The
compact primitive compiler then has exactly that distinct-term language.
The native interned readback and custom ordering adapters remain separate.
-/
namespace MicroCFTA.SourceBoundedImport
open Language

/-- The source depth counts leaves as zero. It is distinct from node-count size. -/
def Bounded (automaton : Automaton State Symbol) (root : State) (bound : Int) (term : Term Symbol) : Prop :=
  Accepts automaton root term ∧ ((term.height - 1 : Nat) : Int) ≤ bound

/-- Exact denotation derives successful reconstruction and the compact compiler's distinct language. -/
theorem rebuild_exact [DecidableEq Symbol] [Ord (Term Symbol)] [Ord (Option (Term Symbol))]
    (automaton : Automaton State Symbol) (root : State) (bound : Int)
    (assignment : Symbol → Nat)
    (ranked : ∀ state edge, edge ∈ automaton state → assignment edge.label = edge.children.length)
    (output : List (Term Symbol)) (language : ∀ term, term ∈ output ↔ Bounded automaton root bound term) :
    SourceFromTerms.build output = .ok (FTAValidation.normalizeRows (SourceFromTerms.rows output)) ∧
      (∀ term, Accepts (FTAValidation.rowFor (FTAValidation.normalizeRows (SourceFromTerms.rows output))) none term ↔
        Bounded automaton root bound term) ∧
      FiniteAutomatonDriver.ResultExact (Bounded automaton root bound) (SourceFiniteRebuildDriver.compile output) := by
  have built := SourceDenotationRanked.rebuild_succeeds automaton assignment ranked output
    (fun term member => ⟨root, ((language term).mp member).1⟩)
  refine ⟨built, fun term => (SourceFromTerms.build_exact output _ built term).trans (language term), ?_⟩
  exact (FiniteAutomatonDriver.result_ext _ _ language _).mp (SourceFiniteRebuildDriver.compile_exact output)

/-- A ranked successful denotation cannot return the fallback's residual-guard reconstruction error. -/
theorem fallback_rebuild [DecidableEq Symbol] [Ord (Term Symbol)] [Ord (Option (Term Symbol))]
    (automaton : Automaton State Symbol) (root : State) (bound : Int)
    (assignment : Symbol → Nat)
    (ranked : ∀ state edge, edge ∈ automaton state → assignment edge.label = edge.children.length)
    (output : List (Term Symbol)) (language : ∀ term, term ∈ output ↔ Bounded automaton root bound term)
    (grouped : FTAValidation.Rows (Option (Term Symbol)) Symbol → Value) (guard : SourceGuards.Guard Formula) :
    SourceCompileImport.finish (Invalid := Invalid) (Unknown := Unknown) SourceFromTerms.build grouped guard (.ok output) =
      .ok (grouped (FTAValidation.normalizeRows (SourceFromTerms.rows output))) := by
  have built := (rebuild_exact automaton root bound assignment ranked output language).1
  simp [SourceCompileImport.finish, built]

/-- Every successful compact result has exact source positions, both inverses, and language rejection. -/
theorem compiler_fields [DecidableEq Symbol] [Ord (Term Symbol)]
    (automaton : Automaton State Symbol) (root : State) (bound : Int)
    (output : List (Term Symbol)) (language : ∀ term, term ∈ output ↔ Bounded automaton root bound term)
    (result : CompactEdgeRanks.Index (Term Symbol)) (success : SourceFiniteRebuildDriver.compile output = some result) :
    result.count = (SourceFromTerms.ordered output).length ∧
      (∀ rank, result.select rank = (SourceFromTerms.ordered output)[rank]?) ∧
      CompactEdgeRanks.Correct result ∧
      (∀ term, result.rank term = none ↔ ¬Bounded automaton root bound term) := by
  obtain ⟨counted, selected⟩ := SourceFiniteRebuildDriver.compile_fields output result success
  obtain ⟨correct, rejected⟩ := SourceFiniteRebuildDriver.compile_inverse output result success
  exact ⟨counted, selected, correct, fun term => (rejected term).trans (not_congr (language term))⟩

/-- The ordinary denotation branch derives the same finite rebuild contract without solver calls. -/
theorem plain_correct [DecidableEq State] [DecidableEq Symbol]
    [Ord (Term Symbol)] [Ord (Option (Term Symbol))]
    (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms)
    (setDistinct : ∀ terms, (setList terms).Nodup)
    (keys : List State) (supported : ∀ state, state ∉ keys → automaton state = [])
    (assignment : Symbol → Nat)
    (ranked : ∀ state edge, edge ∈ automaton state → assignment edge.label = edge.children.length)
    (root : State) (bound : Int) :
    let output := SourceDenotationPlain.terms automaton setList keys bound root
    output.Nodup ∧ output.Pairwise (fun first second => first.height ≤ second.height) ∧
      SourceFromTerms.build output = .ok (FTAValidation.normalizeRows (SourceFromTerms.rows output)) ∧
      (∀ term, Accepts (FTAValidation.rowFor (FTAValidation.normalizeRows (SourceFromTerms.rows output))) none term ↔
        Bounded automaton root bound term) ∧
      FiniteAutomatonDriver.ResultExact (Bounded automaton root bound) (SourceFiniteRebuildDriver.compile output) := by
  obtain ⟨unique, ordered⟩ := SourceDenotationPlain.terms_distinct_ordered automaton plain
    setList setExact setDistinct keys supported bound root
  exact ⟨unique, ordered, rebuild_exact automaton root bound assignment ranked _
    (SourceDenotationPlain.terms_exact automaton plain setList setExact keys supported bound root)⟩

open FullSyntax SourceObservations SourceSizedLiquidProgram SolverAdapter
open SourceSizedLiquidAmbientAdequacy EnumerationCorrectness EnumerationSemantics

/-- The actual ambient evaluator and bounded enumeration derive the finite import contract. -/
theorem liquid_eventual [Ord SourceDenotationLiquid.Tree] [Ord (Option SourceDenotationLiquid.Tree)]
    (model : FormulaLowering.Model Value) (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat) (roundtrip : ∀ key, decode (encode key) = key)
    (source : Nat → List (EnumerationState.Edge SourceDenotationLiquid.Symbol SourceDenotationLiquid.Constraint))
    (meet : Nat → Nat → Nat) (valid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (sourceRows : EnumerationIntersection.HashRows (fun state => (source state).map
      (EnumerationLanguage.edgeView (Logical (SourceSizedLiquidAmbient.Meaning model given assumptions)))) meet)
    (assignment : SourceDenotationLiquid.Symbol → Nat)
    (ranked : ∀ node edge, edge ∈ source node → assignment edge.symbol = edge.children.length)
    (bound : Int) (nonnegative : 0 ≤ bound) (node : Nat) :
    ∃ cutoff, ∀ fuel, cutoff ≤ fuel → ∀ output work,
      SourceDenotationLiquid.Run (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check)
        source encode decode meet bound fuel node (.ok (.ok output)) work →
      output.Nodup ∧
      SourceFromTerms.build output = .ok (FTAValidation.normalizeRows (SourceFromTerms.rows output)) ∧
      (∀ term, Accepts (FTAValidation.rowFor (FTAValidation.normalizeRows (SourceFromTerms.rows output))) none term ↔
        Bounded (fun state => (source state).map
          (EnumerationLanguage.edgeView (Logical (SourceSizedLiquidAmbient.Meaning model given assumptions)))) node bound term) ∧
      FiniteAutomatonDriver.ResultExact
        (Bounded (fun state => (source state).map
          (EnumerationLanguage.edgeView (Logical (SourceSizedLiquidAmbient.Meaning model given assumptions)))) node bound)
        (SourceFiniteRebuildDriver.compile output) := by
  obtain ⟨cutoff, exactRun⟩ := SourceDenotationLiquid.eventual_exact model given assumptions milliseconds check correct
    encode decode roundtrip source meet valid sourceRows bound nonnegative node
  refine ⟨cutoff, ?_⟩
  intro fuel enough output work run
  obtain ⟨unique, language⟩ := exactRun fuel enough output work run
  refine ⟨unique, rebuild_exact _ node bound assignment ?_ output language⟩
  intro state edge member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact ranked state original present

end MicroCFTA.SourceBoundedImport
