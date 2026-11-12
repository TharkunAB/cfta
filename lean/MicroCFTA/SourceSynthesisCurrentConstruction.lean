import MicroCFTA.SourceSynthesisCurrentContext
import MicroCFTA.SourceSynthesisFirstOrderTotality

/-!
# Current source construction at signed sizes

The wrapper uses the current context and the existing row algorithms.
Construction success does not imply membership or native completion.
-/
namespace MicroCFTA.SourceSynthesisCurrentConstruction
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression MissingKey relevantRows ofType)
open SourceSynthesisSelections (permutations)

/-- Construct the current root with canonical query bindings and repaired types. -/
def firstOrderRaw (lib : Library) (query : Query) (signed : Int) :
    Except MissingKey Expression :=
  let ctx := SourceSynthesisCurrentContext.context lib query
  if signed < 0 then .error (.relevant true signed (ctx.argumentEdges.map Prod.fst))
  else do
    let chunks ← (permutations ctx.argumentEdges).mapM fun selected =>
      relevantRows ctx true signed.toNat (selected.map Prod.fst)
    pure (ofType (.union chunks.flatten) (SourceSynthesisCurrentContext.typeNode query.queryGoal))

/-- A negative request retains its signed size and all original query names. -/
theorem firstOrderRaw_negative (lib : Library) (query : Query) (signed : Int)
    (negative : signed < 0) :
    firstOrderRaw lib query signed =
      .error (.relevant true signed (query.queryArguments.map Prod.fst)) := by
  simp only [firstOrderRaw, negative, ↓reduceIte,
    SourceSynthesisCurrentContext.context_argument_names]

/-- Every nonnegative current request has an actual successful root expression. -/
theorem firstOrderRaw_total (lib : Library) (query : Query) (signed : Int)
    (nonnegative : 0 ≤ signed) :
    ∃ expression, firstOrderRaw lib query signed = .ok expression := by
  have allowed : ¬signed < 0 := by omega
  let ctx := SourceSynthesisCurrentContext.context lib query
  obtain ⟨chunks, chunksRun⟩ := SymbolicDriver.pure_mapM_total
    (fun selected => relevantRows ctx true signed.toNat (selected.map Prod.fst))
    (permutations ctx.argumentEdges) (by
      intro selected included
      exact SourceSynthesisFirstOrderTotality.relevantRows_total_of_resolution
        ctx signed.toNat true (selected.map Prod.fst)
        (SourceSynthesisSelections.root_lookup_exists ctx.argumentEdges selected included))
  refine ⟨ofType (.union chunks.flatten)
    (SourceSynthesisCurrentContext.typeNode query.queryGoal), ?_⟩
  rw [firstOrderRaw, ite_eq_right allowed]
  change (permutations ctx.argumentEdges).mapM _ >>= _ = _
  rw [chunksRun]
  rfl

/-- Current root construction succeeds exactly on the nonnegative signed domain. -/
theorem firstOrderRaw_ok_iff_nonnegative (lib : Library) (query : Query) (signed : Int) :
    (∃ expression, firstOrderRaw lib query signed = .ok expression) ↔ 0 ≤ signed := by
  constructor
  · rintro ⟨expression, returned⟩
    by_cases nonnegative : 0 ≤ signed
    · exact nonnegative
    · have failed := firstOrderRaw_negative lib query signed (by omega)
      rw [failed] at returned
      cases returned
  · exact firstOrderRaw_total lib query signed

end MicroCFTA.SourceSynthesisCurrentConstruction
