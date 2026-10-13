import MicroCFTA.SourceSizedLiquidAmbient

/-!
# Ambient free-name preflight

The repaired adapter reserves free names in ambient assumptions before it
accepts generated value bindings. It retains the original declaration list
and inherited sorts. Rejected preflight returns Unknown without an SMT call.
The older adapter remains available as the historical collision model.
-/

namespace MicroCFTA.SourceSizedLiquidAmbientRepair

open FullSyntax SolverAdapter SourceSizedLiquidProgram

/-- Ambient free names cannot also name generated values. -/
def collides (assumptions : List Formula) (query : Query) : Bool :=
  query.bindings.any fun binding => binding.1 ∈ partsNames assumptions

/-- Reserve the free ambient names in addition to the original declared-name check. -/
def prepareQuery (given : List Declaration) (assumptions : List Formula) (query : Query) : Option Prepared :=
  if collides assumptions query then none
  else SolverAdapter.prepareQuery given query.bindings assumptions query.antecedent query.consequent

/-- The repaired source checks the union of declared names and lowered ambient free symbols. -/
def reservedFresh (ambient : List Declaration) (assumptions : List Formula)
    (binding : Name × Name) : Option Declaration :=
  if binding.1 ∈ ambient.map Prod.fst ∨
      binding.1 ∈ partsSymbols (FormulaLowering.lowerParts assumptions) then none
  else some (binding.1, (lookupSort binding.2 ambient).getD .int)

/-- Traverse the repaired fresh declarations in their source order. -/
def reservedFreshList (ambient : List Declaration) (assumptions : List Formula) :
    List (Name × Name) → Option (List Declaration)
  | [] => some []
  | binding :: rest => do
      let first ← reservedFresh ambient assumptions binding
      let tail ← reservedFreshList ambient assumptions rest
      pure (first :: tail)

/-- The repaired traversal is exactly the old traversal with the additional free-name preflight. -/
theorem reservedFreshList_exact (ambient : List Declaration) (assumptions : List Formula)
    (bindings : List (Name × Name)) :
    reservedFreshList ambient assumptions bindings =
      if bindings.any (fun binding => binding.1 ∈ partsNames assumptions) then none
      else freshDeclarations ambient bindings := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      by_cases oldCollision : binding.1 ∈ ambient.map Prod.fst
      · have refused : freshDeclarations ambient (binding :: rest) = none := by
          simp [freshDeclarations, freshDeclaration, oldCollision]
        rw [refused]
        simp only [ite_self]
        simp [reservedFreshList, reservedFresh, oldCollision]
      · by_cases newCollision : binding.1 ∈ partsNames assumptions
        · simp [reservedFreshList, reservedFresh, parts_symbols_lower, newCollision]
        · simp only [reservedFreshList, reservedFresh, parts_symbols_lower, oldCollision, newCollision,
            or_self, ↓reduceIte, ih, List.any_cons,
            freshDeclarations, freshDeclaration]
          cases tailCollision : rest.any (fun binding => binding.1 ∈ partsNames assumptions) <;> simp

/-- The repaired source emits the original declarations after its reserved-name traversal. -/
def sourcePrepare (given : List Declaration) (assumptions : List Formula) (query : Query) : Option Prepared := do
  let ambient := declarations given
  let fresh ← reservedFreshList ambient assumptions query.bindings
  pure ⟨ambient ++ fresh ++ undeclared ambient fresh (mentioned assumptions query.antecedent query.consequent),
    assertion assumptions query.antecedent query.consequent⟩

/-- The proof adapter is the actual repaired preflight, including lowered free-symbol collection. -/
theorem sourcePrepare_exact (given : List Declaration) (assumptions : List Formula) (query : Query) :
    sourcePrepare given assumptions query = prepareQuery given assumptions query := by
  unfold sourcePrepare prepareQuery collides
  dsimp only
  rw [reservedFreshList_exact]
  cases collision : query.bindings.any (fun binding => binding.1 ∈ partsNames assumptions) <;>
    simp [SolverAdapter.prepareQuery, prepare]

/-- Successful repaired requests retain exactly the original declarations and assertion. -/
theorem successful_original (given : List Declaration) (assumptions : List Formula) (query : Query)
    (request : Prepared) (prepared : prepareQuery given assumptions query = some request) :
    SolverAdapter.prepareQuery given query.bindings assumptions query.antecedent query.consequent = some request := by
  unfold prepareQuery at prepared
  split at prepared
  · contradiction
  · exact prepared

/-- The repair changes no query that avoids the free ambient names. -/
theorem unchanged (given : List Declaration) (assumptions : List Formula) (query : Query)
    (fresh : ∀ binding ∈ query.bindings, binding.1 ∉ partsNames assumptions) :
    prepareQuery given assumptions query =
      SolverAdapter.prepareQuery given query.bindings assumptions query.antecedent query.consequent := by
  have clean : collides assumptions query = false := by
    simp only [collides, List.any_eq_false, decide_eq_true_eq]
    exact fresh
  simp [prepareQuery, clean]

/-- A collision with a free ambient name is rejected before external execution. -/
theorem rejects (given : List Declaration) (assumptions : List Formula) (query : Query)
    (binding : Name × Name) (present : binding ∈ query.bindings)
    (collision : binding.1 ∈ partsNames assumptions) : prepareQuery given assumptions query = none := by
  have found : collides assumptions query = true := by
    exact List.any_eq_true.mpr ⟨binding, present, by simpa using collision⟩
  simp [prepareQuery, found]

/-- One actual repaired adapter call preserves preflight, returned verdicts, and exceptions. -/
inductive Call (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) : Query → Nat → Result → Prop where
  | preflight : prepareQuery given assumptions query = none →
      Call given assumptions milliseconds check query 1 (.returned .unknown)
  | checked : prepareQuery given assumptions query = some request → check request work attempt →
      Call given assumptions milliseconds check query (work + 1) (finish milliseconds attempt).result

/-- Every repaired call is a sound query in the exact mixed-sort ambient context. -/
theorem call_supports (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    {query work result} (call : Call given assumptions milliseconds check query work result) :
    ResultSupports result (SourceSizedLiquidAmbient.Meaning model given assumptions query) := by
  cases call with
  | preflight rejected => trivial
  | checked prepared called =>
      exact SourceSizedLiquidAmbient.call_supports model given assumptions milliseconds check correct
        (.checked (successful_original given assumptions _ _ prepared) called)

/-- Finite external outcomes give finite repaired adapter outcomes, including raised failures. -/
theorem call_finite (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (query : Query) :
    ∃ work result, Call given assumptions milliseconds check query work result := by
  cases prepared : prepareQuery given assumptions query with
  | none => exact ⟨1, .returned .unknown, .preflight prepared⟩
  | some request =>
      obtain ⟨work, attempt, called⟩ := completed request
      exact ⟨work + 1, (finish milliseconds attempt).result, .checked prepared called⟩

end MicroCFTA.SourceSizedLiquidAmbientRepair
