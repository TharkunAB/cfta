import MicroCFTA.SourceIdentityReads
import MicroCFTA.Observation

/-!
# Exact source guard observation plans

The plan uses every current Guard path and strengthens symbol-sensitive reads.
Its sparse traversal retains all information the source evaluator reads.
-/
namespace MicroCFTA.SourceGuardPlan
open SourceGuards SourceObservations SourceReadAgreement

/-- The source requests complete symbols only at its structural and substitution paths. -/
def need (guard : Guard Formula) (path : Path) : Observation.Need :=
  if path ∈ sensitive guard then .symbol else .refinement

/-- Build the actual source path plan in ascending path order. -/
def plan (guard : Guard Formula) : Observation.Plan :=
  Observation.buildPlan ((orderedPaths (paths guard)).map (fun target => (target, need guard target)))

/-- Repeated requests for one path combine its same computed need without changing it. -/
theorem requested_function (targets : List Path) (needs : Path → Observation.Need) (path : Path)
    (initial : Option Observation.Need) :
    Observation.requestedAt (targets.map (fun target => (target, needs target))) path initial =
      if path ∈ targets then Observation.addNeed initial (needs path) else initial := by
  induction targets generalizing initial with
  | nil => simp [Observation.requestedAt]
  | cons head rest ih =>
      simp only [List.map_cons, Observation.requestedAt, List.foldl_cons] at *
      rw [ih]
      by_cases same : path = head <;> by_cases tail : path ∈ rest <;>
        simp [same, tail, Observation.addNeed_idempotent]

/-- The plan contains exactly the required paths, with the exact required observation kind. -/
theorem lookup_plan (guard : Guard Formula) (path : Path) :
    Observation.lookup (plan guard) path = if path ∈ paths guard then some (need guard path) else none := by
  unfold plan Observation.buildPlan
  rw [Observation.lookup_buildFrom, requested_function, Observation.lookup_empty]
  simp [orderedPaths, Observation.addNeed]

/-- The full observations retained beside each sparse source signature. -/
def observations (guard : Guard Formula) (term : Language.Term (Label Formula)) : Observations Formula :=
  Observation.readWith (fun _ => rootObservation) (plan guard) term

/-- The source signature entry for the planned need. -/
def inspect (needed : Observation.Need) (term : Language.Term (Label Formula)) : SignatureEntry Formula :=
  match needed with
  | .refinement => .refinement (rootObservation term).refinement
  | .symbol => .symbol (rootObservation term)

/-- Read the actual trie signature from a complete term. -/
def signature (guard : Guard Formula) (term : Language.Term (Label Formula)) : Path → Option (SignatureEntry Formula) :=
  Observation.readWith inspect (plan guard) term

/-- Planned observations agree with complete observations at every requested path. -/
theorem observations_requested (guard : Guard Formula) (term : Language.Term (Label Formula))
    (path : Path) (requested : path ∈ paths guard) :
    observations guard term path = observe term path := by
  rw [observations, Observation.readWith_correct, lookup_plan]
  simp [requested, observe]

/-- The trie signature has exactly the source evaluator's path-indexed grouping meaning. -/
theorem signature_exact (guard : Guard Formula) (term : Language.Term (Label Formula)) :
    signature guard term = SourceReadAgreement.signature guard (observe term) := by
  funext path
  rw [signature, Observation.readWith_correct, lookup_plan]
  by_cases requested : path ∈ paths guard
  · simp only [requested, ↓reduceIte, Option.bind_some, SourceReadAgreement.signature, observe, Option.map_map]
    by_cases sensitive : path ∈ SourceGuards.sensitive guard <;>
      cases term.atPath path <;> simp [need, inspect, sensitive]
  · simp [requested, SourceReadAgreement.signature]

/-- Sparse trie reading is sufficient for every source guard, including conflicting actual identities. -/
theorem planned_evaluator_exact [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : SourceGuards.Entailment Formula) (guard : Guard Formula) (term : Language.Term (Label Formula)) :
    evaluateGuardWithShape formulas solver (observations guard term) guard =
      evaluateGuardWithShape formulas solver (observe term) guard :=
  SourceIdentityReads.requested_observations_exact formulas solver guard _ _
    (fun path member => observations_requested guard term path member)

/-- An unambiguous decided result from the actual trie equals public complete-term evaluation. -/
theorem planned_decided_exact [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : SourceGuards.Entailment Formula) (guard : Guard Formula) (term : Language.Term (Label Formula))
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = [])
    (decided : evaluateGuardWithShape formulas solver (observations guard term) guard ≠ .unknown) :
    evaluateGuardWithShape formulas solver (observations guard term) guard = evaluateGuard formulas solver guard term := by
  rw [planned_evaluator_exact] at decided ⊢
  exact SourceGuardRefinement.unambiguous_decided_exact formulas solver term guard unambiguous decided

/-- Equal source trie signatures select the same guard decision when no fresh conflict values are needed. -/
theorem signature_group_exact [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : SourceGuards.Entailment Formula) (guard : Guard Formula)
    (first second : Language.Term (Label Formula))
    (same : signature guard first = signature guard second)
    (noConflict : conflicts (observe first) (sameShape formulas (observe first) []) guard = []) :
    evaluateGuardWithShape formulas solver (observations guard first) guard =
      evaluateGuardWithShape formulas solver (observations guard second) guard := by
  rw [planned_evaluator_exact, planned_evaluator_exact]
  apply SourceIdentityReads.no_conflict_signature_exact formulas solver guard _ _ _ noConflict
  simpa only [signature_exact] using same

end MicroCFTA.SourceGuardPlan
