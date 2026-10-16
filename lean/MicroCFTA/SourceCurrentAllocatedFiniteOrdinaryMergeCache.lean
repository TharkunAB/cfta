import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
import MicroCFTA.SourceCurrentMemoMergeEffects

/-!
# Conditional domain certificates for completed merge entries

Each stored entry relates its result to its own captured original.
Completion retains an earlier winner or stores the proved candidate.
Physical request readback identifies an existing winner's complete original.
These helpers do not supply a body execution or its result certificate.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCache
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable {Symbol Guard : Type}

/-- Domain originals require domain results in the completed result table. -/
def Stored (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → DNode entry.original → DNode entry.result

/-- An empty completed table needs no producer certificate. -/
theorem empty_stored : Stored (empty : Memo Symbol Guard) := by
  intro key entry found
  cases found

/-- Completion checks only the new candidate and preserves earlier entries. -/
theorem remember_stored {memo : Memo Symbol Guard} (stored : Stored memo)
    (input candidate : Value Symbol Guard) (law : DNode input → DNode candidate) :
    Stored (remember memo input candidate) := by
  intro key entry found domain
  rcases remember_cases memo input candidate key entry found with old | ⟨_, same⟩
  · exact stored key entry old domain
  · subst entry
    exact law domain

/-- Physical hit readback identifies the complete original before using its domain certificate. -/
theorem hit_domain [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input : Value Symbol Guard}
    {entry : Entry Symbol Guard} (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (structural : Stored memo)
    (domain : DNode input) (found : memo input.referenceOf = some entry) :
    entry.original = input ∧ DNode entry.result := by
  have same := (SourceCurrentMemoMergeEffects.hit_original semantic available physical found).1
  exact ⟨same, structural _ entry found (same.symm ▸ domain)⟩

/-- The literal winner has the requested complete original even when an earlier entry wins. -/
theorem winner_original [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input : Value Symbol Guard}
    (candidate : Value Symbol Guard) (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) :
    (winner memo input candidate).original = input := by
  cases found : memo input.referenceOf with
  | none =>
      rw [(remember_absent memo input candidate found).2]
  | some entry =>
      rw [(winner_existing memo input candidate entry found).2]
      exact (SourceCurrentMemoMergeEffects.hit_original semantic available physical found).1

/-- Winner readback derives domain from the old entry or the locally proved candidate. -/
theorem winner_domain [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input candidate : Value Symbol Guard}
    (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (structural : Stored memo)
    (domain : DNode input) (candidateDomain : DNode candidate) :
    (winner memo input candidate).original = input ∧ DNode (winner memo input candidate).result := by
  have same := winner_original candidate semantic available physical
  have completed := remember_stored structural input candidate (fun _ => candidateDomain)
  exact ⟨same, completed _ _ (winner_found memo input candidate) (same.symm ▸ domain)⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCache
