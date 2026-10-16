import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCache

/-!
# Conditional output profiles in completed merge entries

Each certificate uses the complete original stored with its own result.
Completion preserves an earlier winner and checks only a new candidate.
Physical readback identifies the captured original at a warm hit.
These lifecycle laws do not prove a recursive body certificate.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open MergedOrdinaryHeight (height)
variable {Symbol Guard : Type}

/-- A merge result has a height-indexed row envelope and no greater input height. -/
def Certificate (original result : Value Symbol Guard) : Prop :=
  ∀ rows arity bound, NodeShape rows arity original → height original ≤ bound →
    NodeShape (envelope rows bound) arity result ∧ height result ≤ height original

/-- Every completed entry retains the certificate for its own captured original. -/
def Stored (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → Certificate entry.original entry.result

/-- An unchanged input satisfies every permitted output envelope. -/
theorem self_certificate (input : Value Symbol Guard) : Certificate input input := by
  intro rows arity bound profile _
  exact ⟨NodeShape.mono input profile
    (SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.rows_le_envelope rows bound) (Nat.le_refl _), Nat.le_refl _⟩

/-- Empty satisfies every permitted output envelope and input-relative height bound. -/
theorem empty_certificate (input : Value Symbol Guard) : Certificate input .empty := by
  intro _ _ _ _ _
  exact ⟨True.intro, Nat.zero_le _⟩

/-- An empty completed merge table needs no output certificate. -/
theorem empty_stored : Stored (empty : Memo Symbol Guard) := by
  intro key entry found
  cases found

/-- Completion retains every earlier certificate or stores the proved new candidate. -/
theorem remember_stored {memo : Memo Symbol Guard} (stored : Stored memo)
    (input candidate : Value Symbol Guard) (certificate : Certificate input candidate) :
    Stored (remember memo input candidate) := by
  intro key entry found
  rcases remember_cases memo input candidate key entry found with old | ⟨_, same⟩
  · exact stored key entry old
  · subst entry
    exact certificate

/-- The output profile invariant implies the earlier conditional domain invariant. -/
theorem Stored.domain {memo : Memo Symbol Guard} (stored : Stored memo) :
    SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored memo := by
  intro key entry found domain
  let limits := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.limits entry.original
  have profile := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.node_shape_self entry.original domain
  have result := stored key entry found limits.1 limits.2 (height entry.original) profile (Nat.le_refl _)
  exact SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain entry.result result.1

/-- Physical hit readback transfers the exact owner's certificate to the candidate request. -/
theorem hit_certificate [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input : Value Symbol Guard}
    {entry : Entry Symbol Guard} (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (stored : Stored memo)
    (found : memo input.referenceOf = some entry) :
    entry.original = input ∧ Certificate input entry.result := by
  have same := (SourceCurrentMemoMergeEffects.hit_original semantic available physical found).1
  exact ⟨same, same ▸ stored _ entry found⟩

/-- An exact warm winner supplies the requested profile and the original-relative height bound. -/
theorem hit_profile [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input : Value Symbol Guard}
    {entry : Entry Symbol Guard} (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (stored : Stored memo)
    (found : memo input.referenceOf = some entry) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (bounded : height input ≤ bound) :
    entry.original = input ∧ NodeShape (envelope rows bound) arity entry.result ∧ height entry.result ≤ height input := by
  have hit := hit_certificate semantic available physical stored found
  exact ⟨hit.1, hit.2 rows arity bound profile bounded⟩

/-- The winner reread uses an earlier certificate or the newly proved candidate certificate. -/
theorem winner_certificate [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input candidate : Value Symbol Guard}
    (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (stored : Stored memo)
    (certificate : Certificate input candidate) :
    (winner memo input candidate).original = input ∧ Certificate input (winner memo input candidate).result ∧
      Stored (remember memo input candidate) := by
  have same := SourceCurrentAllocatedFiniteOrdinaryMergeCache.winner_original candidate semantic available physical
  have completed := remember_stored stored input candidate certificate
  have law := completed _ _ (winner_found memo input candidate)
  rw [same] at law
  exact ⟨same, law, completed⟩

/-- Reentrant completion preserves the earlier winner even when a different candidate finishes. -/
theorem winner_existing_certificate {memo : Memo Symbol Guard} (stored : Stored memo)
    (input candidate : Value Symbol Guard) (entry : Entry Symbol Guard)
    (found : memo input.referenceOf = some entry) :
    remember memo input candidate = memo ∧ winner memo input candidate = entry ∧
      Certificate entry.original entry.result :=
  ⟨(winner_existing memo input candidate entry found).1,
    (winner_existing memo input candidate entry found).2, stored _ entry found⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache
