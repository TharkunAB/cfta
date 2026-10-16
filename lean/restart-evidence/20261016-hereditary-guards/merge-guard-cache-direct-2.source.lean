import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
import MicroCFTA.SourceCurrentMemoMergeEffects

/-!
# Hereditary guard bounds in completed Merge entries

Each certificate refers to its own complete captured original. Physical
readback identifies that record at a warm hit. Completion retains an
earlier winner. The recursive producer derives each new candidate law.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryGuardProfiles (Node)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- The winner retains every hereditary guard bound of its captured original. -/
def Certificate (original result : Value Symbol Guard) : Prop :=
  ∀ limits, Node limits original → Node limits result

/-- Each completed entry stores the law of its own original and result. -/
def Stored (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → Certificate entry.original entry.result

/-- An unchanged value retains every hereditary guard bound. -/
theorem self_certificate (input : Value Symbol Guard) : Certificate input input := fun _ profile => profile

/-- Empty satisfies every hereditary guard bound. -/
theorem empty_certificate (input : Value Symbol Guard) : Certificate input .empty := fun _ _ => True.intro

/-- An empty completed table needs no candidate law. -/
theorem empty_stored : Stored (empty : Memo Symbol Guard) := by
  intro key entry found
  cases found

/-- A completed candidate adds its derived law without replacing earlier entries. -/
theorem remember_stored {memo : Memo Symbol Guard} (stored : Stored memo)
    (input candidate : Value Symbol Guard) (certificate : Certificate input candidate) :
    Stored (remember memo input candidate) := by
  intro key entry found
  rcases remember_cases memo input candidate key entry found with old | ⟨_, same⟩
  · exact stored key entry old
  · subst entry
    exact certificate

/-- Physical key readback transfers the complete captured law to the actual request. -/
theorem hit_certificate [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input : Value Symbol Guard}
    {entry : Entry Symbol Guard} (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (stored : Stored memo)
    (found : memo input.referenceOf = some entry) :
    entry.original = input ∧ Certificate input entry.result := by
  have same := (SourceCurrentMemoMergeEffects.hit_original semantic available physical found).1
  exact ⟨same, same ▸ stored _ entry found⟩

/-- The literal winner reread uses its prior law or the newly derived candidate law. -/
theorem winner_certificate [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input candidate : Value Symbol Guard}
    (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (stored : Stored memo)
    (certificate : Certificate input candidate) :
    Certificate input (winner memo input candidate).result ∧ Stored (remember memo input candidate) := by
  cases found : memo input.referenceOf with
  | none =>
      have same := (remember_absent memo input candidate found)
      exact ⟨by simpa only [same.2] using certificate, remember_stored stored input candidate certificate⟩
  | some entry =>
      have hit := hit_certificate semantic available physical stored found
      exact ⟨by simpa only [(winner_existing memo input candidate entry found).2] using hit.2,
        remember_stored stored input candidate certificate⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache
