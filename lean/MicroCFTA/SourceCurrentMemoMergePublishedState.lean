import MicroCFTA.SourceCurrentMemoMergePublishedGraph

/-!
# Captured records in a published merge table

Published keys identify the complete captured original records in one
coherent heap. Completed entries have a published producer at their key.
These are warm-state invariants. They contain no result-language claim.
-/
namespace MicroCFTA.SourceCurrentMemoMergePublishedState
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMergeResultMemo (Producer Published)
open SourceCurrentMemoMergeGraph (Memo Entry remember)
open SourceCurrentMemoMergePublishedGraph (publish selected selected_present publish_extends)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard

/-- Every published key retains a resident captured original with exactly that reference. -/
structure Known (heap : Heap) (table : Published) : Prop where
  keys : ∀ key producer, table key = some producer → producer.original.referenceOf = key
  available : ∀ key producer, table key = some producer → Available heap producer.original

/-- Every completed lookup key has an actual published producer. -/
def CompletedPublished (table : Published) (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → ∃ producer, table key = some producer

/-- An empty publication table has no captured-record obligations. -/
theorem Known.empty (heap : Heap) : Known heap (fun _ => none) := by
  constructor <;> intro key producer impossible <;> cases impossible

/-- Physical heap growth retains the complete captured originals at unchanged published keys. -/
theorem Known.grows {before after : Heap} {table : Published}
    (known : Known before table) (keeps : Keeps before after) : Known after table :=
  ⟨known.keys, fun key producer found => keeps.available _ (known.available key producer found)⟩

/-- First-writer publication adds only its actual available captured input. -/
theorem Known.publish {heap : Heap} {table : Published} (known : Known heap table)
    (input : Value Symbol Guard) (ticket : Nat) (available : Available heap input) :
    Known heap (publish table input ticket) := by
  constructor
  · intro key producer found
    rcases InternedRecordCoherence.record_cases table input.referenceOf key ⟨ticket, input⟩ producer found with
      old | ⟨same, equal⟩
    · exact known.keys key producer old
    · subst producer
      exact same.symm
  · intro key producer found
    rcases InternedRecordCoherence.record_cases table input.referenceOf key ⟨ticket, input⟩ producer found with
      old | ⟨_, equal⟩
    · exact known.available key producer old
    · subst producer
      exact available

/-- The selected producer captures a complete record available in the actual current heap. -/
theorem selected_available {heap : Heap} {table : Published} (known : Known heap table)
    (input : Value Symbol Guard) (ticket : Nat) (available : Available heap input) :
    Available heap (selected table input ticket).original :=
  (known.publish input ticket available).available _ _ (selected_present table input ticket)

/-- Coherent resident identity makes the selected captured original literally the requested record. -/
theorem selected_original {heap : Heap} {table : Published} {input : Value Symbol Guard} {ticket : Nat}
    (known : Known heap table) (semantic : SemanticReady heap) (available : Available heap input) :
    (selected table input ticket).original = input := by
  have current := known.publish input ticket available
  have found := selected_present table input ticket
  exact InternedFreshProbeKeys.resident_reference_injective heap semantic.ready.semantic.1.normal.facts.coherent
    (selected table input ticket).original input (current.available _ _ found).resident available.resident
    (current.keys _ _ found)

/-- An empty completed map is covered by every publication table. -/
theorem CompletedPublished.empty (table : Published) :
    CompletedPublished table SourceCurrentMemoMergeGraph.empty := by
  intro key entry impossible
  cases impossible

/-- Published-table extension retains coverage for every unchanged completed entry. -/
theorem CompletedPublished.grows {table saved : Published} {memo : Memo Symbol Guard}
    (covered : CompletedPublished table memo) (growth : Extends table saved) : CompletedPublished saved memo := by
  intro key entry found
  obtain ⟨producer, published⟩ := covered key entry found
  exact ⟨producer, growth key producer published⟩

/-- Publishing an additional captured producer retains all earlier completed coverage. -/
theorem CompletedPublished.publish {table : Published} {memo : Memo Symbol Guard}
    (covered : CompletedPublished table memo) (input : Value Symbol Guard) (ticket : Nat) :
    CompletedPublished (publish table input ticket) memo :=
  covered.grows (publish_extends table input ticket)

/-- Completion has published coverage when its actual original key already has a producer. -/
theorem CompletedPublished.remember {table : Published} {memo : Memo Symbol Guard}
    (covered : CompletedPublished table memo) (input output : Value Symbol Guard) (producer : Producer)
    (published : table input.referenceOf = some producer) :
    CompletedPublished table (remember memo input output) := by
  intro key entry found
  rcases SourceCurrentMemoMergeGraph.remember_cases memo input output key entry found with old | ⟨same, _⟩
  · exact covered key entry old
  · exact ⟨producer, same ▸ published⟩

end MicroCFTA.SourceCurrentMemoMergePublishedState
