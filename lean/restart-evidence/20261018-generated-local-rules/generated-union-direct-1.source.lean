import MicroCFTA.SourceCurrentSourceDirectedCases
import MicroCFTA.SourceCurrentStoredLiteralExecutionParts
import MicroCFTA.SourceCurrentLiteralFilterParts

/-!
# Literal fragments through actual union filtering and reconstruction

An actual union member retains its literal atoms and full rows after
self filtering when the bare-self exception permits that member.
Actual warm reconstruction preserves this literal inclusion. Mu atoms
remain opaque. These laws do not assert warm subgroup filters or supply
the local simulation law for every generated source pair.
-/
namespace MicroCFTA.SourceCurrentGeneratedUnionCases
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome work)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open InternedBinderProtocol (Reference)
open SourceCurrentSourceDirectedCases (Below)
open SourceCurrentStoredLiteralExecutionParts (LiteralOutput RowOutput)
open SourceEqualityRequiredCache (Ready)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual warm calls under one map preserve exact literal inclusion. -/
theorem execute_below (first second left right : Value Symbol Guard)
    (environment : Environment Symbol Guard) (reader : State Symbol Guard)
    (ready : Ready reader) (firstAvailable : Available reader first)
    (secondAvailable : Available reader second) (replacements : Replacements reader environment)
    (included : Below first second)
    (firstDone : execute first environment reader = .done left reader)
    (secondDone : execute second environment reader = .done right reader) : Below left right := by
  have firstParts := SourceCurrentStoredLiteralExecutionParts.parts first left environment reader
    ready firstAvailable replacements firstDone
  have secondParts := SourceCurrentStoredLiteralExecutionParts.parts second right environment reader
    ready secondAvailable replacements secondDone
  constructor
  · intro atom found
    obtain ⟨source,part,output,called,present⟩ := (firstParts.1 atom).mp found
    exact (secondParts.1 atom).mpr ⟨source,included.1 source part,output,called,present⟩
  · intro row found
    rcases (firstParts.2 row).mp found with atom | ordinary
    · obtain ⟨source,part,output,called,present⟩ := atom
      exact (secondParts.2 row).mpr (Or.inl ⟨source,included.1 source part,output,called,present⟩)
    · obtain ⟨source,part,called,live⟩ := ordinary
      exact (secondParts.2 row).mpr (Or.inr ⟨source,included.2 source part,called,live⟩)

/-- The exact bare-self retention condition preserves literal inclusion through actual filters. -/
theorem filter_below (reader : State Symbol Guard) (normal : Normal reader)
    (own : Reference) (member parent : Value Symbol Guard)
    (memberAvailable : Available reader member) (parentAvailable : Available reader parent)
    (included : Below member parent)
    (retained : member ≠ .reference own ∨ parent = .reference own) :
    Below (run (withoutSelfReference own member) reader).1
      (run (withoutSelfReference own parent) reader).1 := by
  constructor
  · intro atom found
    obtain ⟨part,other⟩ := (SourceCurrentLiteralFilterParts.literal reader normal own member memberAvailable atom).mp found
    apply (SourceCurrentLiteralFilterParts.literal reader normal own parent parentAvailable atom).mpr
    refine ⟨included.1 atom part,?_⟩
    rcases retained with different | bare
    · exact Or.inr (other.resolve_left different)
    · exact Or.inl bare
  · intro row found
    apply (SourceCurrentLiteralFilterParts.row reader normal own parent parentAvailable row).mpr
    exact included.2 row ((SourceCurrentLiteralFilterParts.row reader normal own member memberAvailable row).mp found)

/-- A retained actual union member supplies a reconstructed literal fragment of its parent result. -/
theorem retained_member (reader : State Symbol Guard) (ready : Ready reader)
    (values : List (Value Symbol Guard)) (available : Values reader values)
    (member parent memberFiltered parentFiltered left right : Value Symbol Guard)
    (own : Reference) (environment : Environment Symbol Guard)
    (selected : member ∈ values)
    (made : run (makeUnion values) reader = (parent,reader))
    (retained : member ≠ .reference own ∨ parent = .reference own)
    (memberFilter : run (withoutSelfReference own member) reader = (memberFiltered,reader))
    (parentFilter : run (withoutSelfReference own parent) reader = (parentFiltered,reader))
    (replacements : Replacements reader environment)
    (firstDone : execute memberFiltered environment reader = .done left reader)
    (secondDone : execute parentFiltered environment reader = .done right reader) : Below left right := by
  have parentAvailable : Available reader parent := by
    have actual := (makeUnion_available values reader ready.semantic.1.normal.facts.coherent
      ready.semantic.1.normal.facts.cached available).2.2
    simpa only [made] using actual
  have raw := SourceCurrentSourceDirectedCases.union_member values reader ready.semantic.1.normal available member selected
  rw [made] at raw
  have filtered := filter_below reader ready.semantic.1.normal own member parent
    (available member selected) parentAvailable raw retained
  rw [memberFilter,parentFilter] at filtered
  have memberOutput : Available reader memberFiltered := by
    apply (InternedNestedFacts.filter_verified own member reader ready.semantic.1.normal.facts
      (available member selected)).result memberFiltered reader
    simp only [work,memberFilter]
  have parentOutput : Available reader parentFiltered := by
    apply (InternedNestedFacts.filter_verified own parent reader ready.semantic.1.normal.facts
      parentAvailable).result parentFiltered reader
    simp only [work,parentFilter]
  exact execute_below memberFiltered parentFiltered left right environment reader ready
    memberOutput parentOutput replacements filtered firstDone secondDone

end MicroCFTA.SourceCurrentGeneratedUnionCases
