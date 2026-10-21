import MicroCFTA.SourceCurrentNativeRequestPositivePositions
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointOrigins

/-! # Positive native memo support at a later source heap -/
namespace MicroCFTA.SourceCurrentNativePositiveSupportRebase
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionThunks
open SourceCurrentNativeRequestPositivePositions (Support)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)

/-- The same captured requests retain positive-position support at a later source heap. -/
theorem rebase (source later : Heap) (state : Native width Symbol Guard)
    (sourceFacts : Facts source) (laterFacts : Facts later)
    (growth : Grows source later) (issued : Extends source.nodes.issued later.nodes.issued)
    (origins : SourceCurrentConstrainedCapCheckedJointOrigins.Stored source state)
    (supported : Support source state) : Support later state := by
  constructor
  · refine ⟨supported.1.bounded, supported.1.linked, ?_⟩
    intro handle cell found
    cases cell with
    | mk request phase =>
        cases phase with
        | suspended | evaluating => trivial
        | returned result =>
            intro depth bindings inputs left right path positive
            have origin := origins.nodes handle ⟨request, .returned result⟩ found
            have oldBindings := SourceCurrentConstrainedCapCheckedJointOrigins.bindings_back
              Plain source later growth issued laterFacts request.domain.key origin.scope.bindings bindings
            exact supported.1.checked handle ⟨request, .returned result⟩ found depth oldBindings
              (origin.inputs_back inputs) left right path positive
  · refine ⟨supported.2.bounded, supported.2.linked, ?_⟩
    intro handle cell found
    cases cell with
    | mk request phase =>
        cases phase with
        | suspended | evaluating => trivial
        | returned result =>
            intro depth bindings inputs left right
            have origin := origins.edges handle ⟨request, .returned result⟩ found
            have oldBindings := SourceCurrentConstrainedCapCheckedJointOrigins.bindings_back
              Plain source later growth issued laterFacts request.domain.key origin.scope.bindings bindings
            exact supported.2.checked handle ⟨request, .returned result⟩ found depth oldBindings
              (origin.inputs_back sourceFacts inputs) left right

end MicroCFTA.SourceCurrentNativePositiveSupportRebase
