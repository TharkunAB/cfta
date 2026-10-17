import MicroCFTA.SourceMemoGateSemantics
import MicroCFTA.SourceCurrentHereditaryUnconstrained

/-!
# Hereditary plain regions from the actual source gate

Coherent available input turns the visited source predicate into the
hereditary annotation condition. The proof needs no condition on unrelated
heap records. It visits stored Mu bodies and excludes both probes.
Accepted plain recursive regions therefore contain no own equality work.
This result does not establish a decreasing outer recursion measure.
-/
namespace MicroCFTA.SourceCurrentGatePlainRegion
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityAnnotationLanguage InternedSourceCrush
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

private theorem child_reached {value child record : Value S G}
    (selected : child ∈ sourceChildren value) (reached : Reaches [child] record) : Reaches [value] record :=
  reached.mono (fun root member => by
    obtain rfl := List.mem_singleton.mp member
    exact .child value child (.root value List.mem_cons_self) selected)

private theorem annotated_of_reached (valid : G → Prop) (heap : State S G)
    (value : Value S G) (available : Available heap value)
    (checks : ∀ record, Reaches [value] record →
      ∀ edge ∈ InternedEdgeResidency.nodeEdges record, valid edge.entry.key.constraint) : Annotated valid value := by
  revert checks
  induction available with
  | intro value resident issued children ih =>
      intro checks
      cases value with
      | empty => exact .empty
      | reference name => exact .reference name
      | node entry edges depth free =>
          refine .node entry edges depth free (checks _ (.root _ List.mem_cons_self)) ?_
          intro child member
          exact ih child (by simpa only [InternedProbeProvenance.children] using member)
            (fun record reached => checks record (child_reached member reached))
      | union entry members depth free =>
          refine .union entry members depth free ?_
          intro child member
          exact ih child (by simpa only [InternedProbeProvenance.children] using member)
            (fun record reached => checks record (child_reached member reached))
      | mu entry body depth ordinary =>
          refine .mu entry body depth ordinary ?_
          exact ih body (by simp [InternedProbeProvenance.children])
            (fun record reached => checks record (child_reached List.mem_cons_self reached))

/-- The actual visited gate derives hereditary plain annotations on coherent available input. -/
theorem annotations (heap : State Symbol Guard) (value : Value Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (available : Available heap value)
    (accepted : SourceMemoGate.unconstrained value = true) :
    Annotated (fun guard => SourceMemoGate.plain guard = true) value :=
  annotated_of_reached _ heap value available
    ((SourceMemoGate.unconstrained_exact value heap coherent available).mp accepted)

/-- The hereditary annotation condition and the actual source gate agree at available records. -/
theorem annotations_iff (heap : State Symbol Guard) (value : Value Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (available : Available heap value) :
    SourceMemoGate.unconstrained value = true ↔ Annotated (fun guard => SourceMemoGate.plain guard = true) value :=
  ⟨annotations heap value coherent available, SourceCurrentHereditaryUnconstrained.unconstrained value⟩

/-- A closed gate-accepted input derives the existing plain region from its physical facts. -/
theorem region (heap : State Symbol Guard) (value : Value Symbol Guard)
    (facts : InternedNestedFacts.Facts heap) (available : Available heap value) (closed : value.free = [])
    (accepted : SourceMemoGate.unconstrained value = true) : SourceEqualityPartialPlainRegion.Region value :=
  SourceCurrentHereditaryUnconstrained.to_plain_region heap facts value
    (annotations heap value facts.coherent available accepted) available closed

/-- Every actual reached guard in an accepted source region has the empty physical own payload. -/
theorem reached_empty (heap : State Symbol Guard) (value : Value Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (available : Available heap value)
    (accepted : SourceMemoGate.unconstrained value = true)
    (record : Value Symbol Guard) (reached : Reaches [value] record)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ InternedEdgeResidency.nodeEdges record) :
    SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []) :=
  SourceCurrentHereditaryUnconstrained.plain_physical edge.entry.key.constraint
    ((SourceMemoGate.unconstrained_exact value heap coherent available).mp accepted record reached edge member)

end MicroCFTA.SourceCurrentGatePlainRegion
