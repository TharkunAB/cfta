import MicroCFTA.SourceSynthesisUniverseColdFrames
import MicroCFTA.SourceSynthesisUniverseResidentRows

/-!
# Resident raw rows of the actual cold universe and its probes

The actual callback frames supply all three raw row packets. Their record
growth puts the packets in the completed universe heap. Availability of the
stored body and both probes follows from the returned Mu record.
-/
namespace MicroCFTA.SourceSynthesisUniverseColdResidentRows
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisTypeSyntax
open SourceSynthesisUniverseResidentRows (Rows)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

private theorem rows_of_callback (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (before : InternedConstructorTemplates.State String Guard) (facts : Facts before)
    (available : Available before (.reference name)) (value : Value String Guard)
    (after : InternedConstructorTemplates.State String Guard)
    (done : InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) [] name before =
      .done value after) : Rows top catalog name value after := by
  obtain ⟨actual, final, completed, _finalFacts, _finalAvailable, rows⟩ :=
    SourceSynthesisUniverseResidentRows.callback_rows top catalog name before facts available
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj (done.symm.trans completed)
  exact rows

/-- Cold construction derives the body and both probe row packets in its actual final heap. -/
theorem allTypes_cold_rows (top : Guard) (catalog : List (String × Nat)) :
    ∃ entry body depth ordinary heap,
      InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] empty =
        .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity) body ∧
      Rows top catalog (.interned entry.identity) body heap ∧
      Rows top catalog .depth depth heap ∧
      Rows top catalog (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary heap ∧
      Available heap body ∧ Available heap depth ∧ Available heap ordinary := by
  obtain ⟨entry, body, depth, ordinary, heap, afterDepth, afterOrdinary, afterBody,
      done, facts, available, shape, depthDone, ordinaryDone, bodyDone, _entryEq, _missing,
      depthFacts, _ordinaryFacts, allocatedFacts, freshAvailable, _bodyFacts, _publication,
      depthGrowth, ordinaryGrowth, _allocatedGrowth, bodyGrowth⟩ :=
    SourceSynthesisUniverseColdFrames.allTypes_cold_frames top catalog
  have depthRows := rows_of_callback top catalog .depth empty empty_facts
    (InternedNestedProvenance.depth_available empty) depth afterDepth depthDone
  have ordinaryRows := rows_of_callback top catalog
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthFacts
    (InternedNestedProvenance.ordinary_available afterDepth _) ordinary afterOrdinary ordinaryDone
  have bodyRows := rows_of_callback top catalog (.interned entry.identity) _ allocatedFacts
    freshAvailable body afterBody bodyDone
  exact ⟨entry, body, depth, ordinary, heap, done, facts, available, shape,
    bodyRows.grows bodyGrowth, depthRows.grows depthGrowth, ordinaryRows.grows ordinaryGrowth,
    available.children body (by simp [InternedProbeProvenance.children]),
    available.children depth (by simp [InternedProbeProvenance.children]),
    available.children ordinary (by simp [InternedProbeProvenance.children])⟩

end MicroCFTA.SourceSynthesisUniverseColdResidentRows
