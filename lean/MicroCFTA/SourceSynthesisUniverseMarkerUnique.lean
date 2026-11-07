import MicroCFTA.SourceSynthesisUniverseBody

/-!
# Physical identity of resident source markers

Two available nullary rows with the same symbol and guard use the same
edge record. Their singleton nodes then use the same node record.
This compares complete payloads in the actual current constructor cache.
-/
namespace MicroCFTA.SourceSynthesisUniverseMarkerUnique
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedRecordCoherence InternedEdgeResidency
open SourceSynthesisUniverseBody (RowReadback)

variable {Guard : Type}

/-- Available marker readbacks with the same nullary key have identical complete values. -/
theorem marker_eq (label : String) (top : Guard) (left right : Value String Guard)
    (heap : State String Guard) (facts : Facts heap)
    (leftAvailable : Available heap left) (rightAvailable : Available heap right)
    (leftRead : RowReadback label top [] left) (rightRead : RowReadback label top [] right) :
    left = right := by
  obtain ⟨leftEntry, leftRow, leftEq, _, leftKey⟩ := leftRead
  obtain ⟨rightEntry, rightRow, rightEq, _, rightKey⟩ := rightRead
  subst left right
  have leftStored := leftAvailable.resident leftEntry rfl
  have rightStored := rightAvailable.resident rightEntry rfl
  have leftResident : EdgeResident heap leftRow :=
    facts.linked leftEntry.key _ leftStored leftRow (List.mem_singleton_self leftRow)
  have rightResident : EdgeResident heap rightRow :=
    facts.linked rightEntry.key _ rightStored rightRow (List.mem_singleton_self rightRow)
  have first : heap.edgeRecords leftRow.entry.key = some leftRow := leftResident
  have second : heap.edgeRecords rightRow.entry.key = some rightRow := rightResident
  rw [leftKey] at first
  rw [rightKey] at second
  have rowEq : leftRow = rightRow := Option.some.inj (first.symm.trans second)
  subst rightRow
  obtain ⟨_, firstTable, firstFields⟩ := facts.coherent.nodes leftEntry.key _ leftStored
  obtain ⟨_, secondTable, secondFields⟩ := facts.coherent.nodes rightEntry.key _ rightStored
  have firstKey : leftEntry.key = .node [leftRow.entry.identity] := firstFields.2.1
  have secondKey : rightEntry.key = .node [leftRow.entry.identity] := secondFields.2.1
  have firstEntry : heap.nodes.table leftEntry.key = some leftEntry :=
    firstTable.trans (congrArg some firstFields.1.symm)
  have secondEntry : heap.nodes.table rightEntry.key = some rightEntry :=
    secondTable.trans (congrArg some secondFields.1.symm)
  rw [firstKey] at firstEntry
  rw [secondKey] at secondEntry
  have entryEq : leftEntry = rightEntry := Option.some.inj (firstEntry.symm.trans secondEntry)
  subst rightEntry
  rfl

end MicroCFTA.SourceSynthesisUniverseMarkerUnique
