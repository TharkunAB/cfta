import MicroCFTA.SourceSynthesisUniverseProbeRowReplay

/-!
# Probe row replay with the actual source name map

The same name map supplies the source and target keys.
The constructor heap keeps its original symbol type.
Resident complete rows determine each actual constructor result.
-/
namespace MicroCFTA.SourceSynthesisUniverseMappedProbeRows
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedRecordCoherence InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)

variable {Symbol Guard : Type}
set_option autoImplicit false

/-- Two available nullary markers with the same complete key have the same complete value. -/
theorem marker_eq (symbol : Symbol) (top : Guard)
    (leftEntry rightEntry : Interned NodeKey) (leftRow rightRow : EdgeValue Symbol Guard)
    (heap : State Symbol Guard) (facts : Facts heap)
    (leftAvailable : Available heap (.node leftEntry [leftRow] 0 []))
    (rightAvailable : Available heap (.node rightEntry [rightRow] 0 []))
    (leftKey : leftRow.entry.key = ⟨symbol, [], top⟩)
    (rightKey : rightRow.entry.key = ⟨symbol, [], top⟩) :
    Value.node leftEntry [leftRow] 0 [] = .node rightEntry [rightRow] 0 [] := by
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

/-- The same mapped catalog descriptor reconstructs its actual resident probe row. -/
theorem catalog_row_replay [DecidableEq (EdgeKey Symbol Guard)]
    (literal : String → Symbol) (top : Guard) (name probe : Reference) (descriptor : String × Nat)
    (source target : EdgeValue Symbol Guard) (current : State Symbol Guard)
    (facts : Facts current) (resident : EdgeResident current target)
    (sourceChildren : source.children = List.replicate descriptor.2 (.reference name))
    (sourceKey : source.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref name), top⟩)
    (targetKey : target.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref probe), top⟩) :
    run (makeEdge source.entry.key.symbol top
      (source.children.map (input (replacement name (.reference probe))))) current = (target, current) := by
  apply SourceSynthesisUniverseProbeRowReplay.resident_edge_replay source.entry.key.symbol top _ target
    current facts resident
  rw [sourceKey, sourceChildren]
  simpa [input, replacement, Value.referenceOf] using targetKey

/-- The mapped arrow retains its complete closed marker and replaces both local references. -/
theorem arrow_row_replay [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (top : Guard) (name probe : Reference)
    (source target : EdgeValue Symbol Guard) (marker : Value Symbol Guard)
    (current : State Symbol Guard) (facts : Facts current) (resident : EdgeResident current target)
    (closed : marker.free = [])
    (sourceChildren : source.children = [marker, .reference name, .reference name])
    (sourceKey : source.entry.key = ⟨symbol, [marker.referenceOf, .ref name, .ref name], top⟩)
    (targetKey : target.entry.key = ⟨symbol, [marker.referenceOf, .ref probe, .ref probe], top⟩) :
    run (makeEdge source.entry.key.symbol top
      (source.children.map (input (replacement name (.reference probe))))) current = (target, current) := by
  have markerRead := InternedStoredSubstitutionScope.input_closed marker
    (replacement name (.reference probe)) closed
  have referenceRead : input (replacement name (.reference probe))
      (.reference name : Value Symbol Guard) = .reference probe := by
    simp [input, replacement]
  have mappedChildren : source.children.map (input (replacement name (.reference probe))) =
      [marker, .reference probe, .reference probe] := by
    rw [sourceChildren]
    simp only [List.map_cons, List.map_nil, markerRead, referenceRead]
  apply SourceSynthesisUniverseProbeRowReplay.resident_edge_replay source.entry.key.symbol top _ target
    current facts resident
  rw [mappedChildren, sourceKey]
  exact targetKey

/-- The actual descriptor list aligns the complete source and target catalog rows. -/
theorem catalog_rows_replay [DecidableEq (EdgeKey Symbol Guard)]
    (literal : String → Symbol) (top : Guard) (name probe : Reference)
    (descriptors : List (String × Nat)) (sources targets : List (EdgeValue Symbol Guard))
    (current : State Symbol Guard) (facts : Facts current)
    (sourceAligned : All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference name) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref name), top⟩) descriptors sources)
    (targetAligned : All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference probe) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref probe), top⟩) descriptors targets)
    (targetResident : ∀ target ∈ targets, EdgeResident current target) :
    All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top
        (source.children.map (input (replacement name (.reference probe))))) current =
          (target, current)) sources targets := by
  induction sourceAligned generalizing targets with
  | nil => cases targetAligned; exact .nil
  | @cons descriptor source descriptors sources sourceKeys rest ih =>
      cases targetAligned with
      | @cons _ target _ targets targetKeys targetRest =>
          exact .cons
            (catalog_row_replay literal top name probe descriptor source target current facts
              (targetResident target List.mem_cons_self) sourceKeys.1 sourceKeys.2 targetKeys.2)
            (ih targets targetRest (fun row member => targetResident row (List.mem_cons_of_mem _ member)))

/-- One actual marker and the shared name map align the full raw probe request. -/
theorem raw_rows_replay [DecidableEq (EdgeKey Symbol Guard)]
    (literal : String → Symbol) (top : Guard) (name probe : Reference) (marker : Value Symbol Guard)
    (sourceArrow targetArrow : EdgeValue Symbol Guard) (descriptors : List (String × Nat))
    (sources targets : List (EdgeValue Symbol Guard)) (current : State Symbol Guard) (facts : Facts current)
    (closed : marker.free = [])
    (sourceChildren : sourceArrow.children = [marker, .reference name, .reference name])
    (sourceKey : sourceArrow.entry.key = ⟨literal "->", [marker.referenceOf, .ref name, .ref name], top⟩)
    (targetKey : targetArrow.entry.key = ⟨literal "->", [marker.referenceOf, .ref probe, .ref probe], top⟩)
    (sourceAligned : All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference name) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref name), top⟩) descriptors sources)
    (targetAligned : All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference probe) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref probe), top⟩) descriptors targets)
    (targetResident : ∀ target ∈ targetArrow :: targets, EdgeResident current target) :
    All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top
        (source.children.map (input (replacement name (.reference probe))))) current =
          (target, current)) (sourceArrow :: sources) (targetArrow :: targets) := by
  exact .cons
    (arrow_row_replay (literal "->") top name probe sourceArrow targetArrow marker current facts
      (targetResident targetArrow List.mem_cons_self) closed sourceChildren sourceKey targetKey)
    (catalog_rows_replay literal top name probe descriptors sources targets current facts sourceAligned targetAligned
      (fun row member => targetResident row (List.mem_cons_of_mem _ member)))

#print axioms marker_eq
#print axioms catalog_row_replay
#print axioms arrow_row_replay
#print axioms catalog_rows_replay
#print axioms raw_rows_replay

end MicroCFTA.SourceSynthesisUniverseMappedProbeRows
