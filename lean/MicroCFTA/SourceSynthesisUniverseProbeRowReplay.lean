import MicroCFTA.SourceSynthesisUniverseBody
import MicroCFTA.InternedStoredSubstitutionRebind

/-!
# Physical replay of universe rows at a probe reference

An actual resident target edge fixes the complete cache result.
Catalog rows replace each source reference with the probe reference.
The arrow row also retains its original closed marker.
The actual edge request then returns the target without a cache effect.
-/
namespace MicroCFTA.SourceSynthesisUniverseProbeRowReplay
open Cache InternedConstructorTemplates InternedNestedFacts InternedEdgeResidency
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceSynthesisUniverseBody (RowKeys)

variable {Symbol Guard : Type}

/-- The actual constructor reuses a resident edge with the exact requested key. -/
theorem resident_edge_replay [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (top : Guard) (children : List (Value Symbol Guard))
    (target : EdgeValue Symbol Guard) (current : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts current) (resident : EdgeResident current target)
    (key : target.entry.key = ⟨symbol, children.map Value.referenceOf, top⟩) :
    run (makeEdge symbol top children) current = (target, current) := by
  have stored : current.edgeRecords target.entry.key = some target := resident
  have installed := (facts.coherent.edges target.entry.key target resident).1
  simp only [makeEdge, run, edgeStep, key.symm, Cache.intern,
    installed, keepFirst, stored, Option.getD_some]

/-- Every literal catalog position reads the probe and reuses its resident target row. -/
theorem catalog_replay [DecidableEq (EdgeKey String Guard)]
    (top : Guard) (name probe : Reference) (descriptor : String × Nat)
    (source target : EdgeValue String Guard) (current : InternedConstructorTemplates.State String Guard)
    (facts : Facts current) (resident : EdgeResident current target)
    (sourceKeys : RowKeys top name descriptor source) (targetKeys : RowKeys top probe descriptor target) :
    run (makeEdge source.entry.key.symbol top
      (source.children.map (input (replacement name (.reference probe))))) current = (target, current) := by
  apply resident_edge_replay source.entry.key.symbol top _ target current facts resident
  rw [sourceKeys.2, sourceKeys.1]
  simpa [input, replacement, Value.referenceOf] using targetKeys.2

/-- The literal arrow request keeps its closed marker before the two probe references. -/
theorem arrow_replay [DecidableEq (EdgeKey String Guard)]
    (top : Guard) (name probe : Reference) (source target : EdgeValue String Guard)
    (marker : Value String Guard) (current : InternedConstructorTemplates.State String Guard)
    (facts : Facts current) (resident : EdgeResident current target) (closed : marker.free = [])
    (sourceChildren : source.children = [marker, .reference name, .reference name])
    (sourceKey : source.entry.key = ⟨"->", [marker.referenceOf, .ref name, .ref name], top⟩)
    (targetKey : target.entry.key = ⟨"->", [marker.referenceOf, .ref probe, .ref probe], top⟩) :
    run (makeEdge source.entry.key.symbol top
      (source.children.map (input (replacement name (.reference probe))))) current = (target, current) := by
  have markerRead := InternedStoredSubstitutionScope.input_closed marker
    (replacement name (.reference probe)) closed
  have referenceRead : input (replacement name (.reference probe))
      (.reference name : Value String Guard) = .reference probe := by
    simp [input, replacement]
  have mappedChildren : source.children.map (input (replacement name (.reference probe))) =
      [marker, .reference probe, .reference probe] := by
    rw [sourceChildren]
    simp only [List.map_cons, List.map_nil, markerRead, referenceRead]
  apply resident_edge_replay source.entry.key.symbol top _ target current facts resident
  rw [mappedChildren, sourceKey]
  exact targetKey

end MicroCFTA.SourceSynthesisUniverseProbeRowReplay
