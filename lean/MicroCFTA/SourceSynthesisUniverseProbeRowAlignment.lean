import MicroCFTA.SourceSynthesisUniverseProbeRowReplay

/-!
# Ordered replay of the actual raw universe probe rows

The source rows and target rows use the same descriptor list.
Each target row is resident in the current constructor cache.
The actual edge requests therefore replay the target rows in order.
Descriptors can repeat. The statements do not compare canonical row order.
-/
namespace MicroCFTA.SourceSynthesisUniverseProbeRowAlignment
open Language
open Cache InternedConstructorTemplates InternedNestedFacts InternedEdgeResidency
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedBinderProtocol (Reference)
open SourceSynthesisUniverseBody (RowKeys)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- The same descriptor list aligns the literal source and target edge requests. -/
theorem catalog_rows_replay (top : Guard) (name probe : Reference)
    (descriptors : List (String × Nat)) (sources targets : List (EdgeValue String Guard))
    (current : InternedConstructorTemplates.State String Guard) (facts : Facts current)
    (sourceAligned : All₂ (RowKeys top name) descriptors sources)
    (targetAligned : All₂ (RowKeys top probe) descriptors targets)
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
            (SourceSynthesisUniverseProbeRowReplay.catalog_replay top name probe descriptor source target
              current facts (targetResident target List.mem_cons_self) sourceKeys targetKeys)
            (ih targets targetRest
              (fun row member => targetResident row (List.mem_cons_of_mem _ member)))

/-- The matching closed marker aligns the distinguished arrow before every catalog row. -/
theorem raw_rows_replay (top : Guard) (name probe : Reference) (marker : Value String Guard)
    (sourceArrow targetArrow : EdgeValue String Guard) (descriptors : List (String × Nat))
    (sources targets : List (EdgeValue String Guard))
    (current : InternedConstructorTemplates.State String Guard) (facts : Facts current)
    (closed : marker.free = [])
    (sourceChildren : sourceArrow.children = [marker, .reference name, .reference name])
    (sourceKey : sourceArrow.entry.key = ⟨"->", [marker.referenceOf, .ref name, .ref name], top⟩)
    (targetKey : targetArrow.entry.key = ⟨"->", [marker.referenceOf, .ref probe, .ref probe], top⟩)
    (sourceAligned : All₂ (RowKeys top name) descriptors sources)
    (targetAligned : All₂ (RowKeys top probe) descriptors targets)
    (targetResident : ∀ target ∈ targetArrow :: targets, EdgeResident current target) :
    All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top
        (source.children.map (input (replacement name (.reference probe))))) current =
          (target, current)) (sourceArrow :: sources) (targetArrow :: targets) := by
  exact .cons
    (SourceSynthesisUniverseProbeRowReplay.arrow_replay top name probe sourceArrow targetArrow marker
      current facts (targetResident targetArrow List.mem_cons_self) closed sourceChildren sourceKey targetKey)
    (catalog_rows_replay top name probe descriptors sources targets current facts sourceAligned targetAligned
      (fun row member => targetResident row (List.mem_cons_of_mem _ member)))

end MicroCFTA.SourceSynthesisUniverseProbeRowAlignment
