import MicroCFTA.SourceCurrentPrimaryEndpointCap
import MicroCFTA.SourceCurrentRequiredPrimaryExposure
import MicroCFTA.SourceEqualityProjectionLanguage
import MicroCFTA.SourceEqualityRequiredExecution

/-!
# Raw finite endpoint corridors through actual Required

Each corridor bounds a whole region or follows the same selected child in
every raw ordinary row. The actual original false gates derive all selected
corridors of the prepared forest. Unrelated siblings need no supplied cap.
-/
namespace MicroCFTA.SourceCurrentRequiredRawCorridor
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityAnnotationLanguage EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (Origin RowMap ChildMap)
open SourceCurrentConstrainedCap (Cap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
private def Finite (value : Node) : Prop := ∃ depth, Cap Plain depth value

private theorem uniform (values : List Node) (all : ∀ value ∈ values, Finite value) :
    ∃ depth, ∀ value ∈ values, Cap Plain depth value := by
  induction values with
  | nil => exact ⟨0,by intro value member; cases member⟩
  | cons value values ih =>
    obtain ⟨first,bounded⟩ := all value List.mem_cons_self
    obtain ⟨rest,others⟩ := ih (fun child member => all child (List.mem_cons_of_mem _ member))
    refine ⟨max first rest,?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | later
    · exact bounded.mono (Nat.le_max_left _ _)
    · exact (others child later).mono (Nat.le_max_right _ _)

private theorem child_finite {value : Node} (bounded : Finite value) (row : Row)
    (member : row ∈ nodeEdges value) (child : Node) (inside : child ∈ row.children) : Finite child := by
  obtain ⟨depth,bounded⟩ := bounded
  have localRow := SourceCurrentConstrainedCap.node_edge bounded row member
  cases depth with
  | zero => exact ⟨0,.plain 0 (localRow.2 child inside)⟩
  | succ depth => exact ⟨depth,localRow child inside⟩

private theorem ordinary_finite (value : Node) (ordinary : Ordinary value)
    (children : ∀ row ∈ nodeEdges value, ∀ child ∈ row.children, Finite child) : Finite value := by
  cases value with
  | empty => exact ⟨0,.plain 0 .empty⟩
  | reference | union | mu => cases ordinary
  | node entry rows depth free =>
    obtain ⟨bound,bounded⟩ := uniform (rows.flatMap EdgeValue.children) (by
      intro child member
      obtain ⟨row,selected,inside⟩ := List.mem_flatMap.mp member
      exact children row selected child inside)
    exact ⟨bound+1,.node bound entry rows depth free bounded⟩

private theorem origin_finite {original prepared : Node} (origin : Origin original prepared) :
    Finite original → Finite prepared := by
  apply Origin.rec
    (motive_1 := fun original prepared _ => Finite original → Finite prepared)
    (motive_2 := fun originals outputs _ =>
      (∀ row ∈ originals, ∀ child ∈ row.children, Finite child) →
      ∀ row ∈ outputs, ∀ child ∈ row.children, Finite child)
    (motive_3 := fun originals outputs _ =>
      (∀ child ∈ originals, Finite child) → ∀ child ∈ outputs, Finite child)
    (t := origin)
  · intro value bounded; exact bounded
  · intro original prepared annotated _; exact ⟨0,.plain 0 annotated⟩
  · intro entry originals level free result ordinary mapped ih bounded
    exact ordinary_finite result ordinary (ih (fun row member child inside => child_finite bounded row member child inside))
  · intro originals _ row member; cases member
  · intro originals outputs sourceIndex original output found fields children rest childIH restIH rows row member
    rcases List.mem_cons.mp member with rfl | later
    · exact childIH (rows original (List.mem_of_getElem? found))
    · exact restIH rows row later
  · intro children child member; cases member
  · intro original output originals outputs first rest firstIH restIH children child member
    rcases List.mem_cons.mp member with rfl | later
    · exact firstIH (children original List.mem_cons_self)
    · exact restIH (fun child member => children child (List.mem_cons_of_mem _ member)) child later

/-- A finite endpoint region or every raw selected ordinary child has the remaining corridor. -/
inductive RawCorridor : List Int → Node → Prop where
  | full (path value) (bounded : ∃ depth, Cap Plain depth value) : RawCorridor path value
  | node (entry) (rows : List Row) (depth free index path)
      (children : ∀ row ∈ rows, ∀ child, select row.children index = some child → RawCorridor path child) :
      RawCorridor (index::path) (.node entry rows depth free)

/-- Actual Required origins preserve each raw corridor at the same signed path. -/
theorem origin {path original prepared} (safe : RawCorridor path original)
    (origin : Origin original prepared) : RawCorridor path prepared := by
  induction path generalizing original prepared with
  | nil => cases safe with | full _ _ bounded => exact .full _ _ (origin_finite origin bounded)
  | cons index path ih =>
    cases origin with
    | identity value => exact safe
    | plain original prepared annotated => exact .full _ _ ⟨0,.plain 0 annotated⟩
    | ordinary entry originals level free prepared ordinary mapped =>
      cases safe with
      | full _ _ bounded => exact .full _ _ (origin_finite (.ordinary entry originals level free prepared ordinary mapped) bounded)
      | node _ _ _ _ _ _ children =>
        cases prepared with
        | empty => exact .full _ _ ⟨0,.plain 0 .empty⟩
        | reference | union | mu => cases ordinary
        | node entry rows depth free =>
          apply RawCorridor.node
          intro row member child selected
          obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
          obtain ⟨sourceIndex,sourceRow,original,fields,related⟩ := mapped.indexed position row found
          obtain ⟨sourceChild,sourceFound,childOrigin⟩ := SourceEqualityProjectionLanguage.all₂_signed related index child selected
          exact ih (children sourceRow (List.mem_of_getElem? original) sourceChild sourceFound) childOrigin

noncomputable local instance : DecidableEq (EdgeKey Symbol Guard) :=
  SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint

private theorem gate_corridor (path : List Nat) (value : Node) (anchor before after : Heap)
    (semantic : SemanticReady anchor) (available : Available anchor value)
    (current : SemanticReady before) (resident : Available before value)
    (gate : NodeTrace source reaches path value before false after) : RawCorridor (path.map Int.ofNat) value := by
  induction path generalizing value before after with
  | nil => exact .full _ _ ⟨_,SourceCurrentPrimaryEndpointCap.endpoint_cap before
      current.ready.semantic.1.normal.facts.coherent value resident gate⟩
  | cons index path ih =>
    cases value with
    | empty => exact .full _ _ ⟨0,.plain 0 .empty⟩
    | reference | union => cases gate
    | mu entry body depth ordinary =>
      have accepted : source (.mu entry body depth ordinary) = true := by
        cases gate with
        | closed accepted _ => exact accepted
        | unfold accepted _ _ _ => exact accepted
      exact .full _ _ ⟨0,.plain 0 (SourceCurrentGatePlainRegion.annotations anchor _
        semantic.ready.semantic.1.normal.facts.coherent available accepted)⟩
    | node entry rows depth free =>
      cases gate with
      | finite fast =>
        exact .full _ _ ⟨_,SourceCurrentPrimaryEndpointCap.reaches_cap anchor
          semantic.ready.semantic.1.normal.facts.coherent _ available
          (SourceEndpointReachability.zero_clear source _
            (by simpa only [Value.depth,beq_iff_eq] using (Bool.and_eq_true_iff.mp fast).1))⟩
      | branches slow scanned =>
        have effects := SourceCurrentPrimaryReplay.edges_replay source reaches index path rows before false after
          scanned current (fun child member => resident.children child member)
        apply RawCorridor.node entry rows depth free (Int.ofNat index) (path.map Int.ofNat)
        intro row member child found
        have natural : row.children[index]? = some child := by
          simpa only [select,Int.ofNat_eq_natCast,
            ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using found
        have traced := SourceCurrentRequiredPrimaryExposure.false_selected (SourceCurrentRequiredPrimaryExposure.false_edges_members index path rows before after scanned current
          (fun child member => resident.children child member) after (grows_refl _) row member) natural
        have inside := List.mem_flatMap.mpr ⟨row,member,select_member found⟩
        exact ih child after after (available.children child inside) effects.1
          (effects.2.1.available child (resident.children child inside)) traced

/-- An actual original false gate supplies its raw signed corridor. -/
theorem original_gate [edgeEq : DecidableEq (EdgeKey Symbol Guard)]
    (path : List Nat) (value : Node) (before after : Heap)
    (semantic : SemanticReady before) (available : Available before value)
    (actual : NodeTrace source reaches path value before false after) :
    RawCorridor (path.map Int.ofNat) value := by
  have sameEdge : edgeEq = SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint :=
    Subsingleton.elim _ _
  cases sameEdge
  exact gate_corridor path value before before after semantic available semantic available actual

/-- The literal Required return retains every original selected slot and raw endpoint corridor. -/
theorem required [edgeEq : DecidableEq (EdgeKey Symbol Guard)]
    {requiredFuel requiredReadFuel : Nat}
    {selected : EqualityNormalize.Constraints} {originals prepared : List Node}
    {scanHeap preparedHeap : Heap}
    (actual : SourceEqualityRequiredExecution.requireAll requiredFuel requiredReadFuel
      (SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap)
    (semantic : SemanticReady scanHeap) (normal : SourceCurrentRequiredUnionNormal.UnionNormal scanHeap)
    (costs : CostHeap scanHeap) (available : Values scanHeap originals) (guards : Guards scanHeap)
    (primary : ∀ paths ∈ selected, ClassTrace source reaches originals paths scanHeap false scanHeap) :
    ∀ chosenClass ∈ selected, ∀ index path, index :: path ∈ chosenClass →
      ∀ value, prepared[index]? = some value →
        ∃ original, originals[index]? = some original ∧ Origin original value ∧
          RawCorridor (path.map Int.ofNat) value := by
  have sameEdge : edgeEq = SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint :=
    Subsingleton.elim _ _
  cases sameEdge
  letI : DecidableEq (EdgeKey Symbol Guard) :=
    SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff
    (SourceEqualitySelectedRequired.paths selected) originals scanHeap prepared preparedHeap).mpr
      ⟨requiredFuel, requiredReadFuel, actual⟩
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected) with
  | node entries =>
    simp only [compiled] at graph
    have domain := SourceCurrentRequiredPrimaryExposure.selected_domain originals selected scanHeap
      semantic normal available primary entries compiled
    have safe : SourceCurrentRequiredRowOrigins.ChildrenSafe entries 0 originals := by
      intro offset needed selectedNeeded value atOffset
      exact domain offset needed (by simpa only [Nat.zero_add] using selectedNeeded) value atOffset
    have related : All₂ Origin originals prepared :=
      SourceCurrentRequiredRowOrigins.children graph semantic costs available guards safe
    intro chosenClass chosen index path included value found
    obtain ⟨original, originalFound, mapped⟩ :=
      SourceEqualityProjectionLanguage.all₂_selected related index value found
    have gatePath := SourceCurrentRequiredPrimaryExposure.false_class_paths originals chosenClass scanHeap scanHeap
      (primary chosenClass chosen) semantic available scanHeap (grows_refl _) (index :: path) included
    have gate : NodeTrace source reaches path original scanHeap false scanHeap := by
      cases gatePath with
      | child traced => exact SourceCurrentRequiredPrimaryExposure.false_selected traced originalFound
    exact ⟨original, originalFound, mapped,
      origin (original_gate path original scanHeap scanHeap semantic
        (available _ (List.mem_of_getElem? originalFound)) gate) mapped⟩

end MicroCFTA.SourceCurrentRequiredRawCorridor
