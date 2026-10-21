import MicroCFTA.SourceCurrentRequiredPositivePosition
import MicroCFTA.SourceCurrentNativeMuPublication
import MicroCFTA.InternedFreshOrdinaryFirstOrderHeap
import MicroCFTA.InternedUnionFilterFusion
import MicroCFTA.InternedStoredPlanBinderDepthExact
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Positive positions in an actual binder-free publication

The three callbacks retain one source body and one capture list. The body
contains no nested binder syntax. Captured Mu values remain opaque.
-/
namespace MicroCFTA.SourceCurrentBinderFreePublicationPositions
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (nodeEdges EdgeResident)
open InternedStoredMuOrigins (Normal)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNativeMuPublication (Publication)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard

private def RowsPositive (rows : List Row) : List Nat → Prop
  | [] => ∃ row ∈ rows, SourceMemoGate.plain row.entry.key.constraint = false
  | index :: rest => ∃ row ∈ rows, ∃ child, row.children[index]? = some child ∧ PositiveAt child rest

private theorem node_positive {entry rows depth free path} :
    PositiveAt (.node entry rows depth free) path ↔ RowsPositive rows path := by
  constructor
  · intro positive
    cases positive with
    | root index row selected nonplain => exact ⟨row,List.mem_of_getElem? selected,nonplain⟩
    | child index childIndex row child selected chosen rest => exact ⟨row,List.mem_of_getElem? selected,child,chosen,rest⟩
  · cases path with
    | nil =>
        rintro ⟨row,member,positive⟩
        obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
        exact .root index row selected positive
    | cons index path =>
        rintro ⟨row,member,child,chosen,positive⟩
        obtain ⟨rowIndex,selected⟩ := List.mem_iff_getElem?.mp member
        exact .child rowIndex index row child selected chosen positive

private theorem union_positive {entry members depth free path} :
    PositiveAt (.union entry members depth free) path ↔ ∃ child ∈ members, PositiveAt child path := by
  constructor
  · intro positive; cases positive with
    | member index child selected rest => exact ⟨child,List.mem_of_getElem? selected,rest⟩
  · rintro ⟨child,member,positive⟩
    obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
    exact .member index child selected positive

private theorem rows_members {first second : List Row}
    (same : ∀ row, row ∈ first ↔ row ∈ second) (path) :
    RowsPositive first path ↔ RowsPositive second path := by
  cases path <;> simp only [RowsPositive, same]

private theorem rows_append (first second : List Row) (path) :
    RowsPositive (first ++ second) path ↔ RowsPositive first path ∨ RowsPositive second path := by
  cases path <;> simp only [RowsPositive,List.mem_append,exists_or,or_and_right]
  all_goals aesop

section Physical
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem makeNode_positive (rows : List Row) (state : Heap) (normal : Normal state)
    (resident : Edges state rows) (path) :
    PositiveAt (run (makeNode rows) state).1 path ↔ RowsPositive (surviving rows) path := by
  have fields := EqualityLeafProjectionPhysical.makeNode_edges rows state normal.facts.coherent normal.facts.linked resident
  have kept : ∀ row ∈ surviving rows, EdgeResident state row :=
    fun row member => resident row (List.mem_filter.mp member).1
  have exactRows : RowsPositive (canonicalEdges (surviving rows)) path ↔ RowsPositive (surviving rows) path :=
    rows_members (fun row => ⟨canonicalEdges_member _ row,
      InternedNodeSetCongruence.canonicalEdges_retains state normal.facts.coherent _ row kept⟩) path
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows state normal.facts resident
  generalize value : (run (makeNode rows) state).1 = result at fields ordinary ⊢
  cases result with
  | empty =>
      have noRows : canonicalEdges (surviving rows) = [] := fields.symm
      rw [← exactRows,noRows]
      cases path <;> simp [RowsPositive]
      all_goals intro impossible; cases impossible
  | node entry rows depth free => rw [node_positive,← fields]; exact exactRows
  | reference | union | mu => cases ordinary

private theorem ordinary_positive (inputs : List Node) (rows : List Row)
    (actual : ordinaryEdges inputs = some rows) (path) :
    RowsPositive rows path ↔ ∃ input ∈ inputs, PositiveAt input path := by
  induction inputs generalizing rows with
  | nil => cases actual; cases path <;> simp [RowsPositive]
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at actual <;> try contradiction
      case node entry own depth free =>
        cases later : ordinaryEdges rest with
        | none => simp [later] at actual
        | some outputs =>
            have same : own ++ outputs = rows := by simpa only [later,Option.map_some,Option.some.injEq] using actual
            subst rows
            rw [rows_append,ih outputs later]
            simp only [List.mem_cons,exists_eq_or_imp,node_positive]

private theorem flattened_positive (inputs : List Node) (path) :
    (∃ input ∈ inputs.flatMap unionMembers, PositiveAt input path) ↔
      ∃ input ∈ inputs, PositiveAt input path := by
  simp only [List.mem_flatMap,exists_and_left]
  constructor
  · rintro ⟨input,source,member,selected,positive⟩
    cases source with
    | empty => cases selected
    | union entry members depth free => exact ⟨_,member,union_positive.mpr ⟨input,selected,positive⟩⟩
    | reference | node | mu =>
        have same := List.mem_singleton.mp selected
        exact ⟨_,member,same ▸ positive⟩
  · rintro ⟨input,member,positive⟩
    cases input with
    | empty | reference | mu => cases positive
    | node entry rows depth free => exact ⟨_,_,member,List.mem_singleton_self _,positive⟩
    | union entry members depth free =>
        obtain ⟨child,selected,positive⟩ := union_positive.mp positive
        exact ⟨child,_,member,selected,positive⟩

private theorem makeUnion_positive (inputs : List Node) (state : Heap) (normal : Normal state)
    (available : Values state inputs) (path) :
    PositiveAt (run (makeUnion inputs) state).1 path ↔ ∃ input ∈ inputs, PositiveAt input path := by
  have flatAvailable : Values state (inputs.flatMap unionMembers) := by
    intro value member
    obtain ⟨input,present,selected⟩ := List.mem_flatMap.mp member
    exact unionMembers_available input (available input present) value selected
  have selectedPositive :
      (∃ input ∈ distinctNodes (inputs.flatMap unionMembers), PositiveAt input path) ↔
        ∃ input ∈ inputs, PositiveAt input path := by
    rw [← flattened_positive inputs path]
    constructor
    · rintro ⟨input,member,positive⟩; exact ⟨input,distinctNodes_member _ _ member,positive⟩
    · rintro ⟨input,member,positive⟩
      exact ⟨input,InternedUnionRetention.distinctNodes_retains state normal.facts.coherent _
        (fun value member => (flatAvailable value member).resident) input member,positive⟩
  rw [← selectedPositive]
  cases selected : distinctNodes (inputs.flatMap unionMembers) with
  | nil => simp only [makeUnion,selected,run,List.not_mem_nil,false_and,exists_false]
           constructor <;> intro impossible <;> cases impossible
  | cons first rest =>
      cases rest with
      | nil => simp only [makeUnion,selected,run,List.mem_singleton,exists_eq_left]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | none =>
              obtain ⟨entry,readback⟩ := InternedUnionFilterFusion.union_readback inputs first second tail state
                normal.facts available selected ordinary
              rw [readback,union_positive,selected]
          | some rows =>
              have inputsAvailable : Values state (first :: second :: tail) := by
                simpa only [selected] using InternedUnionFilterFusion.selected_available inputs state available
              have resident := InternedEdgeResidency.ordinaryEdges_resident _ rows state normal.facts.linked
                (fun value member => (inputsAvailable value member).resident) ordinary
              have live := InternedStoredPlanBinderDepth.ordinaryEdges_surviving _ rows state normal.live inputsAvailable ordinary
              simpa only [makeUnion,selected,ordinary] using
                (makeNode_positive rows state normal resident path).trans (by rw [live]; exact ordinary_positive _ rows ordinary path)

private theorem filter_positive (name : InternedBinderProtocol.Reference) (value : Node) (state : Heap)
    (normal : Normal state) (available : Available state value) (path) :
    PositiveAt (run (withoutSelfReference name value) state).1 path ↔ PositiveAt value path := by
  cases value <;> simp only [withoutSelfReference,run] <;> try exact Iff.rfl
  case union entry members depth free =>
    split
    · rw [makeUnion_positive _ state normal (fun value member => available.children value (List.mem_filter.mp member).1),union_positive]
      constructor
      · rintro ⟨child,member,positive⟩; exact ⟨child,(List.mem_filter.mp member).1,positive⟩
      · rintro ⟨child,member,positive⟩
        refine ⟨child,List.mem_filter.mpr ⟨member,?_⟩,positive⟩
        apply Bool.eq_true_iff.mpr
        simp only [bne_iff_ne]
        intro equal
        have same := (referenceOf_self_iff name child).mp equal
        subst child
        cases positive
    · exact Iff.rfl

end Physical
end MicroCFTA.SourceCurrentBinderFreePublicationPositions
