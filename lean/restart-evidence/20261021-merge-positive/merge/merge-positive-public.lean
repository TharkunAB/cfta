import MicroCFTA.MergedPhysicalGroupEdges
import MicroCFTA.MergedOrdinaryHeight
import MicroCFTA.InternedUnionRetention
import MicroCFTA.EqualityLeafProjectionPhysical
import MicroCFTA.SourceCurrentRequiredPositivePosition
import MicroCFTA.SourceCurrentMemoMergeLanguageCertified
import MicroCFTA.SourceCurrentMemoMergeWorkerProofs
import MicroCFTA.SourceCurrentAllocatedMergeWorkerSound

/-! # Positive finite child positions through actual memo-aware Merge calls -/
namespace MicroCFTA.SourceCurrentMergePositivePosition
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
open SourceCurrentRequiredPositivePosition (PositiveAt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Each completed entry retains positive positions of its full captured original. -/
def Support (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → ∀ path, PositiveAt entry.result path → PositiveAt entry.original path

/-- The empty table contains no unsupported result. -/
theorem support_empty : Support (empty : Memo Symbol Guard) := by
  intro key entry found
  cases found

private theorem support_remember {memo : Memo Symbol Guard} (support : Support memo)
    (input output : Node) (law : ∀ path, PositiveAt output path → PositiveAt input path) :
    Support (remember memo input output) := by
  intro key entry found
  rcases remember_cases memo input output key entry found with old | ⟨_, same⟩
  · exact support key entry old
  · subst entry
    exact law

private abbrev Positions (inputs : List Node) (output : Node) : Prop :=
  ∀ path, PositiveAt output path → ∃ input ∈ inputs, PositiveAt input path
private abbrev RowPositions (inputs : List Row) (output : Row) : Prop :=
  (SourceMemoGate.plain output.entry.key.constraint = false →
    ∃ input ∈ inputs, SourceMemoGate.plain input.entry.key.constraint = false) ∧
  ∀ (index : Nat) (child : Node), output.children[index]? = some child → ∀ path, PositiveAt child path →
    ∃ input ∈ inputs, ∃ original, input.children[index]? = some original ∧ PositiveAt original path
private abbrev ValuePost (inputs : List Node) (heap : Heap) (output : Node) : Prop :=
  ValueReady heap output ∧ Positions inputs output
private abbrev EdgePost (inputs : List Row) (heap : Heap) (output : Row) : Prop :=
  EdgeReady heap output ∧ RowPositions inputs output
private abbrev RowsPost (inputs : List Row) (heap : Heap) (outputs : List Row) : Prop :=
  ∀ row ∈ outputs, EdgePost inputs heap row
private abbrev RequestContract (input : Node) (before : Heap) (output : Node) (after : Heap) : Prop :=
  SourceCurrentMemoMergeEffects.Contract input before output after ∧
    ∀ path, PositiveAt output path → PositiveAt input path

private theorem value_post_grows {inputs before after output} (effect : Effect before after)
    (ready : ValuePost inputs before output) : ValuePost inputs after output :=
  ⟨value_grows effect output ready.1, ready.2⟩
private theorem edge_post_grows {inputs before after output} (effect : Effect before after)
    (ready : EdgePost inputs before output) : EdgePost inputs after output :=
  ⟨edge_grows effect output ready.1, ready.2⟩

private theorem paired_output {A B : Type} {inputs : List A} {outputs : List B} {relation : A → B → Prop}
    (related : All₂ relation inputs outputs) (output : B) (member : output ∈ outputs) :
    ∃ input ∈ inputs, relation input output := by
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨input, found, law⟩ := SourceEqualityProjectionLanguage.all₂_selected related index output selected
  exact ⟨input, List.mem_of_getElem? found, law⟩



open InternedEdgeResidency (nodeEdges)
open InternedNestedFacts (Facts)

private theorem columns_indexed {A : Type} (rows : List (List A)) (arity index : Nat) (column : List A)
    (selected : (MergedAlternativesGroups.columns rows arity)[index]? = some column) :
    ∀ value ∈ column, ∃ row ∈ rows, row[index]? = some value := by
  induction arity generalizing rows index with
  | zero => simp only [MergedAlternativesGroups.columns, List.getElem?_nil] at selected; cases selected
  | succ arity ih =>
      cases index with
      | zero =>
          simp only [MergedAlternativesGroups.columns, List.getElem?_cons_zero, Option.some.injEq] at selected
          subst column
          intro value member
          obtain ⟨row, present, found⟩ := List.mem_filterMap.mp member
          exact ⟨row, present, by cases row <;> exact found⟩
      | succ index =>
          have later : (MergedAlternativesGroups.columns (rows.map List.tail) arity)[index]? = some column := by
            simpa only [MergedAlternativesGroups.columns, List.getElem?_cons_succ] using selected
          intro value member
          obtain ⟨tail, included, found⟩ := ih _ index later value member
          obtain ⟨row, present, rfl⟩ := List.mem_map.mp included
          refine ⟨row, present, ?_⟩
          cases row with
          | nil => simp only [List.tail_nil, List.getElem?_nil] at found; cases found
          | cons first rest => exact found

section Constructors

private theorem makeNode_positive [DecidableEq (EdgeKey Symbol Guard)] (state : Heap) (facts : Facts state) (rows : List Row)
    (resident : Edges state rows) {entry depth free path}
    (positive : PositiveAt (run (makeNode rows) state).1 path) :
    PositiveAt (.node entry rows depth free) path := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows state facts resident
  have fields := EqualityLeafProjectionPhysical.makeNode_edges rows state facts.coherent facts.linked resident
  have raw : ∀ row ∈ nodeEdges (run (makeNode rows) state).1, row ∈ rows := by
    intro row member
    exact (List.mem_filter.mp (canonicalEdges_member _ row (fields ▸ member))).1
  generalize computed : (run (makeNode rows) state).1 = result at positive ordinary raw
  cases positive with
  | root rowIndex row selected nonplain =>
      obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp (raw row (List.mem_of_getElem? selected))
      exact .root sourceIndex row found nonplain
  | child rowIndex childIndex row child selected chosen rest =>
      obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp (raw row (List.mem_of_getElem? selected))
      exact .child sourceIndex childIndex row child found chosen rest
  | member memberIndex child selected rest => cases ordinary

private theorem rows_positive (inputs : List Node) (rows : List Row)
    (covered : ∀ row ∈ rows, ∃ input ∈ inputs, row ∈ nodeEdges input) {entry depth free path}
    (positive : PositiveAt (.node entry rows depth free) path) :
    ∃ input ∈ inputs, PositiveAt input path := by
  cases positive with
  | root rowIndex row selected nonplain =>
      obtain ⟨input, member, present⟩ := covered row (List.mem_of_getElem? selected)
      cases input with
      | node source originals level names =>
          obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp present
          exact ⟨_, member, .root sourceIndex row found nonplain⟩
      | empty | reference | union | mu => cases present
  | child rowIndex childIndex row child selected chosen rest =>
      obtain ⟨input, member, present⟩ := covered row (List.mem_of_getElem? selected)
      cases input with
      | node source originals level names =>
          obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp present
          exact ⟨_, member, .child sourceIndex childIndex row child found chosen rest⟩
      | empty | reference | union | mu => cases present

private theorem ordinary_edges_rows (inputs : List Node) (rows : List Row)
    (actual : ordinaryEdges inputs = some rows) :
    ∀ row ∈ rows, ∃ input ∈ inputs, row ∈ nodeEdges input := by
  induction inputs generalizing rows with
  | nil => cases actual; intro row impossible; cases impossible
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at actual <;> try contradiction
      case node entry originals depth free =>
        cases later : ordinaryEdges rest with
        | none => simp only [later, Option.map_none] at actual; cases actual
        | some outputs =>
            have same : originals ++ outputs = rows := by simpa only [later, Option.map_some, Option.some.injEq] using actual
            subst rows
            intro row member
            rcases List.mem_append.mp member with here | there
            · exact ⟨_, List.mem_cons_self, here⟩
            · obtain ⟨input, present, found⟩ := ih outputs later row there
              exact ⟨input, List.mem_cons_of_mem _ present, found⟩

private theorem flatten_positive (inputs : List Node) {input path}
    (member : input ∈ inputs.flatMap unionMembers) (positive : PositiveAt input path) :
    ∃ original ∈ inputs, PositiveAt original path := by
  obtain ⟨original, present, chosen⟩ := List.mem_flatMap.mp member
  cases original with
  | empty => cases chosen
  | union entry members depth free =>
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp chosen
      exact ⟨_, present, .member index input selected positive⟩
  | reference | node | mu =>
      have same := List.mem_singleton.mp chosen
      exact ⟨_, present, same ▸ positive⟩

private theorem ordinaryUnion_positive [DecidableEq (EdgeKey Symbol Guard)] (state : Heap) (facts : Facts state) (inputs : List Node)
    (available : Values state inputs) {path}
    (positive : PositiveAt (run (MergedOrdinaryHeight.ordinaryUnion inputs) state).1 path) :
    ∃ input ∈ inputs, PositiveAt input path := by
  have resident : Edges state (inputs.flatMap nodeEdges) := by
    intro row member
    obtain ⟨input, present, selected⟩ := List.mem_flatMap.mp member
    exact InternedEdgeResidency.resident_edges state facts.linked input (available input present).resident row selected
  have structural := makeNode_positive state facts _ resident
    (entry := ⟨0, .node []⟩) (depth := 0) (free := []) positive
  exact rows_positive inputs _ (fun row member => List.mem_flatMap.mp member) structural

private theorem makeUnion_positive [DecidableEq (EdgeKey Symbol Guard)] (state : Heap) (facts : Facts state) (inputs : List Node)
    (available : Values state inputs) {path}
    (positive : PositiveAt (run (makeUnion inputs) state).1 path) :
    ∃ input ∈ inputs, PositiveAt input path := by
  have retained : Values state (distinctNodes (inputs.flatMap unionMembers)) := by
    intro input member
    obtain ⟨original, present, chosen⟩ := List.mem_flatMap.mp (distinctNodes_member _ _ member)
    exact unionMembers_available original (available original present) input chosen
  have fromMember : ∀ input ∈ distinctNodes (inputs.flatMap unionMembers), PositiveAt input path →
      ∃ original ∈ inputs, PositiveAt original path := by
    intro input member positive
    exact flatten_positive inputs (distinctNodes_member _ _ member) positive
  cases normalized : distinctNodes (inputs.flatMap unionMembers) with
  | nil => simp only [makeUnion, normalized, run] at positive; cases positive
  | cons first rest =>
      cases rest with
      | nil =>
          exact fromMember first (by rw [normalized]; exact List.mem_singleton_self _) (by simpa only [makeUnion, normalized, run] using positive)
      | cons second tail =>
          let members := first :: second :: tail
          have memberAvailable : Values state members := by simpa only [normalized] using retained
          cases ordinary : ordinaryEdges members with
          | some rows =>
              have rowsResident := InternedEdgeResidency.ordinaryEdges_resident members rows state facts.linked
                (fun value member => (memberAvailable value member).resident) ordinary
              have structural := makeNode_positive state facts rows rowsResident
                (entry := ⟨0, .node []⟩) (depth := 0) (free := [])
                (by simpa only [makeUnion, normalized, ordinary, members] using positive)
              obtain ⟨input, present, positive⟩ := rows_positive members rows (ordinary_edges_rows members rows ordinary) structural
              exact fromMember input (by simpa only [normalized] using present) positive
          | none =>
              let key := InternedBinderProtocol.NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let result := (nodeStep key identify state).1
              let after := (nodeStep key identify state).2
              obtain ⟨entry, fields⟩ := InternedGateRank.requested_fields key identify state facts.coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              change InternedRecordCoherence.NodeFields key entry result at fields
              have sourceResult : (run (makeUnion inputs) state).1 = result := by
                simp only [makeUnion, normalized, ordinary, members, run]
                rfl
              have sourceAfter : (run (makeUnion inputs) state).2 = after := by
                simp only [makeUnion, normalized, ordinary, members, run]
                rfl
              have completed := makeUnion_available inputs state facts.coherent facts.cached available
              have resultAvailable : Available after result := by
                simpa only [makeUnion, normalized, ordinary, members, run] using completed.2.2
              have afterCoherent : InternedRecordCoherence.Coherent after := by
                simpa only [makeUnion, normalized, ordinary, members, run] using completed.1
              cases observed : result with
              | empty | reference | node | mu => simp [observed, InternedRecordCoherence.NodeFields, key, muKey] at fields
              | union actual actualMembers depth free =>
                  simp only [observed, InternedRecordCoherence.NodeFields] at fields
                  have sameIds : members.map Value.referenceOf = actualMembers.map Value.referenceOf := by
                    exact InternedBinderProtocol.NodeKey.union.inj fields.2.1
                  have sameMembers : actualMembers = members := InternedNormalizationFree.value_lists_equal after afterCoherent
                    actualMembers members
                    (fun child member => (resultAvailable.children child (by simpa only [observed, children] using member)).resident)
                    (fun child member => by
                      rw [← sourceAfter]
                      exact (available_after_run (makeUnion inputs) state facts.coherent.valid
                        (memberAvailable child member)).resident)
                    sameIds.symm
                  have positiveResult : PositiveAt (.union actual actualMembers depth free) path := by
                    simpa only [sourceResult, observed] using positive
                  cases positiveResult with
                  | member memberIndex child selected rest =>
                      have present : child ∈ members := sameMembers ▸ List.mem_of_getElem? selected
                      exact fromMember child (by simpa only [normalized] using present) rest

end Constructors
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem paired_map_certified (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : Heap → Request → Prop) (post : Heap → Request → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ request value, post before request value → post after request value)
    (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Certified RequestContract clear (call request) before (fun after output => post after request output))
    (before : Heap) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Certified RequestContract clear (map call requests) before
      (fun after values => All₂ (post after) requests values) := by
  induction requests generalizing before with
  | nil => exact .nil
  | cons request requests ih =>
      apply bind_certified RequestContract clear _ _ before (fun state output => post state request output) _
        (checked request List.mem_cons_self before semantic costs (inputs request List.mem_cons_self))
      intro value middle effect valid
      apply bind_certified RequestContract clear _ _ middle _ _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready
      exact .cons (postGrows middle after later request value valid) ready

private theorem request_certified (clear : Guard → Bool) (value : Node) (before : Heap)
    (available : Available before value) (closed : value.free = []) :
    Certified RequestContract clear (.request value) before (ValuePost [value]) := by
  refine ⟨available, ?_⟩
  intro result after _ returned
  exact ⟨⟨returned.1.1, returned.1.2 closed⟩,
    fun path positive => ⟨value, List.mem_cons_self, returned.2 path positive⟩⟩

private theorem retained_certified (clear : Guard → Bool) (inputs : List Node) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs)
    (closed : ClosedValues inputs) :
    Certified RequestContract clear (retainedColumn inputs) before (ValuePost inputs) := by
  have branches (values : List Node) (available : Values before values) (closed : ClosedValues values) :
      Certified RequestContract clear
        (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
          else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) before (ValuePost values) := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeUnion_noNewMu values before)⟩, checked.2,
        fun path positive => makeUnion_positive before semantic.ready.semantic.1.normal.facts values available positive⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      apply bind_certified RequestContract clear _ _ before (ValuePost values) _
      · exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
          (InternedShallowHeap.makeNode_noNewMu _ before)⟩, ⟨checked.2.1, checked.2.2.1⟩,
          fun path positive => ordinaryUnion_positive before semantic.ready.semantic.1.normal.facts values available positive⟩
      · intro value middle _ ready
        refine ⟨ready.1.1, ?_⟩
        intro result after _ returned
        exact ⟨⟨returned.1.1, returned.1.2 ready.1.2⟩,
          fun path positive => ready.2 path (returned.2 path positive)⟩
  cases inputs with
  | nil => exact branches [] available closed
  | cons first rest =>
      cases rest with
      | nil => exact ⟨⟨available first List.mem_cons_self, closed first List.mem_cons_self⟩,
          fun _ positive => ⟨first, List.mem_cons_self, positive⟩⟩
      | cons second rest => exact branches _ available closed

private theorem column_certified (clear : Guard → Bool) (inputs : List Node) (before : Heap)
    (semantic : SemanticReady before) (_costs : CostHeap before) (available : Values before inputs)
    (closed : ClosedValues inputs) :
    Certified RequestContract clear (column inputs) before (ValuePost inputs) := by
  apply bind_certified RequestContract clear _ _ before
    (fun heap values => Values heap values ∧ ClosedValues values ∧ ∀ value ∈ values, value ∈ inputs) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done _
    have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
      (fun _ _ _ => rfl) inputs before semantic available closed values after done
    exact ⟨checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  · intro values middle effect ready
    exact (retained_certified clear values middle effect.semantic effect.costs ready.1 ready.2.1).mono (by
      intro after result returned
      refine ⟨returned.1, ?_⟩
      intro path positive
      obtain ⟨value, member, original⟩ := returned.2 path positive
      exact ⟨value, ready.2.2 value member, original⟩)

private theorem small_certified (clear : Guard → Bool) (edge : Row) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : EdgeResident before edge)
    (closed : ClosedValues edge.children) :
    Certified RequestContract clear (small edge) before (EdgePost [edge]) := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  apply bind_certified RequestContract clear _ _ before
    (fun state values => All₂ (fun input result => ValuePost [input] state result) edge.children values) _
    (paired_map_certified clear Code.request (fun state value => Available state value ∧ value.free = [])
      (fun state input result => ValuePost [input] state result)
      (fun _ _ effect value ready => ⟨effect.keeps.available value ready.1, ready.2⟩)
      (fun _ _ effect _ _ post => value_post_grows effect post) edge.children
      (fun value _ state _ _ ready => request_certified clear value state ready.1 ready.2)
      before semantic costs (fun value member => ⟨available value member, closed value member⟩))
  intro values middle effect ready
  have valuesAvailable : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.1.1))
  have valuesClosed : ClosedValues values := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.1.2))
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear edge.entry.key.symbol edge.entry.key.constraint values
    middle effect.semantic effect.costs valuesAvailable valuesClosed
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle effect.semantic.ready.semantic.1.normal.facts
    edge.entry.key.symbol edge.entry.key.constraint values valuesAvailable
  refine ⟨checked.1, checked.2, ?_, ?_⟩
  · intro positive
    exact ⟨edge, List.mem_cons_self, by simpa only [fields.2.1] using positive⟩
  · intro index child chosen path positive
    rw [fields.2.2] at chosen
    obtain ⟨original, sourceChosen, post⟩ := SourceEqualityProjectionLanguage.all₂_selected ready index child chosen
    obtain ⟨_, singleton, sourcePositive⟩ := post.2 path positive
    exact ⟨edge, List.mem_cons_self, original, sourceChosen, by simpa only [List.mem_singleton.mp singleton] using sourcePositive⟩

private theorem large_certified (clear : Guard → Bool) (top : Guard) (topPlain : SourceMemoGate.plain top = true)
    (first : Row) (rest : List Row) (before : Heap) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (first :: rest)) (closed : ClosedEdges (first :: rest)) :
    Certified RequestContract clear (large top first rest) before (EdgePost (first :: rest)) := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List Node) (member : column ∈ columns) (value : Node) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  apply bind_certified RequestContract clear _ _ before
    (fun state values => All₂ (fun inputs result => ValuePost inputs state result) columns values) _
    (paired_map_certified clear column (fun state inputs => Values state inputs ∧ ClosedValues inputs)
      (fun state inputs result => ValuePost inputs state result)
      (fun _ _ effect _ ready => ⟨(fun value member => effect.keeps.available value (ready.1 value member)), ready.2⟩)
      (fun _ _ effect _ _ post => value_post_grows effect post) columns
      (fun values _ state semantic costs ready => column_certified clear values state semantic costs ready.1 ready.2)
      before semantic costs (fun column member => ⟨(by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact closed edge outer value inner)⟩))
  intro values middle effect ready
  have valuesAvailable : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.1.1))
  have valuesClosed : ClosedValues values := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.1.2))
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear first.entry.key.symbol top values
    middle effect.semantic effect.costs valuesAvailable valuesClosed
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle effect.semantic.ready.semantic.1.normal.facts
    first.entry.key.symbol top values valuesAvailable
  refine ⟨checked.1, checked.2, ?_, ?_⟩
  · intro positive
    rw [fields.2.1, topPlain] at positive
    cases positive
  · intro index child chosen path positive
    rw [fields.2.2] at chosen
    obtain ⟨column, selected, post⟩ := SourceEqualityProjectionLanguage.all₂_selected ready index child chosen
    obtain ⟨value, member, sourcePositive⟩ := post.2 path positive
    obtain ⟨row, included, sourceChosen⟩ := columns_indexed ((first :: rest).map EdgeValue.children)
      first.children.length index column selected value member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp included
    exact ⟨edge, present, value, sourceChosen, sourcePositive⟩

private theorem group_certified (clear : Guard → Bool) (top : Guard) (topPlain : SourceMemoGate.plain top = true)
    (edges : List Row) (before : Heap) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    Certified RequestContract clear (group top edges) before (RowsPost edges) := by
  unfold group
  split
  · have checked := paired_map_certified clear small
      (fun state edge => EdgeResident state edge ∧ ClosedValues edge.children)
      (fun state edge result => EdgePost [edge] state result)
      (fun _ _ effect edge ready => ⟨InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge ready.1, ready.2⟩)
      (fun _ _ effect _ _ post => edge_post_grows effect post) edges
      (fun edge _ state semantic costs ready => small_certified clear edge state semantic costs ready.1 ready.2)
      before semantic costs (fun edge member => ⟨resident edge member, closed edge member⟩)
    exact checked.mono (by
      intro state results ready row member
      obtain ⟨source, present, post⟩ := paired_output ready row member
      refine ⟨post.1, ?_, ?_⟩
      · intro positive
        obtain ⟨original, singleton, sourcePositive⟩ := post.2.1 positive
        exact ⟨source, present, by simpa only [List.mem_singleton.mp singleton] using sourcePositive⟩
      · intro index child chosen path positive
        obtain ⟨original, singleton, originalChild, found, sourcePositive⟩ := post.2.2 index child chosen path positive
        exact ⟨source, present, originalChild, by simpa only [List.mem_singleton.mp singleton] using found, sourcePositive⟩)
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply bind_certified RequestContract clear _ _ before (EdgePost (first :: rest)) _
          (large_certified clear top topPlain first rest before semantic costs resident closed)
        intro result _ _ ready row member
        exact (List.mem_singleton.mp member) ▸ ready

private theorem root_certified (clear : Guard → Bool) (top : Guard) (topPlain : SourceMemoGate.plain top = true)
    (entry : Interned NodeKey) (edges : List Row) (depth : Nat) (free : List Reference)
    (groups : List (List Row)) (grouping : MergedPhysicalGroupRoot.Grouping edges groups)
    (before : Heap) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    Certified RequestContract clear (root top groups) before
      (fun state result => ValueReady state result ∧ ∀ path, PositiveAt result path →
        PositiveAt (.node entry edges depth free) path) := by
  have original (group : List Row) (member : group ∈ groups) (edge : Row) (included : edge ∈ group) : edge ∈ edges :=
    grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  apply bind_certified RequestContract clear _ _ before
    (fun state rows => All₂ (fun inputs results => RowsPost inputs state results) groups rows) _
    (paired_map_certified clear (group top) (fun state edges => Edges state edges ∧ ClosedEdges edges)
      (fun state inputs results => RowsPost inputs state results)
      (fun _ _ effect _ ready => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (ready.1 edge member)), ready.2⟩)
      (fun _ _ effect _ _ post row member => edge_post_grows effect (post row member)) groups
      (fun edges _ state semantic costs ready => group_certified clear top topPlain edges state semantic costs ready.1 ready.2)
      before semantic costs (fun group member => ⟨(fun edge included => resident edge (original group member edge included)),
        fun edge included => closed edge (original group member edge included)⟩))
  intro rows middle effect ready
  have rowResident : ∀ own ∈ rows, Edges middle own := EnumerationSoundness.all₂_outputs _ _ _
    (ready.imp (fun _ _ post row member => (post row member).1.1))
  have rowClosed : ∀ own ∈ rows, ClosedEdges own := EnumerationSoundness.all₂_outputs _ _ _
    (ready.imp (fun _ _ post row member => (post row member).1.2))
  have flatResident : Edges middle rows.flatten := by
    intro edge member
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    exact rowResident own member edge included
  have flatClosed : ClosedEdges rows.flatten := by
    intro edge member
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    exact rowClosed own member edge included
  have rawOrigin (edge : Row) (member : edge ∈ rows.flatten) : RowPositions edges edge := by
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    obtain ⟨group, groupMember, post⟩ := paired_output ready own member
    have law := (post edge included).2
    refine ⟨?_, ?_⟩
    · intro positive
      obtain ⟨source, present, nonplain⟩ := law.1 positive
      exact ⟨source, original group groupMember source present, nonplain⟩
    · intro index child chosen path positive
      obtain ⟨source, present, originalChild, found, sourcePositive⟩ := law.2 index child chosen path positive
      exact ⟨source, original group groupMember source present, originalChild, found, sourcePositive⟩
  have checked := SourceCurrentMemoMergeEffects.node_certified clear rows.flatten middle effect.semantic effect.costs flatResident flatClosed
  refine ⟨checked.1, checked.2, ?_⟩
  intro path positive
  have raw : PositiveAt (.node entry rows.flatten depth free) path :=
    makeNode_positive middle effect.semantic.ready.semantic.1.normal.facts rows.flatten flatResident positive
  cases raw with
  | root index row selected nonplain =>
      obtain ⟨source, member, positive⟩ := (rawOrigin row (List.mem_of_getElem? selected)).1 nonplain
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
      exact .root index source found positive
  | child rowIndex childIndex row child selected chosen rest =>
      obtain ⟨source, member, originalChild, found, positive⟩ :=
        (rawOrigin row (List.mem_of_getElem? selected)).2 childIndex child chosen _ rest
      obtain ⟨sourceIndex, selectedSource⟩ := List.mem_iff_getElem?.mp member
      exact .child sourceIndex childIndex source originalChild selectedSource found positive

private theorem body_certified (clear : Guard → Bool) (top : Guard) (topPlain : SourceMemoGate.plain top = true)
    (input : Node) (before : Heap) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before input) :
    Certified RequestContract clear (body top input) before (fun after output => RequestContract input before output after) := by
  cases input with
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have facts := semantic.ready.semantic.1.normal.facts
        have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
        have rowsClosed : ClosedEdges edges := fun edge member child inner =>
          MergedOrdinaryHeight.closed_child before facts.coherent entry edges depth free available.resident closed edge member child inner
        exact (root_certified clear top topPlain entry edges depth free (MergedSourceGrouping.groups edges)
          (MergedSourceGrouping.groups_correct edges) before semantic costs resident rowsClosed).mono
          (fun _ _ ready => ⟨⟨ready.1.1, fun _ => ready.1.2⟩, by simpa only [closed] using ready.2⟩)
      · simp only [body, closed, ite_false, Certified]
        exact ⟨⟨available, id⟩, fun _ positive => positive⟩
  | empty | reference | mu | union => exact ⟨⟨available, id⟩, fun _ positive => positive⟩

/-- Actual instructions preserve the table law and discharge each actual request certificate. -/
theorem run (clear : Guard → Bool) (top : Guard) (topPlain : SourceMemoGate.plain top = true)
    {code : Code Symbol Guard Output} {before after : Heap}
    {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : Heap → Output → Prop), SemanticReady before → CostHeap before →
      Stored before memo → Support memo →
      Certified (fun input previous result current =>
        SourceCurrentMemoMergeEffects.Contract input previous result current ∧
          ∀ path, PositiveAt result path → PositiveAt input path) clear code before post →
      Effect before after ∧ Stored after saved ∧ Support saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → Stored before memo → Support memo →
          Available before input → Effect before after ∧ Stored after saved ∧ Support saved ∧
            RequestContract input before output after) with
  | pure value state memo =>
      intro post semantic costs stored support checked
      exact ⟨effect_refl _ semantic costs, stored, support, checked⟩
  | work job state memo =>
      intro post semantic costs stored support checked
      exact ⟨checked.1, stored.grows checked.1.keeps, support, checked.2⟩
  | select fuel done =>
      intro post semantic costs stored support checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨effect, stored.grows effect.keeps, support, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs stored support checked
      obtain ⟨effect, retained, finalSupport, returned⟩ := ih semantic costs stored support checked.1
      exact ⟨effect, retained, finalSupport, checked.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored support checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstStored, firstSupport, valid⟩ :=
        ihFirst intermediate semantic costs stored support firstChecked
      obtain ⟨laterEffect, laterStored, laterSupport, returned⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstStored firstSupport
          (nextChecked _ _ firstEffect valid)
      exact ⟨firstEffect.trans laterEffect, laterStored, laterSupport, returned⟩
  | hit found =>
      rename_i semantic costs stored support available
      obtain ⟨same, result, closed⟩ := hit_original semantic available stored found
      have law := support _ _ found
      rw [same] at law
      exact ⟨effect_refl _ semantic costs, stored, support, ⟨result, closed⟩, law⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs stored support available
      obtain ⟨effect, retained, currentSupport, physical, law⟩ :=
        ih _ semantic costs stored support (body_certified clear top topPlain input before semantic costs available)
      have inputAvailable := effect.keeps.available input available
      have completed := stored_remember retained input candidate inputAvailable physical.1 physical.2
      have finalSupport := support_remember currentSupport input candidate law
      obtain ⟨same, winnerAvailable, winnerClosed⟩ :=
        hit_original effect.semantic inputAvailable completed (winner_found current input candidate)
      have winnerSupport := finalSupport _ _ (winner_found current input candidate)
      rw [same] at winnerSupport
      exact ⟨effect, completed, finalSupport, ⟨winnerAvailable, winnerClosed⟩, winnerSupport⟩

/-- Every literal call retains positive child paths and physical table effects. -/
theorem call (clear : Guard → Bool) (top : Guard) (topPlain : SourceMemoGate.plain top = true)
    {input output : Node} {before after : Heap} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (support : Support memo) (available : Available before input) :
    Effect before after ∧ Stored after saved ∧ Support saved ∧
      SourceCurrentMemoMergeEffects.Contract input before output after ∧
        ∀ path, PositiveAt output path → PositiveAt input path :=
  run clear top topPlain (.request actual) (fun after output => RequestContract input before output after)
    semantic costs stored support ⟨available, fun _ _ _ returned => returned⟩

/-- The fuelled worker derives the same law from its actual completed call. -/
theorem worker (clear : Guard → Bool) (top : Guard) (topPlain : SourceMemoGate.plain top = true)
    {fuel selectionFuel input before memo output after saved}
    (actual : SourceCurrentMemoMergeWorker.call clear top fuel selectionFuel input before memo = .done output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (support : Support memo) (available : Available before input) :
    Effect before after ∧ Stored after saved ∧ Support saved ∧
      SourceCurrentMemoMergeEffects.Contract input before output after ∧
        ∀ path, PositiveAt output path → PositiveAt input path :=
  call clear top topPlain (SourceCurrentMemoMergeWorkerProofs.call_sound actual)
    semantic costs stored support available

/-- The actual allocated worker retains the same positions at its exact returned heap. -/
theorem allocated (clear : Guard → Bool)
    {fuel selectionFuel input before memo output after saved}
    (actual : SourceCurrentAllocatedMergeWorker.call clear fuel selectionFuel input before memo = .done output after saved)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap) (stored : Stored before.heap memo)
    (support : Support memo) (available : Available before.heap input) :
    Effect before.heap after.heap ∧ Stored after.heap saved ∧ Support saved ∧
      SourceCurrentMemoMergeEffects.Contract input before.heap output after.heap ∧
        ∀ path, PositiveAt output path → PositiveAt input path :=
  call clear SourceEqualityConstraintConstructors.top rfl
    (SourceCurrentAllocatedMergeGraph.Call.graph (SourceCurrentAllocatedMergeWorkerSound.call_sound actual))
    semantic costs stored support available

end MicroCFTA.SourceCurrentMergePositivePosition

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 16384
set_option maxHeartbeats 0

#check @MicroCFTA.SourceCurrentMergePositivePosition.Support
#print MicroCFTA.SourceCurrentMergePositivePosition.Support
#print axioms MicroCFTA.SourceCurrentMergePositivePosition.Support

#check @MicroCFTA.SourceCurrentMergePositivePosition.support_empty
#print MicroCFTA.SourceCurrentMergePositivePosition.support_empty
#print axioms MicroCFTA.SourceCurrentMergePositivePosition.support_empty

#check @MicroCFTA.SourceCurrentMergePositivePosition.run
#print MicroCFTA.SourceCurrentMergePositivePosition.run
#print axioms MicroCFTA.SourceCurrentMergePositivePosition.run

#check @MicroCFTA.SourceCurrentMergePositivePosition.call
#print MicroCFTA.SourceCurrentMergePositivePosition.call
#print axioms MicroCFTA.SourceCurrentMergePositivePosition.call

#check @MicroCFTA.SourceCurrentMergePositivePosition.worker
#print MicroCFTA.SourceCurrentMergePositivePosition.worker
#print axioms MicroCFTA.SourceCurrentMergePositivePosition.worker

#check @MicroCFTA.SourceCurrentMergePositivePosition.allocated
#print MicroCFTA.SourceCurrentMergePositivePosition.allocated
#print axioms MicroCFTA.SourceCurrentMergePositivePosition.allocated
