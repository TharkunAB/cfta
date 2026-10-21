import MicroCFTA.SourceCurrentConstrainedCapCheckedJointTrace
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointClosed
import MicroCFTA.SourceCurrentNativeMaybeMuPositivePositions
import MicroCFTA.SourceCurrentNativePublicationTrace

/-! # Positive child positions in actual native requests -/
namespace MicroCFTA.SourceCurrentNativeRequestPositivePositions
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open InternedNestedProvenance (Values Edges)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceEqualityNativeDemand
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs EdgeInputs)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointCode (NodeLaw EdgeLaw)
open SourceCurrentAllocatedRecursivePrefixState (Current)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentRequiredPositivePosition (PositiveAt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Physical" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "Old" => SourceCurrentConstrainedCapCheckedJointControl.Certified Plain
local notation "OldStore" => SourceCurrentConstrainedCapCheckedJointCache.Stored Plain
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
private abbrev Causal [DecidableEq (EdgeKey Symbol Guard)] (state : Machine Symbol Guard) :=
  Nonempty (SourceCurrentNativeMuPublication.History empty state.heap)
private abbrev Back (left right result : Node) :=
  ∀ path, PositiveAt result path → PositiveAt left path ∨ PositiveAt right path
private abbrev RowBack (left right result : Row) :=
  (SourceMemoGate.plain result.entry.key.constraint = false →
    SourceMemoGate.plain left.entry.key.constraint = false ∨ SourceMemoGate.plain right.entry.key.constraint = false) ∧
  ∀ (index : Nat) (child : Node), result.children[index]? = some child → ∀ path, PositiveAt child path →
    (∃ original, left.children[index]? = some original ∧ PositiveAt original path) ∨
    (∃ original, right.children[index]? = some original ∧ PositiveAt original path)
private def NodePos (source : Heap) (request : NodeRequest Symbol Guard) (result : Node) :=
  ∀ depth, OriginalBindings Plain source request.domain.key → NodeInputs source request →
    Cap Plain depth request.left → Cap Plain depth request.right → Back request.left request.right result
private def EdgePos (source : Heap) (request : EdgeRequest Symbol Guard) (result : Row) :=
  ∀ depth, OriginalBindings Plain source request.domain.key → EdgeInputs source request →
    Edge Plain depth request.left → Edge Plain depth request.right → RowBack request.left request.right result
/-- Returned native cells retain same-position support for their full captured requests. -/
def Support (source : Heap) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  FlatMemoThunk.Valid (fun _ _ => True) (FlatMemoThunk.CellSpec (fun request result =>
    ∀ depth, OriginalBindings Plain source request.domain.key → NodeInputs source request →
      Cap Plain depth request.left → Cap Plain depth request.right → ∀ path, PositiveAt result path →
      PositiveAt request.left path ∨ PositiveAt request.right path)) state.nodes ∧
  FlatMemoThunk.Valid (fun _ _ => True) (FlatMemoThunk.CellSpec (fun request result =>
    ∀ depth, OriginalBindings Plain source request.domain.key → EdgeInputs source request →
      Edge Plain depth request.left → Edge Plain depth request.right →
      (SourceMemoGate.plain result.entry.key.constraint = false →
        SourceMemoGate.plain request.left.entry.key.constraint = false ∨ SourceMemoGate.plain request.right.entry.key.constraint = false) ∧
      ∀ (index : Nat) (child : Node), result.children[index]? = some child → ∀ path, PositiveAt child path →
        (∃ original, request.left.children[index]? = some original ∧ PositiveAt original path) ∨
        (∃ original, request.right.children[index]? = some original ∧ PositiveAt original path))) state.edges

private structure Stored (source : Heap) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop where
  nodes : FlatMemoThunk.Valid (fun _ _ => True) (FlatMemoThunk.CellSpec (NodePos source)) state.nodes
  edges : FlatMemoThunk.Valid (fun _ _ => True) (FlatMemoThunk.CellSpec (EdgePos source)) state.edges

private theorem makeNode_positive [DecidableEq (EdgeKey Symbol Guard)] (state : Heap) (facts : Facts state) (rows : List Row)
    (resident : Edges state rows) {entry depth free path}
    (positive : PositiveAt (InternedConstructorTemplates.run (makeNode rows) state).1 path) :
    PositiveAt (.node entry rows depth free) path := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows state facts resident
  have fields := EqualityLeafProjectionPhysical.makeNode_edges rows state facts.coherent facts.linked resident
  have raw : ∀ row ∈ nodeEdges (InternedConstructorTemplates.run (makeNode rows) state).1, row ∈ rows := by
    intro row member
    exact (List.mem_filter.mp (canonicalEdges_member _ row (fields ▸ member))).1
  generalize computed : (InternedConstructorTemplates.run (makeNode rows) state).1 = result at positive ordinary raw
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

private theorem makeUnion_positive [DecidableEq (EdgeKey Symbol Guard)] (state : Heap) (facts : Facts state) (inputs : List Node)
    (available : Values state inputs) {path}
    (positive : PositiveAt (InternedConstructorTemplates.run (makeUnion inputs) state).1 path) :
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
  | nil => simp only [makeUnion, normalized, InternedConstructorTemplates.run] at positive; cases positive
  | cons first rest =>
      cases rest with
      | nil =>
          exact fromMember first (by rw [normalized]; exact List.mem_singleton_self _) (by simpa only [makeUnion, normalized, InternedConstructorTemplates.run] using positive)
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
              have sourceResult : (InternedConstructorTemplates.run (makeUnion inputs) state).1 = result := by
                simp only [makeUnion, normalized, ordinary, members, InternedConstructorTemplates.run]
                rfl
              have sourceAfter : (InternedConstructorTemplates.run (makeUnion inputs) state).2 = after := by
                simp only [makeUnion, normalized, ordinary, members, InternedConstructorTemplates.run]
                rfl
              have completed := makeUnion_available inputs state facts.coherent facts.cached available
              have resultAvailable : Available after result := by
                simpa only [makeUnion, normalized, ordinary, members, InternedConstructorTemplates.run] using completed.2.2
              have afterCoherent : InternedRecordCoherence.Coherent after := by
                simpa only [makeUnion, normalized, ordinary, members, InternedConstructorTemplates.run] using completed.1
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


private theorem paired_output {A B : Type} {inputs : List A} {outputs : List B} {relation : A → B → Prop}
    (related : All₂ relation inputs outputs) (output : B) (member : output ∈ outputs) :
    ∃ input ∈ inputs, relation input output := by
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨input, found, law⟩ := SourceEqualityProjectionLanguage.all₂_selected related index output selected
  exact ⟨input, List.mem_of_getElem? found, law⟩
private theorem body_back (value : Node) (bounded : Cap Plain depth value) :
    ∀ path, PositiveAt (SourceRecursiveIntersectionKernel.body value) path → PositiveAt value path := by
  cases value with
  | mu entry stored level ordinary =>
      intro path positive
      exact False.elim (SourceCurrentRequiredPositivePosition.not_plain positive
        (SourceCurrentHereditaryNativeScope.body_annotated Plain _ (SourceCurrentConstrainedCapNativeScope.mu_annotated bounded)))
  | empty | reference | node | union => exact fun _ positive => positive
section Certificates
variable {source : Heap} [DecidableEq (EdgeKey Symbol Guard)]
private def CodePos (code : Code Symbol Guard A) (state : Machine Symbol Guard)
    (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next => ∀ value after, work job state = .done value after →
      Extension state after → Context Plain source after → Causal after → CodePos (next value) after post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      Extension state after → Context Plain source after → Causal after → CodePos (next actual.1) after post
  | .read name next => CodePos (next (SourcePreparedSharedRows.read state.heap name)) state post
  | .optionalBinder pair operand next => ∀ value after,
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair operand state.heap) state = .done value after →
      Extension state after → Context Plain source after → Causal after → CodePos (next value) after post
  | .node request next => ∀ value after, Extension state after → Context Plain source after → Causal after →
      Available after.heap value → NodeLaw Plain source request value → NodePos source request value → CodePos (next value) after post
  | .edge request next => ∀ value after, Extension state after → Context Plain source after → Causal after →
      EdgeResident after.heap value → EdgeLaw Plain source request value → EdgePos source request value → CodePos (next value) after post
  | .finishNode .. | .finishEdge .. => False
private def ControlPos (control : Control A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) :=
  match control with
  | .code code => CodePos (source := source) code state post
  | .edgeBody request next => ∀ value after, Extension state after → Context Plain source after → Causal after →
      EdgeResident after.heap value → EdgeLaw Plain source request value → EdgePos source request value → CodePos (source := source) (next value) after post
private theorem pos_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state)
    (middle : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : CodePos (source := source) code state middle)
    (continuation : ∀ value after, Extension state after → Context Plain source after → Causal after →
      middle after value → CodePos (source := source) (next value) after post) : CodePos (source := source) (code.bind next) state post := by
  induction code generalizing state with
  | pure value => exact continuation value state (.refl _) context causal certificate
  | fail => trivial
  | work job resume ih | optionalBinder pair operand resume ih =>
      intro value after done growth afterContext afterCausal
      exact ih value after afterContext afterCausal (certificate value after done growth afterContext afterCausal)
        (fun result final later finalContext finalCausal known => continuation result final (growth.trans later) finalContext finalCausal known)
  | enter domain left right first second resume ih =>
      intro growth afterContext afterCausal
      exact ih _ _ afterContext afterCausal (certificate growth afterContext afterCausal)
        (fun result final later finalContext finalCausal known => continuation result final (growth.trans later) finalContext finalCausal known)
  | read name resume ih => exact ih _ state context causal certificate continuation
  | node request resume ih | edge request resume ih =>
      intro value after growth afterContext afterCausal physical old law
      exact ih value after afterContext afterCausal (certificate value after growth afterContext afterCausal physical old law)
        (fun result final later finalContext finalCausal known => continuation result final (growth.trans later) finalContext finalCausal known)
  | finishNode | finishEdge => cases certificate
private theorem pos_forall {I : Sort u} (code : Code Symbol Guard A) (state : Machine Symbol Guard)
    (post : I → Machine Symbol Guard → A → Prop) (clean : BodyCode code)
    (known : ∀ i, CodePos (source := source) code state (post i)) : CodePos (source := source) code state (fun after value => ∀ i, post i after value) := by
  induction code generalizing state with
  | pure => exact known
  | fail => trivial
  | work job resume ih | optionalBinder pair operand resume ih =>
      intro value after done growth context causal
      exact ih value after (clean value) (fun i => known i value after done growth context causal)
  | enter domain left right first second resume ih =>
      intro growth context causal
      exact ih _ _ (clean _) (fun i => known i growth context causal)
  | read name resume ih => exact ih _ state (clean _) known
  | node request resume ih | edge request resume ih =>
      intro value after growth context causal physical old law
      exact ih value after (clean value) (fun i => known i value after growth context causal physical old law)
  | finishNode | finishEdge => cases clean
private theorem pos_mono (code : Code Symbol Guard A) (state : Machine Symbol Guard)
    (first second : Machine Symbol Guard → A → Prop) (known : CodePos (source := source) code state first)
    (implies : ∀ after value, first after value → second after value) : CodePos (source := source) code state second := by
  induction code generalizing state with
  | pure value => exact implies state value known
  | fail => trivial
  | work job resume ih | optionalBinder pair operand resume ih =>
      intro value after done growth context causal
      exact ih value after (known value after done growth context causal)
  | enter domain left right first second resume ih =>
      intro growth context causal
      exact ih _ _ (known growth context causal)
  | read name resume ih => exact ih _ state known
  | node request resume ih | edge request resume ih =>
      intro value after growth context causal physical old law
      exact ih value after (known value after growth context causal physical old law)
  | finishNode | finishEdge => cases known
private theorem pos_walk (call : A → Code Symbol Guard B) (requests : List A)
    (relation : Machine Symbol Guard → A → B → Prop)
    (stable : ∀ before after, Extension before after → ∀ request result, relation before request result → relation after request result)
    (calls : ∀ request ∈ requests, ∀ state, Context Plain source state → Causal state →
      CodePos (source := source) (call request) state (fun after value => relation after request value))
    (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state) :
    CodePos (source := source) (walk call requests) state (fun after values => All₂ (relation after) requests values) := by
  induction requests generalizing state with
  | nil => exact .nil
  | cons first rest ih =>
      apply pos_bind _ _ state context causal _ _ (calls first List.mem_cons_self state context causal)
      intro result middle _ middleContext middleCausal law
      apply pos_bind _ _ middle middleContext middleCausal _ _
        (ih (fun request member => calls request (List.mem_cons_of_mem _ member)) middle middleContext middleCausal)
      intro results after growth _ _ laws
      exact .cons (stable middle after growth first result law) laws
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private theorem edge_work_pos (request : EdgeRequest Symbol Guard) (guard : Guard)
    (values : List Node) (state : Machine Symbol Guard) (context : Context Plain source state)
    (guardBack : SourceMemoGate.plain guard = false →
      SourceMemoGate.plain request.left.entry.key.constraint = false ∨
        SourceMemoGate.plain request.right.entry.key.constraint = false)
    (related : All₂ (fun pair value => Available state.heap value ∧ Back pair.1 pair.2 value)
      (request.left.children.zip request.right.children) values) :
    CodePos (source := source) (.work (makeEdge request.left.entry.key.symbol guard values) .pure) state
      (fun _ result => RowBack request.left request.right result) := by
  intro result after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state result after done
  have available : Values state.heap values := by
    intro value member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨pair, _, physical, _⟩ := SourceEqualityProjectionLanguage.all₂_selected related index value found
    exact physical
  have fields := MergedPhysicalGroupEdges.makeEdge_fields state.heap context.valid.1
    request.left.entry.key.symbol guard values available
  constructor
  · intro positive
    exact guardBack (fields.2.1 ▸ positive)
  · intro index child chosen path positive
    rw [fields.2.2] at chosen
    obtain ⟨pair, selected, _, law⟩ := SourceEqualityProjectionLanguage.all₂_selected related index child chosen
    have originals := List.getElem?_zip_eq_some.mp selected
    exact (law path positive).imp (fun back => ⟨pair.1, originals.1, back⟩)
      (fun back => ⟨pair.2, originals.2, back⟩)

private theorem children_fixed_pos (depth : Nat) (request : EdgeRequest Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state)
    (bindings : OriginalBindings Plain source request.domain.key) (inputs : EdgeInputs source request)
    (left : Edge Plain depth request.left) (right : Edge Plain depth request.right)
    (guardBack : SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback combined) = false →
      SourceMemoGate.plain request.left.entry.key.constraint = false ∨
        SourceMemoGate.plain request.right.entry.key.constraint = false) :
    CodePos (source := source) (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun _ result => RowBack request.left request.right result) := by
  let relation := fun (after : Machine Symbol Guard) (pair : Node × Node) (value : Node) =>
    Available after.heap value ∧ Back pair.1 pair.2 value
  have walked := pos_walk
    (fun pair : Node × Node => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) relation
    (by intro before after growth pair result known; exact ⟨growth.available result known.1, known.2⟩)
    (by
      intro pair member current _ _ result after _ _ _ physical _ law
      have inside := List.of_mem_zip member
      have first := inputs.1 pair.1 inside.1
      have second := inputs.2 pair.2 inside.2
      have capped := SourceCurrentConstrainedCapNativeScope.edge_child Plain depth request.left request.right
        left right pair member
      exact ⟨physical, law (depth - 1) bindings
        ⟨first.1, second.1, first.2.1, second.2.1, first.2.2, second.2.2⟩ capped.1 capped.2⟩)
    state context causal
  unfold SourceEqualityNativeCheckedCode.children
  apply pos_bind _ _ state context causal _ _ walked
  intro values middle _ middleContext _ related
  exact edge_work_pos request _ values middle middleContext guardBack related

private theorem sentinel_pos (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (context : Context Plain source state) :
    CodePos (source := source) (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ result => EdgePos source request result) := by
  intro result after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state result after done
  have available : Values state.heap ([.empty] : List Node) := by
    intro value member
    cases List.mem_singleton.mp member
    exact empty_available _
  have fields := MergedPhysicalGroupEdges.makeEdge_fields state.heap context.valid.1
    request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty] available
  intro _ _ _ _ _
  constructor
  · intro positive
    rw [fields.2.1] at positive
    cases positive
  · intro index child chosen path positive
    rw [fields.2.2] at chosen
    cases List.mem_singleton.mp (List.mem_of_getElem? chosen)
    cases positive

private theorem edge_body_fixed_pos (depth : Nat) (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (code : Code Symbol Guard Row)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (context : Context Plain source before.native.machine) (causal : Causal before.native.machine)
    (ready : EdgeReady before.native.machine request)
    (bindings : OriginalBindings Plain source request.domain.key) (inputs : EdgeInputs source request)
    (left : Edge Plain depth request.left) (right : Edge Plain depth request.right)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    CodePos (source := source) code after.native.machine (fun _ result => RowBack request.left request.right result) := by
  have same := (SourceCurrentConstrainedCapCheckedJointEdge.body_effects request before after code good ready yielded).1
  rw [same]
  by_cases arity : request.left.children.length = request.right.children.length
  · have matched : ¬ request.left.children.length ≠ request.right.children.length := by omega
    simp only [SourceEqualityNativeDemand.body, ite_eq_right matched] at yielded
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at yielded; cases yielded
    | ok first =>
      cases first with
      | none => simp only [firstLoaded] at yielded; cases yielded
      | some first =>
        simp only [firstLoaded] at yielded
        cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
        | error message => simp only [secondLoaded] at yielded; cases yielded
        | ok second =>
          cases second with
          | none => simp only [secondLoaded] at yielded; cases yielded
          | some second =>
            simp only [secondLoaded] at yielded
            have firstCached := (good.fields _ _ ready.2.1).1
            have secondCached := (good.fields _ _ ready.2.2).1
            have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
              firstCached first firstLoaded).1
            have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
              secondCached second secondLoaded).1
            obtain ⟨branch, done, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct
              GuardStructuralOrder.le first second request.left.children.length request.right.children.length
              before.operations good.operations firstReady secondReady
            cases branch with
            | mismatch | rejected =>
              simp only [done, SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
              cases yielded
              exact pos_mono _ _ _ _ (sentinel_pos request _ context)
                (fun _ result known => known depth bindings inputs left right)
            | ready combined =>
              have guardBack : SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback combined) = false →
                  SourceMemoGate.plain request.left.entry.key.constraint = false ∨
                    SourceMemoGate.plain request.right.entry.key.constraint = false := by
                intro positive
                cases firstPlain : SourceMemoGate.plain request.left.entry.key.constraint with
                | false => exact .inl rfl
                | true =>
                  cases secondPlain : SourceMemoGate.plain request.right.entry.key.constraint with
                  | false => exact .inr rfl
                  | true =>
                    have combinedPlain := SourceCurrentUnconstrainedGuardClosure.loaded_ready_plain
                      GuardStructuralOrder.le request.left.entry.key.constraint request.right.entry.key.constraint
                      first second request.left.children.length request.right.children.length before.operations good.operations
                      firstCached secondCached firstLoaded secondLoaded firstPlain secondPlain combined done
                    rw [positive] at combinedPlain
                    cases combinedPlain
              simp only [done, SourceEqualityNativeDemand.code_bind_pure] at yielded
              cases yielded
              exact children_fixed_pos depth request combined _ context causal bindings inputs left right guardBack
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, SourceEqualityNativeDemand.sentinel,
      SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact pos_mono _ _ _ _ (sentinel_pos request _ context)
      (fun _ result known => known depth bindings inputs left right)

private theorem edge_body_pos (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (code : Code Symbol Guard Row)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (context : Context Plain source before.native.machine) (causal : Causal before.native.machine)
    (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    CodePos (source := source) code after.native.machine (fun _ result => EdgePos source request result) := by
  have clean : BodyCode code := SourceEqualityNativeDemandBodyCode.body_clean request .pure before after (.code code)
    yielded (fun _ => trivial)
  let Spec := {depth : Nat // OriginalBindings Plain source request.domain.key ∧ EdgeInputs source request ∧
    Edge Plain depth request.left ∧ Edge Plain depth request.right}
  have all : CodePos (source := source) code after.native.machine (fun _ result => ∀ spec : Spec, RowBack request.left request.right result) := by
    apply pos_forall code after.native.machine _ clean
    intro spec
    exact edge_body_fixed_pos spec.val request before after code good context causal ready spec.property.1
      spec.property.2.1 spec.property.2.2.1 spec.property.2.2.2 yielded
  apply pos_mono code after.native.machine _ _ all
  intro final result returned depth bindings inputs left right
  exact returned ⟨depth, bindings, inputs, left, right⟩

private theorem request_pos (depth : Nat) (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : OriginalBindings Plain source request.domain.key) (inputs : NodeInputs source request)
    (left : Cap Plain depth request.left) (right : Cap Plain depth request.right) :
    CodePos (source := source) (requestNode request.domain request.left request.right) state
      (fun after result => Available after.heap result ∧ Back request.left request.right result) := by
  intro value after _ _ _ available _ law
  exact ⟨available, law depth bindings inputs left right⟩
private theorem ordinary_pos [DecidableEq Symbol] (depth : Nat) (domain : Interned DomainKey)
    (left right : Node) (facts : Facts source) (bindings : OriginalBindings Plain source domain.key)
    (inputs : NodeInputs source ⟨domain,left,right⟩) (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right)
    (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state) :
    CodePos (source := source) (compileRows domain (nodeEdges left) (nodeEdges right)) state (fun _ result => Back left right result) := by
  have walked := pos_walk (source := source) (fun pair : Row × Row => requestEdge domain pair.1 pair.2)
    (pairs (nodeEdges left) (nodeEdges right))
    (fun current pair row => EdgeResident current.heap row ∧ RowBack pair.1 pair.2 row)
    (by intro before after growth pair row known; exact ⟨edge_grows _ _ growth.heap row known.1,known.2⟩)
    (by
      intro pair member current _ _ result after _ _ _ resident _ law
      have inside := (pairs_member _ _ pair).mp member
      exact ⟨resident,law depth bindings
        (SourceCurrentConstrainedCapOriginalSupport.rows_input source facts domain left right inputs pair.1 pair.2 inside.1 inside.2.1)
        (SourceCurrentConstrainedCap.node_edge leftCap pair.1 inside.1)
        (SourceCurrentConstrainedCap.node_edge rightCap pair.2 inside.2.1)⟩) state context causal
  unfold compileRows
  apply pos_bind _ _ state context causal _ _ walked
  intro rows after _ afterContext _ related result final done _ _ _ path positive
  obtain ⟨rfl,rfl⟩ := work_done _ after result final done
  have resident : Edges after.heap rows := by
    intro row member
    exact (paired_output related row member).choose_spec.2.1
  have raw := makeNode_positive after.heap afterContext.valid.1 rows resident
    (entry := ⟨0,.node []⟩) (depth := 0) (free := []) positive
  cases raw with
  | root index row selected nonplain =>
      obtain ⟨pair,member,_,law⟩ := paired_output related row (List.mem_of_getElem? selected)
      have inside := (pairs_member _ _ pair).mp member
      rcases law.1 nonplain with first | second
      · cases left with
        | empty | reference | union | mu => cases inside.1
        | node entry edges level free => exact .inl (.root _ pair.1 (List.mem_iff_getElem?.mp inside.1).choose_spec first)
      · cases right with
        | empty | reference | union | mu => cases inside.2.1
        | node entry edges level free => exact .inr (.root _ pair.2 (List.mem_iff_getElem?.mp inside.2.1).choose_spec second)
  | child index childIndex row child selected chosen rest =>
      obtain ⟨pair,member,_,law⟩ := paired_output related row (List.mem_of_getElem? selected)
      have inside := (pairs_member _ _ pair).mp member
      rcases law.2 childIndex child chosen _ rest with ⟨original,found,positive⟩ | ⟨original,found,positive⟩
      · cases left with
        | empty | reference | union | mu => cases inside.1
        | node entry edges level free => exact .inl (.child _ childIndex pair.1 original (List.mem_iff_getElem?.mp inside.1).choose_spec found positive)
      · cases right with
        | empty | reference | union | mu => cases inside.2.1
        | node entry edges level free => exact .inr (.child _ childIndex pair.2 original (List.mem_iff_getElem?.mp inside.2.1).choose_spec found positive)
private theorem union_pos (members : List Node) (call : Node → Code Symbol Guard Node) (left right : Node)
    (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state)
    (calls : ∀ member ∈ members, ∀ current, Context Plain source current → Causal current →
      CodePos (source := source) (call member) current (fun after value => Available after.heap value ∧ Back left right value)) :
    CodePos (source := source) ((walk call members).bind fun values => .work (makeUnion values) .pure) state (fun _ value => Back left right value) := by
  apply pos_bind _ _ state context causal _ _
    (pos_walk call members (fun current _ value => Available current.heap value ∧ Back left right value)
      (by intro before after growth _ value known; exact ⟨growth.available _ known.1,known.2⟩) calls state context causal)
  intro values after _ afterContext _ related result final done _ _ _ path positive
  obtain ⟨rfl,rfl⟩ := work_done _ after result final done
  have available : Values after.heap values := by
    intro value member
    exact (paired_output related value member).choose_spec.2.1
  obtain ⟨value,member,positive⟩ := makeUnion_positive after.heap afterContext.valid.1 values available positive
  exact (paired_output related value member).choose_spec.2.2 path positive
private theorem mu_pos (depth : Nat) (domain : Interned DomainKey) (left right : Node)
    (state : Machine Symbol Guard) (context : Context Plain source state)
    (bindings : OriginalBindings Plain source domain.key) (inputs : NodeInputs source ⟨domain,left,right⟩)
    (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right) :
    CodePos (source := source) (compileMu domain left right) state (fun _ result => Back left right result) := by
  cases first : identity left <;> cases second : identity right <;> simp only [compileMu,first,second]
  all_goals try trivial
  rename_i firstId secondId
  let entered := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right firstId secondId
  intro _ enteredContext _
  have enteredBindings := SourceCurrentConstrainedCapOriginalSupport.enter Plain depth source domain bindings left right inputs
    leftCap rightCap state.domains context.valid.2 firstId secondId
  have key := SourceRecursiveIntersectionSchedule.entered_key state.domains context.valid.2 domain.key left right firstId secondId
  have firstBody := SourceCurrentConstrainedCapOriginalSupport.body_input source left inputs.1 inputs.2.2.1
  have secondBody := SourceCurrentConstrainedCapOriginalSupport.body_input source right inputs.2.1 inputs.2.2.2.1
  have bodyInputs : NodeInputs source ⟨entered.1,SourceRecursiveIntersectionKernel.body left,SourceRecursiveIntersectionKernel.body right⟩ := by
    refine ⟨firstBody.1,secondBody.1,firstBody.2,secondBody.2,?_,?_⟩
    · rw [key]; exact SourceCurrentConstrainedCapNativeCoverage.left_body_covered domain.key left right inputs.2.2.2.2.1 _
    · rw [key]; exact SourceCurrentConstrainedCapNativeCoverage.right_body_covered domain.key left right inputs.2.2.2.2.2 _
  have firstCap := SourceCurrentConstrainedCapNativeScope.body_cap Plain depth left leftCap
  have secondCap := SourceCurrentConstrainedCapNativeScope.body_cap Plain depth right rightCap
  intro value middle _ middleContext ⟨history⟩ available old law result after done _ _ _ path positive
  have valueCap := (old depth enteredBindings bodyInputs firstCap secondCap).1
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu (pair firstId secondId) value middle.heap with
  | pending key heap => simp only [construction,actual] at done; cases done
  | done output heap =>
      simp only [construction,actual] at done
      cases done
      have back := SourceCurrentNativeMaybeMuPositivePositions.maybeMu (pair firstId secondId) value middle.heap
        middleContext.semantic available depth valueCap
        (SourceCurrentConstrainedCapGuardNative.stored Plain middle.heap middleContext.guards) history result heap actual path positive
      rcases law depth enteredBindings bodyInputs firstCap secondCap path back with first | second
      · exact .inl (body_back left leftCap path first)
      · exact .inr (body_back right rightCap path second)
private theorem reference_pos (depth : Nat) (domain : Interned DomainKey) (name : Nat) (other : Node) (left : Bool)
    (state : Machine Symbol Guard) (context : Context Plain source state)
    (bindings : OriginalBindings Plain source domain.key)
    (original : SourceRecursiveIntersectionInputView.Original other) (available : Available source other)
    (covered : SourceCurrentConstrainedCapNativeIdentity.Covered domain.key other) (bounded : Cap Plain depth other) :
    CodePos (source := source) (compileReference domain name other left) state
      (fun _ value => ∀ path, PositiveAt value path → PositiveAt other path) := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨bound,found,sourceAvailable,_,reference,annotated,boundCovered,boundOriginal⟩ :=
      SourceCurrentConstrainedCapOriginalSupport.read Plain source state.heap context.valid.1 context.growth context.history domain.key bindings name member
    simp only [compileReference,member,ite_true,CodePos,found]
    cases left
    · intro value after _ _ _ _ _ law path positive
      rcases law depth bindings ⟨original,boundOriginal,available,sourceAvailable,covered,boundCovered⟩ bounded (.plain depth annotated) path positive with first | second
      · exact first
      · exact False.elim (SourceCurrentRequiredPositivePosition.not_plain second annotated)
    · intro value after _ _ _ _ _ law path positive
      rcases law depth bindings ⟨boundOriginal,original,sourceAvailable,available,boundCovered,covered⟩ (.plain depth annotated) bounded path positive with first | second
      · exact False.elim (SourceCurrentRequiredPositivePosition.not_plain first annotated)
      · exact second
  · simp only [compileReference,member,ite_false]; trivial
private theorem node_pos [DecidableEq Symbol] (facts : Facts source) (request : NodeRequest Symbol Guard)
    (depth : Nat) (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state)
    (bindings : OriginalBindings Plain source request.domain.key) (inputs : NodeInputs source request)
    (leftCap : Cap Plain depth request.left) (rightCap : Cap Plain depth request.right) :
    CodePos (source := source) (compileNode request) state (fun _ result => Back request.left request.right result) := by
  rcases request with ⟨domain,left,right⟩
  cases selected : decision domain.key left right with
  | empty => simp only [compileNode,selected]; intro path positive; cases positive
  | reset =>
      simp only [compileNode,selected]
      exact pos_mono _ state _ _ (request_pos depth ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩ state
        (SourceCurrentConstrainedCapOriginalSupport.empty Plain source)
        (SourceCurrentConstrainedCapKernelJointDecision.reset_inputs source domain left right inputs selected) leftCap rightCap)
        (fun _ _ known => known.2)
  | self => simp only [compileNode,selected]; exact fun _ positive => .inl positive
  | swap =>
      simp only [compileNode,selected]
      exact pos_mono _ state _ _ (request_pos depth ⟨domain,right,left⟩ state bindings
        ⟨inputs.2.1,inputs.1,inputs.2.2.2.1,inputs.2.2.1,inputs.2.2.2.2.2,inputs.2.2.2.2.1⟩ rightCap leftCap)
        (fun _ _ known path positive => (known.2 path positive).symm)
  | repeated key => simp only [compileNode,selected]; intro path positive; cases positive
  | bothMu | leftMu | rightMu => simp only [compileNode,selected]; exact mu_pos depth domain left right state context bindings inputs leftCap rightCap
  | leftUnion =>
      simp only [compileNode,selected]
      cases left with
      | empty | reference | node | mu => trivial
      | union entry members level free =>
          apply union_pos members _ _ _ state context causal
          intro member inside current _ _
          have original := SourceCurrentConstrainedCapOriginalSupport.union_member source entry members level free inputs.1 inputs.2.2.1 member inside
          have covered := SourceCurrentConstrainedCapNativeIdentity.Covered.union_member source facts domain.key entry members level free inputs.2.2.1 inputs.2.2.2.2.1 member inside
          exact pos_mono _ current _ _ (request_pos depth ⟨domain,member,right⟩ current bindings
            ⟨original.1,inputs.2.1,original.2,inputs.2.2.2.1,covered,inputs.2.2.2.2.2⟩
            (SourceCurrentConstrainedCap.union_member leftCap member inside) rightCap)
            (fun _ _ known => ⟨known.1,fun path positive => (known.2 path positive).imp
              (fun rest => PositiveAt.member _ member (List.mem_iff_getElem?.mp inside).choose_spec rest) id⟩)
  | rightUnion =>
      simp only [compileNode,selected]
      cases right with
      | empty | reference | node | mu => trivial
      | union entry members level free =>
          apply union_pos members _ _ _ state context causal
          intro member inside current _ _
          have original := SourceCurrentConstrainedCapOriginalSupport.union_member source entry members level free inputs.2.1 inputs.2.2.2.1 member inside
          have covered := SourceCurrentConstrainedCapNativeIdentity.Covered.union_member source facts domain.key entry members level free inputs.2.2.2.1 inputs.2.2.2.2.2 member inside
          exact pos_mono _ current _ _ (request_pos depth ⟨domain,left,member⟩ current bindings
            ⟨inputs.1,original.1,inputs.2.2.1,original.2,inputs.2.2.2.2.1,covered⟩ leftCap
            (SourceCurrentConstrainedCap.union_member rightCap member inside))
            (fun _ _ known => ⟨known.1,fun path positive => (known.2 path positive).imp id
              (fun rest => PositiveAt.member _ member (List.mem_iff_getElem?.mp inside).choose_spec rest)⟩)
  | leftReference =>
      simp only [compileNode,selected]
      cases left with
      | empty | node | union | mu => trivial
      | reference name =>
          cases name <;> try trivial
          rename_i name
          exact pos_mono _ state _ _ (reference_pos depth domain name right true state context bindings inputs.2.1 inputs.2.2.2.1 inputs.2.2.2.2.2 rightCap)
            (fun _ _ known path positive => .inr (known path positive))
  | rightReference =>
      simp only [compileNode,selected]
      cases right with
      | empty | node | union | mu => trivial
      | reference name =>
          cases name <;> try trivial
          rename_i name
          exact pos_mono _ state _ _ (reference_pos depth domain name left false state context bindings inputs.1 inputs.2.2.1 inputs.2.2.2.2.1 leftCap)
            (fun _ _ known path positive => .inl (known path positive))
  | ordinary =>
      simp only [compileNode,selected]
      cases left <;> cases right <;> try trivial
      exact ordinary_pos depth domain _ _ facts bindings inputs leftCap rightCap state context causal
  | unsupported => simp only [compileNode,selected]; trivial
private theorem node_law_pos [DecidableEq Symbol] (facts : Facts source) (request : NodeRequest Symbol Guard)
    (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state) :
    CodePos (source := source) (compileNode request) state (fun _ result => NodePos source request result) := by
  let Spec := {depth : Nat // OriginalBindings Plain source request.domain.key ∧ NodeInputs source request ∧
    Cap Plain depth request.left ∧ Cap Plain depth request.right}
  have all := pos_forall (source := source) (compileNode request) state
    (fun (_ : Spec) _ result => Back request.left request.right result)
    (compileNode_bodyCode request)
    (fun spec => node_pos facts request spec.val state context causal spec.property.1 spec.property.2.1 spec.property.2.2.1 spec.property.2.2.2)
  exact pos_mono _ state _ _ all (fun _ _ known depth bindings inputs left right => known ⟨depth,bindings,inputs,left,right⟩)

end Certificates

variable {source : Heap}
private theorem initial_stored (width : Nat) (machine : Machine Symbol Guard) : Stored source (initial width machine) :=
  ⟨FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩
private theorem lookup_node (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (request : NodeRequest Symbol Guard)
    (stored : Stored source state) : Stored source (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode,key] using stored
  | some keyValue =>
      simp only [lookupNode,key]
      exact ⟨FlatMemoThunk.lookup_valid keyValue request state.nodes _ _ stored.nodes trivial trivial,stored.edges⟩
private theorem lookup_edge (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (stored : Stored source state) : Stored source (lookupEdge width request state).2 :=
  ⟨stored.nodes,FlatMemoThunk.lookup_valid _ request state.edges _ _ stored.edges trivial trivial⟩
private theorem demand_node (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat)
    (stored : Stored source state) : Stored source (demandNode handle state).2 :=
  ⟨FlatMemoThunk.demand_spec handle state.nodes _ _ stored.nodes,stored.edges⟩
private theorem demand_edge (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat)
    (stored : Stored source state) : Stored source (demandEdge handle state).2 :=
  ⟨stored.nodes,FlatMemoThunk.demand_spec handle state.edges _ _ stored.edges⟩
private theorem finish_node (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Node) (stored : Stored source state)
    (running : state.nodes.cells handle = some ⟨request,.evaluating⟩) (law : NodePos source request result) :
    Stored source (finishNode handle result state) := by
  refine ⟨FlatMemoThunk.finish_spec handle result state.nodes _ _ stored.nodes ?_,stored.edges⟩
  intro original found
  have same : request = original := congrArg FlatMemoThunk.Cell.request (Option.some.inj (running.symm.trans found))
  simpa only [same] using law
private theorem finish_edge (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : Row) (stored : Stored source state)
    (running : state.edges.cells handle = some ⟨request,.evaluating⟩) (law : EdgePos source request result) :
    Stored source (finishEdge handle result state) := by
  refine ⟨stored.nodes,FlatMemoThunk.finish_spec handle result state.edges _ _ stored.edges ?_⟩
  intro original found
  have same : request = original := congrArg FlatMemoThunk.Cell.request (Option.some.inj (running.symm.trans found))
  simpa only [same] using law
private theorem node_ready (request : NodeRequest Symbol Guard)
    (before chosen after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat) (result : Node)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored source before)
    (ready : NodeReady before.machine request) (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle,chosen))
    (demanded : demandNode handle chosen = (.ready result,after)) :
    NodePos source request result ∧ Stored source after ∧ after = chosen ∧ Available after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready request before chosen after handle result physical ready safe selected demanded
  have chosenStored := lookup_node before request stored
  simp only [selected] at chosenStored
  exact ⟨chosenStored.nodes.checked handle ⟨request,.returned result⟩ receipt.1,receipt.2.1 ▸ chosenStored,receipt.2⟩
private theorem edge_ready (request : EdgeRequest Symbol Guard)
    (before chosen after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat) (result : Row)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored source before)
    (ready : EdgeReady before.machine request) (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle,chosen))
    (demanded : demandEdge handle chosen = (.ready result,after)) :
    EdgePos source request result ∧ Stored source after ∧ after = chosen ∧ EdgeResident after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready request before chosen after handle result physical ready safe selected demanded
  have chosenStored := lookup_edge before request stored
  simp only [selected] at chosenStored
  exact ⟨chosenStored.edges.checked handle ⟨request,.returned result⟩ receipt.1,receipt.2.1 ▸ chosenStored,receipt.2⟩
private theorem node_started (request actual : NodeRequest Symbol Guard)
    (before chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored source before)
    (ready : NodeReady before.machine request) (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle,chosen))
    (demanded : demandNode handle chosen = (.evaluate actual,running)) :
    actual = request ∧ Stored source running ∧ running.nodes.cells handle = some ⟨request,.evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before chosen running handle physical ready safe selected demanded
  have chosenStored := lookup_node before request stored
  simp only [selected] at chosenStored
  have runningStored := demand_node chosen handle chosenStored
  simp only [demanded] at runningStored
  exact ⟨same,runningStored,same ▸ (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).2⟩
private theorem edge_started (request actual : EdgeRequest Symbol Guard)
    (before chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored source before)
    (ready : EdgeReady before.machine request) (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle,chosen))
    (demanded : demandEdge handle chosen = (.evaluate actual,running)) :
    actual = request ∧ Stored source running ∧ running.edges.cells handle = some ⟨request,.evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual before chosen running handle physical ready safe selected demanded
  have chosenStored := lookup_edge before request stored
  simp only [selected] at chosenStored
  have runningStored := demand_edge chosen handle chosenStored
  simp only [demanded] at runningStored
  exact ⟨same,runningStored,same ▸ (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).2⟩
private theorem node_yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (before : Checked width) (control : Control A) (after : Checked width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (stored : Stored source before.native) (oldStored : OldStore source before.native)
    (ready : NodeReady before.native.machine request)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.node request next)))
    (yielded : SourceEqualityNativeDemand.step (.code (.node request next)) before = .yielded control after) :
    after.native.machine = before.native.machine ∧ after.operations = before.operations ∧
      Stored source after.native ∧
      ((control = .code ((compileNode request).bind next) ∧ after = before) ∨
      (∃ value, control = .code (next value) ∧ Available after.native.machine.heap value ∧ NodePos source request value ∧ NodeLaw Plain source request value) ∨
      (∃ handle, control = .code ((compileNode request).bind
        (fun value => .finishNode handle value (next value))) ∧
        after.native.nodes.cells handle = some ⟨request, .evaluating⟩)) := by
  cases selected : lookupNode width request before.native with
  | mk selection chosen =>
    have chosenMachine : chosen.machine = before.native.machine := by
      simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request before.native
    cases selection with
    | direct actual =>
      obtain ⟨rfl, rfl⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request actual before.native chosen selected
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected,
        SourceEqualityNativeDemand.lift] at yielded
      cases yielded
      exact ⟨rfl, rfl, stored, Or.inl ⟨rfl, rfl⟩⟩
    | memoized handle =>
      obtain ⟨key, encoded, _, _⟩ :=
        SourceRecursiveIntersectionNative.lookupNode_memoized request before.native chosen handle selected
      have safe := words key encoded
      cases demanded : demandNode handle chosen with
      | mk observation running =>
        have machine : running.machine = before.native.machine := by
          simpa only [demanded, chosenMachine] using SourceRecursiveIntersectionNative.demandNode_machine handle chosen
        cases observation with
        | absent | busy =>
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
            SourceEqualityNativeDemand.lift] at yielded
          cases yielded
        | ready value =>
          have receipt := node_ready request before.native chosen running
            handle value valid stored ready safe selected demanded
          have oldLaw := SourceCurrentConstrainedCapCheckedJointCache.node_observed_ready Plain source request before.native chosen running
            handle value valid oldStored ready safe selected demanded
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
            SourceEqualityNativeDemand.lift] at yielded
          cases yielded
          exact ⟨machine, rfl, receipt.2.1, Or.inr (Or.inl ⟨value, rfl, receipt.2.2.2, receipt.1,oldLaw.1⟩)⟩
        | evaluate actual =>
          have started := node_started request actual before.native chosen running
            handle valid stored ready safe selected demanded
          have same := started.1
          subst actual
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
            SourceEqualityNativeDemand.lift] at yielded
          cases yielded
          exact ⟨machine, rfl, started.2.1, Or.inr (Or.inr ⟨handle, rfl, started.2.2⟩)⟩


private theorem edge_yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before : Checked width) (control : Control A) (after : Checked width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (stored : Stored source before.native) (oldStored : OldStore source before.native)
    (ready : EdgeReady before.native.machine request)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.edge request next)))
    (yielded : SourceEqualityNativeDemand.step (.code (.edge request next)) before = .yielded control after) :
    after.native.machine = before.native.machine ∧ after.operations = before.operations ∧
      Stored source after.native ∧
      ((∃ value, control = .code (next value) ∧ EdgeResident after.native.machine.heap value ∧ EdgePos source request value ∧ EdgeLaw Plain source request value) ∨
      (∃ handle, control = .edgeBody request (fun value => .finishEdge handle value (next value)) ∧
        after.native.edges.cells handle = some ⟨request, .evaluating⟩)) := by
  cases selected : lookupEdge width request before.native with
  | mk handle chosen =>
    have chosenMachine : chosen.machine = before.native.machine := by
      simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
    cases demanded : demandEdge handle chosen with
    | mk observation running =>
      have machine : running.machine = before.native.machine := by
        simpa only [demanded, chosenMachine] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
      cases observation with
      | absent | busy =>
        simp only [SourceEqualityNativeDemand.step, selected, demanded] at yielded
        cases yielded
      | ready value =>
        have receipt := edge_ready request before.native chosen running handle
          value valid stored ready words selected demanded
        have oldLaw := SourceCurrentConstrainedCapCheckedJointCache.edge_observed_ready Plain source request before.native chosen running
          handle value valid oldStored ready words selected demanded
        simp only [SourceEqualityNativeDemand.step, selected, demanded] at yielded
        cases yielded
        exact ⟨machine, rfl, receipt.2.1, Or.inl ⟨value, rfl, receipt.2.2.2, receipt.1,oldLaw.1⟩⟩
      | evaluate actual =>
        have started := edge_started request actual before.native chosen running
          handle valid stored ready words selected demanded
        have same := started.1
        subst actual
        simp only [SourceEqualityNativeDemand.step, selected, demanded] at yielded
        cases yielded
        exact ⟨machine, rfl, started.2.1, Or.inr ⟨handle, rfl, started.2.2⟩⟩


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {inventory : List DomainKey} {initialDomains : Cache.State DomainKey}
private abbrev OldReturn (before after : Checked width) (value : A)
    (physicalPost oldPost : Machine Symbol Guard → A → Prop) :=
  SourceCurrentConstrainedCapCheckedJointInduction.Return
    (source := source) (inventory := inventory) (initial := initialDomains) before after value physicalPost oldPost
private def Preserves (fuel : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before after : Checked width) (value : A)
    (physicalPost oldPost post : Machine Symbol Guard → A → Prop),
    Current source inventory initialDomains before → Physical source inventory control before.native.machine physicalPost →
    Fields control before → Context Plain source before.native.machine → Old source control before.native.machine oldPost →
    OldStore source before.native → ControlPos (source := source) control before.native.machine post →
    Stored source before.native → Causal before.native.machine →
    Trace fuel control before (.code (.pure value)) after → Stored source after.native ∧ post after.native.machine value
private theorem through (facts : Facts source) (closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory)
    (bound fuel : Nat) (ih : ∀ count, count < bound → Preserves (source := source) (inventory := inventory) (initialDomains := initialDomains) (width := width) count)
    (smaller : fuel < bound) (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked width) (value : B)
    (bodyPhysical oldBody bodyPost : Machine Symbol Guard → A → Prop)
    (physicalPost oldPost post : Machine Symbol Guard → B → Prop)
    (known : Current source inventory initialDomains before) (physical : Physical source inventory control before.native.machine bodyPhysical)
    (fields : Fields control before) (context : Context Plain source before.native.machine)
    (oldCertificate : Old source control before.native.machine oldBody) (oldStored : OldStore source before.native)
    (certificate : ControlPos (source := source) control before.native.machine bodyPost) (stored : Stored source before.native) (causal : Causal before.native.machine)
    (nextFields : ∀ result, CodeFields before.operations (next result))
    (continuation : ∀ result middle, OldReturn (source := source) (inventory := inventory) (initialDomains := initialDomains) before middle result bodyPhysical oldBody →
      Causal middle.native.machine → bodyPost middle.native.machine result →
      Physical source inventory (.code (next result)) middle.native.machine physicalPost ∧
      Old source (.code (next result)) middle.native.machine oldPost ∧
      ControlPos (source := source) (.code (next result)) middle.native.machine post)
    (actual : Trace fuel (control.bind next) before (.code (.pure value)) after) : Stored source after.native ∧ post after.native.machine value := by
  obtain ⟨inner,outer,result,middle,count,bodyTrace,outerTrace⟩ := SourceCurrentHereditaryNativePhysicalSplit.bind_split control next before after value actual
  have old := SourceCurrentConstrainedCapCheckedJointTrace.completed facts closed inner control before middle result _ _
    known physical fields context oldCertificate oldStored bodyTrace
  have pos := ih inner (by omega) control before middle result _ _ _ known physical fields context oldCertificate oldStored certificate stored causal bodyTrace
  obtain ⟨history⟩ := causal
  have middleCausal := (SourceCurrentNativePublicationTrace.from_history bodyTrace context.semantic history).2
  obtain ⟨nextPhysical,nextOld,nextPos⟩ := continuation result middle old middleCausal pos.2
  exact ih outer (by omega) (.code (next result)) middle after value _ _ _ old.current nextPhysical
    (SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (nextFields result) old.operations)
    old.context nextOld old.stored nextPos pos.1 middleCausal outerTrace

private theorem through_node (facts : Facts source) (closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory)
    (bound fuel handle : Nat) (ih : ∀ count, count < bound → Preserves (source := source) (inventory := inventory) (initialDomains := initialDomains) (width := width) count)
    (smaller : fuel < bound) (request : NodeRequest Symbol Guard) (next : Node → Code Symbol Guard A)
    (before after : Checked width) (value : A) (physicalPost oldPost post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initialDomains before) (context : Context Plain source before.native.machine)
    (oldStored : OldStore source before.native) (stored : Stored source before.native) (causal : Causal before.native.machine)
    (physical : Physical source inventory (.code (compileNode request)) before.native.machine (fun state result => Available state.heap result))
    (fields : Fields (.code (compileNode request)) before) (nextFields : ∀ result, CodeFields before.operations (next result))
    (oldCertificate : Old source (.code (compileNode request)) before.native.machine (fun _ result => NodeLaw Plain source request result))
    (certificate : ControlPos (source := source) (.code (compileNode request)) before.native.machine (fun _ result => NodePos source request result))
    (running : before.native.nodes.cells handle = some ⟨request,.evaluating⟩)
    (continuation : ∀ result middle, OldReturn (source := source) (inventory := inventory) (initialDomains := initialDomains) before middle result
      (fun state result => Available state.heap result) (fun _ result => NodeLaw Plain source request result) →
      Causal middle.native.machine → NodePos source request result →
      Physical source inventory (.code (next result)) middle.native.machine physicalPost ∧
      Old source (.code (next result)) middle.native.machine oldPost ∧ ControlPos (source := source) (.code (next result)) middle.native.machine post)
    (actual : Trace fuel ((.code (compileNode request) : Control Node).bind (fun result => .finishNode handle result (next result))) before (.code (.pure value)) after) :
    Stored source after.native ∧ post after.native.machine value := by
  obtain ⟨inner,frame,result,middle,count,bodyTrace,frameTrace⟩ := SourceCurrentHereditaryNativePhysicalSplit.bind_split
    (.code (compileNode request)) (fun result => .finishNode handle result (next result)) before after value actual
  cases frameTrace with
  | cons _ _ chosen reached _ _ rest frameInputs frameStep outerTrace =>
    have one : step (.code (.finishNode handle result (next result))) middle =
        .yielded (.code (next result)) {middle with native := finishNode handle result middle.native} := rfl
    obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (frameStep.symm.trans one)
    have old := SourceCurrentConstrainedCapCheckedJointTrace.completed facts closed inner _ before middle result _ _ known physical fields context oldCertificate oldStored bodyTrace
    have pos := ih inner (by omega) _ before middle result _ _ _ known physical fields context oldCertificate oldStored certificate stored causal bodyTrace
    have owner := (SourceEqualityNativeDemandProtectedPrefix.node_body_owner inner handle request before middle result known.good.native.shape running bodyTrace.steps).1
    let finished : Checked width := {middle with native := finishNode handle result middle.native}
    have effects := SourceCurrentAllocatedRecursivePrefixState.yielded (.code (.finishNode handle result (next result))) (.code (next result)) middle finished old.current
      ⟨request,owner,old.physical⟩ trivial
      (SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (nextFields result) old.operations) one
    have kept := SourceCurrentConstrainedCapCheckedJointCache.finishNode_stored Plain source middle.native handle request result old.stored owner old.result
    have middleCausal := (SourceCurrentNativePublicationTrace.from_history bodyTrace context.semantic (Classical.choice causal)).2
    have oldFinished : OldReturn (source := source) (inventory := inventory) (initialDomains := initialDomains) before finished result
        (fun state result => Available state.heap result) (fun _ result => NodeLaw Plain source request result) :=
      ⟨effects.1,old.extension.trans effects.2.1,
        SourceCurrentAllocatedRecursivePrefixReceipt.operations_trans old.operations effects.2.2.2.1,old.context,kept,old.physical,old.result⟩
    obtain ⟨nextPhysical,nextOld,nextPos⟩ := continuation result finished oldFinished middleCausal pos.2
    exact ih rest (by omega) (.code (next result)) finished after value _ _ _ effects.1 nextPhysical effects.2.2.2.2 old.context nextOld kept nextPos
      (finish_node middle.native handle request result pos.1 owner pos.2) middleCausal outerTrace

private theorem through_edge (facts : Facts source) (closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory)
    (bound fuel handle : Nat) (ih : ∀ count, count < bound → Preserves (source := source) (inventory := inventory) (initialDomains := initialDomains) (width := width) count)
    (smaller : fuel < bound) (request : EdgeRequest Symbol Guard) (next : Row → Code Symbol Guard A)
    (before after : Checked width) (value : A) (physicalPost oldPost post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initialDomains before) (context : Context Plain source before.native.machine)
    (oldStored : OldStore source before.native) (stored : Stored source before.native) (causal : Causal before.native.machine)
    (physical : Physical source inventory (.edgeBody request .pure) before.native.machine (fun state result => EdgeResident state.heap result))
    (fields : Fields (.edgeBody request .pure) before) (nextFields : ∀ result, CodeFields before.operations (next result))
    (oldCertificate : Old source (.edgeBody request .pure) before.native.machine (fun _ result => EdgeLaw Plain source request result))
    (certificate : ControlPos (source := source) (.edgeBody request .pure) before.native.machine (fun _ result => EdgePos source request result))
    (running : before.native.edges.cells handle = some ⟨request,.evaluating⟩)
    (continuation : ∀ result middle, OldReturn (source := source) (inventory := inventory) (initialDomains := initialDomains) before middle result
      (fun state result => EdgeResident state.heap result) (fun _ result => EdgeLaw Plain source request result) →
      Causal middle.native.machine → EdgePos source request result →
      Physical source inventory (.code (next result)) middle.native.machine physicalPost ∧
      Old source (.code (next result)) middle.native.machine oldPost ∧ ControlPos (source := source) (.code (next result)) middle.native.machine post)
    (actual : Trace fuel ((.edgeBody request .pure : Control Row).bind (fun result => .finishEdge handle result (next result))) before (.code (.pure value)) after) :
    Stored source after.native ∧ post after.native.machine value := by
  obtain ⟨inner,frame,result,middle,count,bodyTrace,frameTrace⟩ := SourceCurrentHereditaryNativePhysicalSplit.bind_split
    (.edgeBody request .pure) (fun result => .finishEdge handle result (next result)) before after value actual
  cases frameTrace with
  | cons _ _ chosen reached _ _ rest frameInputs frameStep outerTrace =>
    have one : step (.code (.finishEdge handle result (next result))) middle =
        .yielded (.code (next result)) {middle with native := finishEdge handle result middle.native} := rfl
    obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (frameStep.symm.trans one)
    have old := SourceCurrentConstrainedCapCheckedJointTrace.completed facts closed inner _ before middle result _ _ known physical fields context oldCertificate oldStored bodyTrace
    have pos := ih inner (by omega) _ before middle result _ _ _ known physical fields context oldCertificate oldStored certificate stored causal bodyTrace
    have owner := (SourceEqualityNativeDemandProtectedPrefix.edge_body_owner inner handle request before middle result known.good.native.shape running bodyTrace.steps).1
    let finished : Checked width := {middle with native := finishEdge handle result middle.native}
    have effects := SourceCurrentAllocatedRecursivePrefixState.yielded (.code (.finishEdge handle result (next result))) (.code (next result)) middle finished old.current
      ⟨request,owner,old.physical⟩ trivial
      (SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (nextFields result) old.operations) one
    have kept := SourceCurrentConstrainedCapCheckedJointCache.finishEdge_stored Plain source middle.native handle request result old.stored owner old.result
    have middleCausal := (SourceCurrentNativePublicationTrace.from_history bodyTrace context.semantic (Classical.choice causal)).2
    have oldFinished : OldReturn (source := source) (inventory := inventory) (initialDomains := initialDomains) before finished result
        (fun state result => EdgeResident state.heap result) (fun _ result => EdgeLaw Plain source request result) :=
      ⟨effects.1,old.extension.trans effects.2.1,
        SourceCurrentAllocatedRecursivePrefixReceipt.operations_trans old.operations effects.2.2.2.1,old.context,kept,old.physical,old.result⟩
    obtain ⟨nextPhysical,nextOld,nextPos⟩ := continuation result finished oldFinished middleCausal pos.2
    exact ih rest (by omega) (.code (next result)) finished after value _ _ _ effects.1 nextPhysical effects.2.2.2.2 old.context nextOld kept nextPos
      (finish_edge middle.native handle request result pos.1 owner pos.2) middleCausal outerTrace
private theorem completed (facts : Facts source) (closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory)
    (fuel : Nat) : Preserves (source := source) (inventory := inventory) (initialDomains := initialDomains) (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind count ih =>
    intro A control before after value physicalPost oldPost post known physical fields context oldCertificate oldStored certificate stored causal actual
    have admitted := SourceCurrentAllocatedRecursivePrefixControl.entered source inventory control before.native.machine physicalPost physical
    cases count with
    | zero => cases actual; exact ⟨stored,certificate⟩
    | succ fuel =>
      cases actual with
      | cons _ _ resume middle _ _ _ inputs one tail =>
        have effects := SourceCurrentAllocatedRecursivePrefixState.yielded control resume before middle known inputs admitted fields one
        have middleContext := SourceCurrentConstrainedCapCheckedJointControl.yielded_context Plain source control resume before middle context effects.1 inputs one
        have stepHistory := (SourceCurrentNativePublicationTrace.step control before context.semantic
          (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs)).2
        have middleCausal : Causal middle.native.machine := by
          obtain ⟨earlier⟩ := causal
          obtain ⟨interval⟩ := (show Nonempty (SourceCurrentNativeMuPublication.History before.native.machine.heap middle.native.machine.heap) from by simpa only [one,Outcome.state] using stepHistory)
          exact ⟨.trans earlier interval⟩
        cases control with
        | edgeBody request next =>
          obtain ⟨body,pureBody,same⟩ := SourceEqualityNativeDemandBodyYield.yielded_unbind request next before middle resume one
          subst resume
          have data := SourceCurrentAllocatedRecursivePrefixControl.edge_data source inventory request next before.native.machine physicalPost physical
          have bodyPhysical := SourceCurrentAllocatedRecursivePrefixCode.body_certified source inventory facts request data.1 data.2.1 before middle body known.good.native.machine known.semantic data.2.2 pureBody
          have bodyFields := SourceCurrentAllocatedNativeFieldClosure.body_fields request .pure before middle (.code body) known.good.fields data.2.2 known.good.operations (fun _ => trivial) pureBody
          have nativeSame : middle.native = before.native := by simpa only [pureBody,Outcome.state] using SourceEqualityNativeDemandOperations.body_native request .pure before
          have middleOld : OldStore source middle.native := nativeSame ▸ oldStored
          have middleStored : Stored source middle.native := nativeSame ▸ stored
          have bodyOld := oldCertificate.1 width before middle body rfl known.good context data.2.2 pureBody
          have bodyPos := edge_body_pos request before middle body known.good context causal data.2.2 pureBody
          apply through facts closed (fuel+1) fuel ih (by omega) (.code body) next middle after value (fun final value => EdgeResident final.heap value) (fun _ value => EdgeLaw Plain source request value) (fun _ value => EdgePos source request value) physicalPost oldPost post effects.1 bodyPhysical bodyFields middleContext bodyOld middleOld bodyPos middleStored middleCausal
            (fun result => SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (fields.2 result) effects.2.2.2.1) ?_ tail
          intro result final returned finalCausal law
          exact ⟨SourceCurrentAllocatedRecursivePrefixControl.edge_next source inventory request next before.native.machine physicalPost physical result final.native.machine returned.current.good.native.machine (effects.2.1.trans returned.extension) returned.current.semantic returned.physical,
            oldCertificate.2 result final.native.machine (effects.2.1.trans returned.extension) returned.context returned.physical returned.result,
            certificate result final.native.machine (effects.2.1.trans returned.extension) returned.context finalCausal returned.physical returned.result law⟩
        | code code =>
          cases code with
          | pure | fail => cases one
          | finishNode | finishEdge => cases certificate
          | work job next =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            have nextPhysical := SourceCurrentAllocatedRecursivePrefixCode.work_next source inventory job next before.native.machine physicalPost physical known.semantic _ _ rfl
            exact ih fuel (by omega) (.code (next (InternedConstructorTemplates.run job before.native.machine.heap).1)) _ after value _ _ _ effects.1 nextPhysical.2.2.2 effects.2.2.2.2 middleContext
              (oldCertificate _ _ rfl effects.2.1 middleContext) ⟨oldStored.nodes,oldStored.edges⟩
              (certificate _ _ rfl effects.2.1 middleContext middleCausal) ⟨stored.nodes,stored.edges⟩ middleCausal tail
          | enter domain left right first second next =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            have nextPhysical := SourceCurrentAllocatedRecursivePrefixCode.enter_next source inventory domain left right first second next before.native.machine physicalPost physical known.semantic
            exact ih fuel (by omega) (.code (next (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second).1)) _ after value _ _ _ effects.1 nextPhysical.2.2.2 effects.2.2.2.2 middleContext
              (oldCertificate effects.2.1 middleContext) ⟨oldStored.nodes,oldStored.edges⟩
              (certificate effects.2.1 middleContext middleCausal) ⟨stored.nodes,stored.edges⟩ middleCausal tail
          | read name next =>
            obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
            exact ih fuel (by omega) (.code (next (SourcePreparedSharedRows.read before.native.machine.heap name))) _ after value _ _ _ effects.1
              (SourceCurrentAllocatedRecursivePrefixCode.read_next source inventory name next before.native.machine physicalPost physical)
              effects.2.2.2.2 middleContext oldCertificate oldStored certificate stored middleCausal tail
          | optionalBinder pair body next =>
            cases constructing : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
            | pending key heap => simp only [step,SourceRecursiveIntersectionNative.step,constructing,lift] at one; cases one
            | done result heap =>
              simp only [step,SourceRecursiveIntersectionNative.step,constructing,lift] at one
              obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj one
              have done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap) before.native.machine = .done result {before.native.machine with heap := heap} := by rw [constructing]; rfl
              have nextPhysical := SourceCurrentAllocatedRecursivePrefixCode.optionalBinder_next source inventory pair body next before.native.machine physicalPost physical known.semantic _ _ done
              exact ih fuel (by omega) (.code (next result)) _ after value _ _ _ effects.1 nextPhysical.2.2.2 effects.2.2.2.2 middleContext
                (oldCertificate _ _ done effects.2.1 middleContext) ⟨oldStored.nodes,oldStored.edges⟩
                (certificate _ _ done effects.2.1 middleContext middleCausal) ⟨stored.nodes,stored.edges⟩ middleCausal tail
          | node request next =>
            have data := SourceCurrentAllocatedRecursivePrefixCode.node_data source inventory request next before.native.machine physicalPost physical
            have oldStep := SourceCurrentConstrainedCapCheckedJointTransition.node_yielded Plain source request next before resume middle known.good.native oldStored data.1 inputs.2 one
            obtain ⟨machine,operations,middleStored,branches⟩ := node_yielded request next before resume middle known.good.native stored oldStored data.1 inputs.2 one
            have ready : NodeReady middle.native.machine request := by rw [machine]; exact data.1
            have bodyPhysical := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory facts closed request data.2.1 data.2.2 middle.native.machine effects.1.good.native.machine effects.1.semantic ready effects.1.growth effects.1.history
            have bodyOld := SourceCurrentConstrainedCapCheckedJointCompile.node_law_certified Plain source facts request middle.native.machine middleContext ready.1
            have bodyPos := node_law_pos facts request middle.native.machine middleContext middleCausal
            have bodyFields := SourceCurrentAllocatedNativeCodeFields.compileNode_fields middle.operations request
            have nextFields : ∀ result, CodeFields middle.operations (next result) := by rw [operations]; exact fields
            have continuation : ∀ result final, OldReturn (source := source) (inventory := inventory) (initialDomains := initialDomains) middle final result
                (fun state result => Available state.heap result) (fun _ result => NodeLaw Plain source request result) → Causal final.native.machine → NodePos source request result →
                Physical source inventory (.code (next result)) final.native.machine physicalPost ∧ Old source (.code (next result)) final.native.machine oldPost ∧ ControlPos (source := source) (.code (next result)) final.native.machine post := by
              intro result final returned finalCausal law
              exact ⟨SourceCurrentAllocatedRecursivePrefixCode.node_next source inventory request next before.native.machine physicalPost physical result final.native.machine returned.current.good.native.machine (effects.2.1.trans returned.extension) returned.current.semantic returned.physical,
                oldCertificate result final.native.machine (effects.2.1.trans returned.extension) returned.context returned.physical returned.result,
                certificate result final.native.machine (effects.2.1.trans returned.extension) returned.context finalCausal returned.physical returned.result law⟩
            rcases branches with ⟨rfl,_⟩ | ⟨result,rfl,available,law,oldLaw⟩ | ⟨handle,rfl,running⟩
            · exact through facts closed (fuel+1) fuel ih (by omega) (.code (compileNode request)) next middle after value (fun final value => Available final.heap value) (fun _ value => NodeLaw Plain source request value) (fun _ value => NodePos source request value) physicalPost oldPost post effects.1 bodyPhysical bodyFields middleContext bodyOld oldStep.2.2.1 bodyPos middleStored middleCausal nextFields continuation tail
            · exact ih fuel (by omega) _ middle after value _ _ _ effects.1
                (SourceCurrentAllocatedRecursivePrefixCode.node_next source inventory request next before.native.machine physicalPost physical result middle.native.machine effects.1.good.native.machine effects.2.1 effects.1.semantic available) (nextFields result) middleContext
                (oldCertificate result middle.native.machine effects.2.1 middleContext available oldLaw) oldStep.2.2.1
                (certificate result middle.native.machine effects.2.1 middleContext middleCausal available oldLaw law) middleStored middleCausal tail
            · exact through_node facts closed (fuel+1) fuel handle ih (by omega) request next middle after value physicalPost oldPost post effects.1 middleContext oldStep.2.2.1 middleStored middleCausal bodyPhysical bodyFields nextFields bodyOld bodyPos running continuation tail
          | edge request next =>
            have data := SourceCurrentAllocatedRecursivePrefixCode.edge_data source inventory request next before.native.machine physicalPost physical
            have oldStep := SourceCurrentConstrainedCapCheckedJointTransition.edge_yielded Plain source request next before resume middle known.good.native oldStored data.1 inputs.2 one
            obtain ⟨machine,operations,middleStored,branches⟩ := edge_yielded request next before resume middle known.good.native stored oldStored data.1 inputs.2 one
            have ready : EdgeReady middle.native.machine request := by rw [machine]; exact data.1
            have bodyPhysical := SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request middle.native.machine data.2.1 data.2.2 ready
            have bodyOld : Old source (.edgeBody request .pure) middle.native.machine (fun _ result => EdgeLaw Plain source request result) :=
              ⟨by
                intro width before after body same good context ready yielded
                rw [←same] at context ready
                exact SourceCurrentConstrainedCapCheckedJointEdge.body_law_certified source request before after body good context ready yielded,
                fun _ _ _ _ _ law => law⟩
            have bodyPos : ControlPos (source := source) (.edgeBody request .pure) middle.native.machine (fun _ result => EdgePos source request result) := fun _ _ _ _ _ _ _ law => law
            have bodyFields : Fields (.edgeBody request .pure) middle := ⟨ready,fun _ => trivial⟩
            have nextFields : ∀ result, CodeFields middle.operations (next result) := by rw [operations]; exact fields
            have continuation : ∀ result final, OldReturn (source := source) (inventory := inventory) (initialDomains := initialDomains) middle final result
                (fun state result => EdgeResident state.heap result) (fun _ result => EdgeLaw Plain source request result) → Causal final.native.machine → EdgePos source request result →
                Physical source inventory (.code (next result)) final.native.machine physicalPost ∧ Old source (.code (next result)) final.native.machine oldPost ∧ ControlPos (source := source) (.code (next result)) final.native.machine post := by
              intro result final returned finalCausal law
              exact ⟨SourceCurrentAllocatedRecursivePrefixCode.edge_next source inventory request next before.native.machine physicalPost physical result final.native.machine returned.current.good.native.machine (effects.2.1.trans returned.extension) returned.current.semantic returned.physical,
                oldCertificate result final.native.machine (effects.2.1.trans returned.extension) returned.context returned.physical returned.result,
                certificate result final.native.machine (effects.2.1.trans returned.extension) returned.context finalCausal returned.physical returned.result law⟩
            rcases branches with ⟨result,rfl,resident,law,oldLaw⟩ | ⟨handle,rfl,running⟩
            · exact ih fuel (by omega) _ middle after value _ _ _ effects.1
                (SourceCurrentAllocatedRecursivePrefixCode.edge_next source inventory request next before.native.machine physicalPost physical result middle.native.machine effects.1.good.native.machine effects.2.1 effects.1.semantic resident) (nextFields result) middleContext
                (oldCertificate result middle.native.machine effects.2.1 middleContext resident oldLaw) oldStep.2.2.1
                (certificate result middle.native.machine effects.2.1 middleContext middleCausal resident oldLaw law) middleStored middleCausal tail
            · exact through_edge facts closed (fuel+1) fuel handle ih (by omega) request next middle after value physicalPost oldPost post effects.1 middleContext oldStep.2.2.1 middleStored middleCausal bodyPhysical bodyFields nextFields bodyOld bodyPos running continuation tail

/-- An actual completed supported request derives its result and both returned native cell laws. -/
theorem call (source : Heap) (facts : Facts source) (depth : Nat)
    (before after : Checked width) (left right result : Node) (fuel : Nat)
    (known : Current source (SourceRecursiveIntersectionSourceInventory.domains source) initialDomains before)
    (context : Context Plain source before.native.machine)
    (causal : SourceCurrentNativeMuPublication.History empty before.native.machine.heap)
    (oldStored : OldStore source before.native) (supported : Support source before.native)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right)
    (actual : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before (.code (.pure result)) after) :
    Support source after.native ∧ (∀ path, PositiveAt result path → PositiveAt left path ∨ PositiveAt right path) ∧
    SourceCurrentConstrainedCapCheckedJointInduction.Return
      (source := source) (inventory := SourceRecursiveIntersectionSourceInventory.domains source) (initial := initialDomains)
      before after result (fun final value => Available final.heap value)
      (fun _ value => NodeLaw Plain source ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩ value) ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts request.domain left right leftAvailable rightAvailable leftClosed rightClosed
  have ready : NodeReady before.native.machine request := ⟨empty_domain _,
    leftAvailable.grows source _ context.growth context.history,rightAvailable.grows source _ context.growth context.history⟩
  have physical : Physical source (SourceRecursiveIntersectionSourceInventory.domains source) (.code (requestNode request.domain left right)) before.native.machine (fun final value => Available final.heap value) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node source _ request before.native.machine ready
    (initial_scope source left right inputs.1 inputs.2.1 leftAvailable rightAvailable)
    (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  have oldCertificate : Old source (.code (requestNode request.domain left right)) before.native.machine (fun _ value => NodeLaw Plain source request value) := fun _ _ _ _ _ law => law
  have certificate : ControlPos (source := source) (.code (requestNode request.domain left right)) before.native.machine (fun _ value => NodePos source request value) := fun _ _ _ _ _ _ _ law => law
  have closed := SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts
  have pos := completed facts closed fuel _ before after result _ _ _ known physical (fun _ => trivial) context oldCertificate oldStored certificate ⟨supported.1,supported.2⟩ ⟨causal⟩ actual
  have old := SourceCurrentConstrainedCapCheckedJointTrace.completed facts closed fuel _ before after result _ _ known physical (fun _ => trivial) context oldCertificate oldStored actual
  exact ⟨⟨pos.1.nodes,pos.1.edges⟩,pos.2 depth (SourceCurrentConstrainedCapOriginalSupport.empty Plain source) inputs leftCap rightCap,old,
    (SourceCurrentNativePublicationTrace.from_history actual context.semantic causal).2⟩

/-- Empty native tables derive every entry law for one actual closed finite-cap request. -/
theorem request (width depth : Nat) (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good (⟨initial width machine,operations⟩ : Checked width))
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady machine.heap)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap)
    (causal : SourceCurrentNativeMuPublication.History empty machine.heap)
    (left right result : Node) (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right) (fuel : Nat) (after : Checked width)
    (actual : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      ⟨initial width machine,operations⟩ (.code (.pure result)) after) :
    Support machine.heap after.native ∧ (∀ path, PositiveAt result path → PositiveAt left path ∨ PositiveAt right path) ∧
    SourceCurrentConstrainedCapCheckedJointInduction.Return
      (source := machine.heap) (inventory := SourceRecursiveIntersectionSourceInventory.domains machine.heap) (initial := machine.domains)
      ⟨initial width machine,operations⟩ after result (fun final value => Available final.heap value)
      (fun _ value => NodeLaw Plain machine.heap ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩ value) ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) := by
  have known := SourceCurrentAllocatedRecursivePrefixState.initial machine.heap (SourceRecursiveIntersectionSourceInventory.domains machine.heap) (⟨initial width machine,operations⟩ : Checked width) good semantic rfl
  exact call machine.heap good.native.machine.1 depth _ after left right result fuel known
    ⟨good.native.machine,semantic.ready.semantic,guards,grows_refl _,extends_refl _⟩ causal
    (SourceCurrentConstrainedCapCheckedJointCache.initial_stored Plain machine.heap width machine)
    ⟨FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩ leftAvailable rightAvailable leftClosed rightClosed leftCap rightCap actual

end MicroCFTA.SourceCurrentNativeRequestPositivePositions
