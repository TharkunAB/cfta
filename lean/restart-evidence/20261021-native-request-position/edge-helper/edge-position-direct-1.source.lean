import MicroCFTA.SourceCurrentConstrainedCapCheckedJointTrace
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointClosed
import MicroCFTA.SourceCurrentNativeMaybeMuPositivePositions
import MicroCFTA.SourceCurrentNativePublicationTrace

/-! # Positive child positions in actual native requests -/
namespace MicroCFTA.SourceCurrentNativeRequestPositivePositions
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
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
private abbrev Causal (state : Machine Symbol Guard) :=
  Nonempty (SourceCurrentNativeMuPublication.History empty state.heap)
private abbrev Back (left right result : Node) :=
  ∀ path, PositiveAt result path → PositiveAt left path ∨ PositiveAt right path
private abbrev RowBack (left right result : Row) :=
  (SourceMemoGate.plain result.entry.key.constraint = false →
    SourceMemoGate.plain left.entry.key.constraint = false ∨ SourceMemoGate.plain right.entry.key.constraint = false) ∧
  ∀ index child, result.children[index]? = some child → ∀ path, PositiveAt child path →
    (∃ original, left.children[index]? = some original ∧ PositiveAt original path) ∨
    (∃ original, right.children[index]? = some original ∧ PositiveAt original path)
private def NodePos (source : Heap) (request : NodeRequest Symbol Guard) (result : Node) :=
  ∀ depth, OriginalBindings Plain source request.domain.key → NodeInputs source request →
    Cap Plain depth request.left → Cap Plain depth request.right → Back request.left request.right result
private def EdgePos (source : Heap) (request : EdgeRequest Symbol Guard) (result : Row) :=
  ∀ depth, OriginalBindings Plain source request.domain.key → EdgeInputs source request →
    Edge Plain depth request.left → Edge Plain depth request.right → RowBack request.left request.right result
private structure Stored (source : Heap) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop where
  nodes : Returned (NodePos source) state.nodes
  edges : Returned (EdgePos source) state.edges

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
  | .optionalBinder pair body next => ∀ value after,
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.heap) state = .done value after →
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
      EdgeResident after.heap value → EdgeLaw Plain source request value → EdgePos source request value → CodePos (next value) after post
private theorem pos_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state)
    (middle : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : CodePos code state middle)
    (continuation : ∀ value after, Extension state after → Context Plain source after → Causal after →
      middle after value → CodePos (next value) after post) : CodePos (code.bind next) state post := by
  induction code generalizing state with
  | pure value => exact continuation value state (.refl _) context causal certificate
  | fail => trivial
  | work job resume ih | optionalBinder pair body resume ih =>
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
    (known : ∀ i, CodePos code state (post i)) : CodePos code state (fun after value => ∀ i, post i after value) := by
  induction code generalizing state with
  | pure => exact known
  | fail => trivial
  | work job resume ih | optionalBinder pair body resume ih =>
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
    (first second : Machine Symbol Guard → A → Prop) (known : CodePos code state first)
    (implies : ∀ after value, first after value → second after value) : CodePos code state second := by
  induction code generalizing state with
  | pure value => exact implies state value known
  | fail => trivial
  | work job resume ih | optionalBinder pair body resume ih =>
      intro value after done growth context causal
      exact ih value after (known value after done growth context causal) implies
  | enter domain left right first second resume ih =>
      intro growth context causal
      exact ih _ _ (known growth context causal) implies
  | read name resume ih => exact ih _ state known implies
  | node request resume ih | edge request resume ih =>
      intro value after growth context causal physical old law
      exact ih value after (known value after growth context causal physical old law) implies
  | finishNode | finishEdge => cases known
private theorem pos_walk (call : A → Code Symbol Guard B) (requests : List A)
    (relation : Machine Symbol Guard → A → B → Prop)
    (stable : ∀ before after, Extension before after → ∀ request result, relation before request result → relation after request result)
    (calls : ∀ request ∈ requests, ∀ state, Context Plain source state → Causal state →
      CodePos (call request) state (fun after value => relation after request value))
    (state : Machine Symbol Guard) (context : Context Plain source state) (causal : Causal state) :
    CodePos (walk call requests) state (fun after values => All₂ (relation after) requests values) := by
  induction requests generalizing state with
  | nil => exact .nil
  | cons first rest ih =>
      apply pos_bind _ _ state context causal _ _ (calls first List.mem_cons_self state context causal)
      intro result middle _ middleContext middleCausal law
      apply pos_bind _ _ middle middleContext middleCausal _ _
        (ih (fun request member => calls request (List.mem_cons_of_mem _ member)) middle middleContext middleCausal)
      intro results after growth _ _ laws
      exact .cons (stable middle after growth first result law) laws

private theorem edge_work_pos (request : EdgeRequest Symbol Guard) (guard : Guard)
    (values : List Node) (state : Machine Symbol Guard) (context : Context Plain source state)
    (guardBack : SourceMemoGate.plain guard = false →
      SourceMemoGate.plain request.left.entry.key.constraint = false ∨
        SourceMemoGate.plain request.right.entry.key.constraint = false)
    (related : All₂ (fun pair value => Available state.heap value ∧ Back pair.1 pair.2 value)
      (request.left.children.zip request.right.children) values) :
    CodePos (.work (makeEdge request.left.entry.key.symbol guard values) .pure) state
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
    CodePos (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
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
    CodePos (SourceEqualityNativeCheckedCode.sentinel request.left) state
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
    CodePos code after.native.machine (fun _ result => RowBack request.left request.right result) := by
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
                by_cases firstPlain : SourceMemoGate.plain request.left.entry.key.constraint = false
                · exact .inl firstPlain
                · right
                  by_contra rightPlain
                  have firstTrue : SourceMemoGate.plain request.left.entry.key.constraint = true := Bool.eq_true_of_not_eq_false firstPlain
                  have rightTrue : SourceMemoGate.plain request.right.entry.key.constraint = true := Bool.eq_true_of_not_eq_false rightPlain
                  have combinedPlain := SourceCurrentUnconstrainedGuardClosure.loaded_ready_plain
                    GuardStructuralOrder.le request.left.entry.key.constraint request.right.entry.key.constraint
                    first second request.left.children.length request.right.children.length before.operations good.operations
                    firstCached secondCached firstLoaded secondLoaded firstTrue rightTrue combined done
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

private theorem edge_body_pos [DecidableEq Symbol] (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (code : Code Symbol Guard Row)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (context : Context Plain source before.native.machine) (causal : Causal before.native.machine)
    (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    CodePos code after.native.machine (fun _ result => EdgePos source request result) := by
  have clean : BodyCode code := SourceEqualityNativeDemandBodyCode.body_clean request .pure before after (.code code)
    yielded (fun _ => trivial)
  let Spec := {depth : Nat // OriginalBindings Plain source request.domain.key ∧ EdgeInputs source request ∧
    Edge Plain depth request.left ∧ Edge Plain depth request.right}
  have all : CodePos code after.native.machine (fun _ result => ∀ spec : Spec, RowBack request.left request.right result) := by
    apply pos_forall code after.native.machine _ clean
    intro spec
    exact edge_body_fixed_pos spec.val request before after code good context causal ready spec.property.1
      spec.property.2.1 spec.property.2.2.1 spec.property.2.2.2 yielded
  apply pos_mono code after.native.machine _ _ all
  intro final result returned depth bindings inputs left right
  exact returned ⟨depth, bindings, inputs, left, right⟩

end MicroCFTA.SourceCurrentNativeRequestPositivePositions
