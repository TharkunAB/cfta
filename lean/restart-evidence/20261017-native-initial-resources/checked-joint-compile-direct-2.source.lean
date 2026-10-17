import MicroCFTA.SourceCurrentConstrainedCapCheckedJointCode

/-!
# Joint laws for every literal checked node branch

The compiler consumes exact conditional laws from smaller requests.
Actual constructor returns and selected binder winners determine each
result law. These certificates do not assert query completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointCompile
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (decision repeatedValue identity pair)
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs EdgeInputs edgeBudget)
open SourceCurrentConstrainedCapPairOccurrences (Classified FreeLE FreeBelow sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (rank pairRank)
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointCode
variable {Symbol Guard : Type}

/-- One actual returned node retains all supported local result laws. -/
abbrev Post (annotation : Guard → Prop) (source : State Symbol Guard) (depth : Nat)
    (request : NodeRequest Symbol Guard) : Machine Symbol Guard → Value Symbol Guard → Prop :=
  fun after value => Available after.heap value ∧ Cap annotation depth value ∧
    Classified (sourceWeight annotation source) (pairRank annotation request.left request.right) value ∧
    Scope request.domain.key.seen value

private theorem certified_walk [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard) (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, Context annotation source state → input state request →
      Certified annotation source (call request) state output)
    (state : Machine Symbol Guard) (context : Context annotation source state)
    (inputs : ∀ request ∈ requests, input state request) :
    Certified annotation source (SourceRecursiveIntersectionCode.walk call requests) state
      (fun after values => ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => intro value member; cases member
  | cons first rest ih =>
      apply certified_bind annotation source _ _ state context output _
        (calls first List.mem_cons_self state context (inputs first List.mem_cons_self))
      intro value after growth afterContext returned
      have tail := ih (fun request member => calls request (List.mem_cons_of_mem _ member)) after afterContext
        (fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member)))
      apply certified_bind annotation source _ _ after afterContext _ _ tail
      intro values final later _ all result member
      rcases List.mem_cons.mp member with rfl | present
      · exact outputStable after final later result returned
      · exact all result present

variable [DecidableEq (EdgeKey Symbol Guard)]
variable (annotation : Guard → Prop) (source : State Symbol Guard)

private theorem request_node (depth : Nat) (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (bindings : OriginalBindings annotation source request.domain.key) (inputs : NodeInputs source request)
    (left : Cap annotation depth request.left) (right : Cap annotation depth request.right) :
    Certified annotation source (requestNode request.domain request.left request.right) state (Post annotation source depth request) :=
  fun _ _ _ _ available law => ⟨available, law depth bindings inputs left right⟩

private theorem node_work (depth bound : Nat) (domain : Interned DomainKey) (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (context : Context annotation source state)
    (resident : ∀ edge ∈ edges, EdgeResident state.heap edge)
    (bounded : ∀ edge ∈ edges, Edge annotation depth edge)
    (children : ∀ edge ∈ edges, ∀ value ∈ edge.children,
      FreeLE (sourceWeight annotation source) bound value ∧ FreeBelow (sourceWeight annotation source) bound value)
    (scopes : ∀ edge ∈ edges, EdgeScope domain.key.seen edge) :
    Certified annotation source (.work (makeNode edges) .pure) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) bound value ∧ Scope domain.key.seen value) := by
  intro value after done _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.node_verified edges state.heap context.valid.1 resident).result _ _ rfl,
    SourceCurrentConstrainedCap.makeNode annotation depth edges state.heap context.valid.1.coherent context.valid.1.linked resident bounded,
    SourceCurrentConstrainedCapPairOccurrences.makeNode _ bound edges state.heap context.valid.1 resident children,
    SourceRecursiveIntersectionResultScope.node domain.key.seen edges state.heap context.valid.1 resident scopes⟩

private theorem union_work (depth bound : Nat) (domain : Interned DomainKey) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (context : Context annotation source state)
    (available : ∀ value ∈ values, Available state.heap value)
    (bounded : ∀ value ∈ values, Cap annotation depth value)
    (classified : ∀ value ∈ values, Classified (sourceWeight annotation source) bound value)
    (scopes : ∀ value ∈ values, Scope domain.key.seen value) :
    Certified annotation source (.work (makeUnion values) .pure) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) bound value ∧ Scope domain.key.seen value) := by
  intro value after done _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨(InternedNestedFacts.union_verified values state.heap context.valid.1 available).result _ _ rfl,
    SourceCurrentConstrainedCap.makeUnion annotation depth values state.heap context.valid.1 available bounded,
    SourceCurrentConstrainedCapPairOccurrences.makeUnion _ bound values state.heap context.semantic.1.normal available classified,
    SourceRecursiveIntersectionResultScope.union domain.key.seen values state.heap context.semantic.1.normal available scopes⟩

private theorem rows_certified [DecidableEq Symbol] (depth : Nat) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (facts : Facts source)
    (bindings : OriginalBindings annotation source domain.key) (inputs : NodeInputs source ⟨domain, left, right⟩)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (state : Machine Symbol Guard) (context : Context annotation source state) :
    Certified annotation source (compileRows domain (nodeEdges left) (nodeEdges right)) state
      (Post annotation source depth ⟨domain, left, right⟩) := by
  let input := fun (_ : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Edge annotation depth pair.1 ∧ Edge annotation depth pair.2 ∧ EdgeInputs source ⟨domain, pair.1, pair.2⟩
  let output := fun (after : Machine Symbol Guard) (edge : EdgeValue Symbol Guard) =>
    EdgeResident after.heap edge ∧ Edge annotation depth edge ∧
      (∀ child ∈ edge.children, FreeLE (sourceWeight annotation source) (pairRank annotation left right) child ∧
        FreeBelow (sourceWeight annotation source) (pairRank annotation left right) child) ∧ EdgeScope domain.key.seen edge
  have walked := certified_walk annotation source
    (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
    (pairs (nodeEdges left) (nodeEdges right)) input output
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth edge known; exact ⟨edge_stable before after growth edge known.1, known.2⟩)
    (by
      intro pair member current _currentContext known
      have inside := (pairs_member _ _ pair).mp member
      have bounds := SourceCurrentConstrainedCapNativeOccurrenceCompile.row_budget annotation domain left right pair.1 pair.2 inside.1 inside.2.1
      intro result after _ _ resident law
      have returned := law depth bindings known.2.2 known.1 known.2.1
      refine ⟨resident, returned.1, ?_, returned.2.2⟩
      intro child childMember
      have free := returned.2.1 child childMember
      refine ⟨fun name named => Nat.le_trans (free name named) bounds.1, ?_⟩
      intro name named
      rcases bounds.2 with smaller | zero
      · exact .inl (Nat.lt_of_le_of_lt (free name named) smaller)
      · exact .inr zero)
    state context (by
      intro pair member
      have inside := (pairs_member _ _ pair).mp member
      exact ⟨SourceCurrentConstrainedCap.node_edge leftCap pair.1 inside.1,
        SourceCurrentConstrainedCap.node_edge rightCap pair.2 inside.2.1,
        SourceCurrentConstrainedCapOriginalSupport.rows_input source facts domain left right inputs
          pair.1 pair.2 inside.1 inside.2.1⟩)
  unfold compileRows
  apply certified_bind annotation source _ _ state context _ _ walked
  intro values after _ afterContext returned
  exact node_work annotation source depth (pairRank annotation left right) domain values after afterContext
    (fun edge member => (returned edge member).1) (fun edge member => (returned edge member).2.1)
    (fun edge member => (returned edge member).2.2.1) (fun edge member => (returned edge member).2.2.2)

private theorem left_union_certified (depth : Nat) (domain : Interned DomainKey) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (level free) (right : Value Symbol Guard) (facts : Facts source)
    (bindings : OriginalBindings annotation source domain.key)
    (inputs : NodeInputs source ⟨domain, .union entry members level free, right⟩)
    (leftCap : Cap annotation depth (.union entry members level free)) (rightCap : Cap annotation depth right)
    (state : Machine Symbol Guard) (context : Context annotation source state) :
    Certified annotation source
      ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain member right) members).bind
        fun values => .work (makeUnion values) .pure) state
      (Post annotation source depth ⟨domain, .union entry members level free, right⟩) := by
  let output := fun (after : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Available after.heap value ∧ Cap annotation depth value ∧
      Classified (sourceWeight annotation source) (pairRank annotation (.union entry members level free) right) value ∧ Scope domain.key.seen value
  have walked := certified_walk annotation source
    (fun member => requestNode domain member right) members
    (fun _ value => Cap annotation depth value ∧ NodeInputs source ⟨domain, value, right⟩) output
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth value known; exact ⟨growth.available value known.1, known.2⟩)
    (by
      intro member inside current currentContext known
      apply certified_bind annotation source _ _ current currentContext _ _
        (request_node annotation source depth ⟨domain, member, right⟩ current bindings known.2 known.1 rightCap)
      intro result after _ afterContext returned
      exact ⟨returned.1, returned.2.1, SourceCurrentConstrainedCapNativeOccurrenceCode.classified_mono _ _ _ result
        after.heap afterContext.valid.1 returned.1 returned.2.2.1
        (SourceCurrentConstrainedCapNonplainRank.left_union_pair_le annotation entry members level free member inside right), returned.2.2.2⟩)
    state context (by
      intro member inside
      have original := SourceCurrentConstrainedCapOriginalSupport.union_member source entry members level free inputs.1 inputs.2.2.1 member inside
      have covered := SourceCurrentConstrainedCapNativeIdentity.Covered.union_member source facts domain.key
        entry members level free inputs.2.2.1 inputs.2.2.2.2.1 member inside
      exact ⟨SourceCurrentConstrainedCap.union_member leftCap member inside,
        original.1, inputs.2.1, original.2, inputs.2.2.2.1, covered, inputs.2.2.2.2.2⟩)
  apply certified_bind annotation source _ _ state context _ _ walked
  intro values after _ afterContext returned
  exact union_work annotation source depth (pairRank annotation (.union entry members level free) right) domain
    values after afterContext (fun value member => (returned value member).1)
    (fun value member => (returned value member).2.1) (fun value member => (returned value member).2.2.1)
    (fun value member => (returned value member).2.2.2)

private theorem right_union_certified (depth : Nat) (domain : Interned DomainKey) (left : Value Symbol Guard)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (level free) (facts : Facts source)
    (bindings : OriginalBindings annotation source domain.key)
    (inputs : NodeInputs source ⟨domain, left, .union entry members level free⟩)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth (.union entry members level free))
    (state : Machine Symbol Guard) (context : Context annotation source state) :
    Certified annotation source
      ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain left member) members).bind
        fun values => .work (makeUnion values) .pure) state
      (Post annotation source depth ⟨domain, left, .union entry members level free⟩) := by
  let output := fun (after : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Available after.heap value ∧ Cap annotation depth value ∧
      Classified (sourceWeight annotation source) (pairRank annotation left (.union entry members level free)) value ∧ Scope domain.key.seen value
  have walked := certified_walk annotation source
    (fun member => requestNode domain left member) members
    (fun _ value => Cap annotation depth value ∧ NodeInputs source ⟨domain, left, value⟩) output
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth value known; exact ⟨growth.available value known.1, known.2⟩)
    (by
      intro member inside current currentContext known
      apply certified_bind annotation source _ _ current currentContext _ _
        (request_node annotation source depth ⟨domain, left, member⟩ current bindings known.2 leftCap known.1)
      intro result after _ afterContext returned
      exact ⟨returned.1, returned.2.1, SourceCurrentConstrainedCapNativeOccurrenceCode.classified_mono _ _ _ result
        after.heap afterContext.valid.1 returned.1 returned.2.2.1
        (SourceCurrentConstrainedCapNonplainRank.right_union_pair_le annotation left entry members level free member inside), returned.2.2.2⟩)
    state context (by
      intro member inside
      have original := SourceCurrentConstrainedCapOriginalSupport.union_member source entry members level free inputs.2.1 inputs.2.2.2.1 member inside
      have covered := SourceCurrentConstrainedCapNativeIdentity.Covered.union_member source facts domain.key
        entry members level free inputs.2.2.2.1 inputs.2.2.2.2.2 member inside
      exact ⟨SourceCurrentConstrainedCap.union_member rightCap member inside,
        inputs.1, original.1, inputs.2.2.1, original.2, inputs.2.2.2.2.1, covered⟩)
  apply certified_bind annotation source _ _ state context _ _ walked
  intro values after _ afterContext returned
  exact union_work annotation source depth (pairRank annotation left (.union entry members level free)) domain
    values after afterContext (fun value member => (returned value member).1)
    (fun value member => (returned value member).2.1) (fun value member => (returned value member).2.2.1)
    (fun value member => (returned value member).2.2.2)

private theorem mu_certified (depth : Nat) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (facts : Facts source) (state : Machine Symbol Guard)
    (context : Context annotation source state) (bindings : OriginalBindings annotation source domain.key)
    (inputs : NodeInputs source ⟨domain, left, right⟩) (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right) :
    Certified annotation source (compileMu domain left right) state (Post annotation source depth ⟨domain, left, right⟩) := by
  cases first : identity left <;> cases second : identity right <;> simp only [compileMu, first, second]
  all_goals try trivial
  rename_i firstId secondId
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right firstId secondId
  intro _enteredGrowth _enteredContext
  have enteredBindings := SourceCurrentConstrainedCapOriginalSupport.enter annotation depth source domain bindings left right inputs
    leftCap rightCap state.domains context.valid.2 firstId secondId
  have key : actual.1.key = SourceRecursiveIntersectionDomain.extend domain.key
      ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair firstId secondId) :=
    SourceRecursiveIntersectionSchedule.entered_key state.domains context.valid.2 domain.key left right firstId secondId
  have leftBody := SourceCurrentConstrainedCapOriginalSupport.body_input source left inputs.1 inputs.2.2.1
  have rightBody := SourceCurrentConstrainedCapOriginalSupport.body_input source right inputs.2.1 inputs.2.2.2.1
  have bodyInputs : NodeInputs source ⟨actual.1, body left, body right⟩ := by
    refine ⟨leftBody.1, rightBody.1, leftBody.2, rightBody.2, ?_, ?_⟩
    · rw [key]
      exact SourceCurrentConstrainedCapNativeCoverage.left_body_covered domain.key left right inputs.2.2.2.2.1 _
    · rw [key]
      exact SourceCurrentConstrainedCapNativeCoverage.right_body_covered domain.key left right inputs.2.2.2.2.2 _
  have leftBound := SourceCurrentConstrainedCapNativeScope.body_cap annotation depth left leftCap
  have rightBound := SourceCurrentConstrainedCapNativeScope.body_cap annotation depth right rightCap
  have bodyRank : pairRank annotation (body left) (body right) = pairRank annotation left right := by
    simp only [pairRank, SourceCurrentConstrainedCapKernelJoint.body_rank annotation depth left leftCap,
      SourceCurrentConstrainedCapKernelJoint.body_rank annotation depth right rightCap]
  have oldWeight := SourceCurrentConstrainedCapNativePairWeight.pair_weight annotation source facts domain.key bindings.annotated
    left right inputs.2.2.1 inputs.2.2.2.1 inputs.2.2.2.2.1 inputs.2.2.2.2.2 firstId secondId first second
  intro value middle _childGrowth middleContext available law
  have returned := law depth enteredBindings bodyInputs leftBound rightBound
  have bodyScope : Scope (pair firstId secondId :: domain.key.seen) value := by
    apply SourceRecursiveIntersectionResultScope.weaken actual.1.key.seen _ ?_ value returned.2.2
    intro next member
    rw [key] at member
    rcases (SourceRecursiveIntersectionDomain.extend_seen _ _ _ next).mp member with same | old
    · exact List.mem_cons.mpr (.inl same)
    · exact List.mem_cons.mpr (.inr old)
  have fresh := SourceCurrentConstrainedCapNativeProbeSupport.of_scope _ value bodyScope
  have classified : Classified (sourceWeight annotation source) (pairRank annotation left right) value := by
    simpa only [bodyRank] using returned.2.1
  intro result after completed _ _
  cases outcome : SourceRecursiveIntersectionMaybeMu.maybeMu (pair firstId secondId) value middle.heap with
  | pending key heap => simp only [construction, outcome] at completed; cases completed
  | done result heap =>
      simp only [construction, outcome] at completed
      cases completed
      have selected : Cap annotation depth result ∧
          Classified (sourceWeight annotation source) (pairRank annotation left right) result ∧
          SourceCurrentConstrainedCapGuardHeap.Heap annotation heap ∧
          SourceCurrentHereditaryConstruction.MuStored annotation heap ∧ Available heap result ∧
          SourceRecursiveIntersectionSemanticHeap.SemanticHeap heap ∧ Grows middle.heap heap ∧
          Extends middle.heap.nodes.issued heap.nodes.issued ∧ SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree result := by
        by_cases zero : pairRank annotation left right = 0
        · have leftZero : rank annotation left = 0 := by unfold pairRank at zero; omega
          have rightZero : rank annotation right = 0 := by unfold pairRank at zero; omega
          have leftPlain := (SourceCurrentConstrainedCapNonplainRank.rank_zero_iff annotation left).mp leftZero
          have rightPlain := (SourceCurrentConstrainedCapNonplainRank.rank_zero_iff annotation right).mp rightZero
          have zeroLaw := law 0 enteredBindings bodyInputs
            (SourceCurrentConstrainedCapNativeScope.body_cap annotation 0 left (.plain 0 leftPlain))
            (SourceCurrentConstrainedCapNativeScope.body_cap annotation 0 right (.plain 0 rightPlain))
          have plain := zeroLaw.1.annotated rfl
          have selected := SourceCurrentConstrainedCapNativeBinderReturn.zero annotation depth _ value middle.heap middleContext.semantic
            available plain middleContext.guards (sourceWeight annotation source) (by simpa only [zero] using classified)
            fresh result heap outcome
          simpa only [zero] using selected
        · exact SourceCurrentConstrainedCapNativeBinderReturn.positive annotation depth _ value middle.heap middleContext.semantic
            available returned.1 middleContext.guards (sourceWeight annotation source) _ (by omega) oldWeight classified fresh result heap outcome
      exact ⟨selected.2.2.2.2.1, selected.1, selected.2.1,
        SourceRecursiveIntersectionResultScope.optionalBinder domain.key.seen (pair firstId secondId)
          value middle.heap middleContext.semantic.1 available bodyScope result heap outcome⟩

private theorem reference_certified (depth : Nat) (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (context : Context annotation source state)
    (bindings : OriginalBindings annotation source domain.key)
    (original : SourceRecursiveIntersectionInputView.Original other) (available : Available source other)
    (covered : SourceCurrentConstrainedCapNativeIdentity.Covered domain.key other) (bounded : Cap annotation depth other) :
    Certified annotation source (compileReference domain name other left) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) (rank annotation other) value ∧ Scope domain.key.seen value) := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨bound, found, resident, _current, _reference, annotated, boundCovered, boundOriginal⟩ :=
      SourceCurrentConstrainedCapOriginalSupport.read annotation source state.heap context.valid.1 context.growth context.history
        domain.key bindings name member
    simp only [compileReference, member, ite_true, Certified, found]
    cases left with
    | false =>
        simpa only [Bool.false_eq_true, ↓reduceIte, Post, pairRank,
          SourceCurrentConstrainedCapNonplainRank.rank_zero annotation bound annotated, Nat.add_zero] using
          request_node annotation source depth ⟨domain, other, bound⟩ state bindings
            ⟨original, boundOriginal, available, resident, covered, boundCovered⟩ bounded (.plain depth annotated)
    | true =>
        simpa only [↓reduceIte, Post, pairRank,
          SourceCurrentConstrainedCapNonplainRank.rank_zero annotation bound annotated, Nat.zero_add] using
          request_node annotation source depth ⟨domain, bound, other⟩ state bindings
            ⟨boundOriginal, original, resident, available, boundCovered, covered⟩ (.plain depth annotated) bounded
  · simp only [compileReference, member, ite_false]
    trivial

/-- Every selected node branch derives its cap, occurrence classifier and scope from its actual smaller requests. -/
theorem node_certified [DecidableEq Symbol] (facts : Facts source) (request : NodeRequest Symbol Guard)
    (depth : Nat) (state : Machine Symbol Guard) (context : Context annotation source state)
    (_known : Domain state request.domain) (bindings : OriginalBindings annotation source request.domain.key)
    (inputs : NodeInputs source request) (leftCap : Cap annotation depth request.left) (rightCap : Cap annotation depth request.right) :
    Certified annotation source (compileNode request) state (Post annotation source depth request) := by
  rcases request with ⟨domain, left, right⟩
  cases selected : decision domain.key left right with
  | empty =>
      simp only [compileNode, selected]
      exact ⟨empty_available state.heap, .plain depth .empty,
        SourceCurrentConstrainedCapPairOccurrences.empty _ _, SourceRecursiveIntersectionResultScope.closed _ _ rfl⟩
  | reset =>
      simp only [compileNode, selected]
      have resetInputs := SourceCurrentConstrainedCapKernelJointDecision.reset_inputs source domain left right inputs selected
      apply certified_mono annotation source _ state _ _
        (request_node annotation source depth ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ state
          (SourceCurrentConstrainedCapOriginalSupport.empty annotation source) resetInputs leftCap rightCap)
      intro after value returned
      exact ⟨returned.1, returned.2.1, returned.2.2.1,
        SourceRecursiveIntersectionResultScope.weaken [] domain.key.seen (by intro pair member; cases member) value returned.2.2.2⟩
  | self =>
      simp only [compileNode, selected]
      exact ⟨inputs.2.2.1.grows source state.heap context.growth context.history, leftCap,
        SourceCurrentConstrainedCapOriginalSupport.classified annotation source facts left inputs.1 inputs.2.2.1 _,
        SourceRecursiveIntersectionResultScope.closed _ _ (SourceRecursiveIntersectionResultScope.self_closed _ _ _ selected)⟩
  | swap =>
      simp only [compileNode, selected]
      simpa only [Post, pairRank, Nat.add_comm] using
        request_node annotation source depth ⟨domain, right, left⟩ state bindings
          ⟨inputs.2.1, inputs.1, inputs.2.2.2.1, inputs.2.2.1, inputs.2.2.2.2.2, inputs.2.2.2.2.1⟩ rightCap leftCap
  | repeated key =>
      simp only [compileNode, selected]
      have weight := SourceCurrentConstrainedCapKernelJointDecision.repeated_weight annotation source facts domain left right bindings inputs key selected
      exact ⟨reference_available state.heap _ (by intro name member; simp [Value.free] at member),
        .plain depth (.reference _), SourceCurrentConstrainedCapPairOccurrences.reference _ _ _ (by rw [weight]; exact Nat.le_refl _),
        SourceRecursiveIntersectionResultScope.repeated domain.key.seen key
          (SourceRecursiveIntersectionResultScope.repeated_seen _ _ _ key selected)⟩
  | bothMu | leftMu | rightMu =>
      simp only [compileNode, selected]
      exact mu_certified annotation source depth domain left right facts state context bindings inputs leftCap rightCap
  | leftUnion =>
      simp only [compileNode, selected]
      cases left with
      | empty | reference | node | mu => trivial
      | union entry members level free =>
          exact left_union_certified annotation source depth domain entry members level free right facts bindings inputs leftCap rightCap state context
  | rightUnion =>
      simp only [compileNode, selected]
      cases right with
      | empty | reference | node | mu => trivial
      | union entry members level free =>
          exact right_union_certified annotation source depth domain left entry members level free facts bindings inputs leftCap rightCap state context
  | leftReference =>
      simp only [compileNode, selected]
      cases left with
      | empty | node | union | mu => trivial
      | reference name =>
          cases name <;> try trivial
          rename_i name
          simpa only [Post, pairRank, SourceCurrentConstrainedCapNonplainRank.reference_zero, Nat.zero_add] using
            reference_certified annotation source depth domain name right true state context bindings
              inputs.2.1 inputs.2.2.2.1 inputs.2.2.2.2.2 rightCap
  | rightReference =>
      simp only [compileNode, selected]
      cases right with
      | empty | node | union | mu => trivial
      | reference name =>
          cases name <;> try trivial
          rename_i name
          simpa only [Post, pairRank, SourceCurrentConstrainedCapNonplainRank.reference_zero, Nat.add_zero] using
            reference_certified annotation source depth domain name left false state context bindings
              inputs.1 inputs.2.2.1 inputs.2.2.2.2.1 leftCap
  | ordinary =>
      simp only [compileNode, selected]
      cases left <;> cases right <;> try trivial
      rename_i first firstRows firstDepth firstFree second secondRows secondDepth secondFree
      exact rows_certified annotation source depth domain (.node first firstRows firstDepth firstFree)
        (.node second secondRows secondDepth secondFree) facts bindings inputs leftCap rightCap state context
  | unsupported =>
      simp only [compileNode, selected]
      trivial

/-- The same literal compiled node supplies its complete conditional law at every supported depth. -/
theorem node_law_certified [DecidableEq Symbol] (facts : Facts source) (request : NodeRequest Symbol Guard)
    (state : Machine Symbol Guard) (context : Context annotation source state) (known : Domain state request.domain) :
    Certified annotation source (compileNode request) state (fun _ value => NodeLaw annotation source request value) := by
  apply certified_forall annotation source _ state _ (compileNode_bodyCode request)
  intro depth
  apply certified_forall annotation source _ state _ (compileNode_bodyCode request)
  intro bindings
  apply certified_forall annotation source _ state _ (compileNode_bodyCode request)
  intro inputs
  apply certified_forall annotation source _ state _ (compileNode_bodyCode request)
  intro leftCap
  apply certified_forall annotation source _ state _ (compileNode_bodyCode request)
  intro rightCap
  apply certified_mono annotation source _ state _ _
    (node_certified annotation source facts request depth state context known bindings inputs leftCap rightCap)
  intro after value returned
  exact returned.2

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointCompile
