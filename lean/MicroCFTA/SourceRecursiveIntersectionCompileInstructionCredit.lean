import MicroCFTA.SourceRecursiveIntersectionInstructionCredit
import MicroCFTA.SourceRecursiveIntersectionCompileNodeBounds

/-!
# Initial instruction credit for complete node compiler dispatch

Original source requests retain independent semantic ranks. Each actual
branch reserves complete child-call credit in its literal execution order.
No completed native trace or future instruction count is an input.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCompileInstructionCredit
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionInstructionProfile (budget sourceBranching)
open SourceRecursiveIntersectionInstructionCredit (At NodeCharge EdgeCharge)
variable {Symbol Guard : Type}
variable [DecidableEq Symbol]
variable {source : State Symbol Guard} {holds : Guard → Language.Term Symbol → Bool} {limit rank : Nat}

/-- A strictly smaller original node request fits the preceding rank credit. -/
theorem node_charge (request : NodeRequest Symbol Guard) (bounded : NodeBelow source holds rank request) :
    NodeCharge source holds limit request (budget limit (rank - 1)) := by
  obtain ⟨scope, complete, smaller⟩ := bounded
  exact ⟨scope, complete, SourceRecursiveIntersectionInstructionProfile.budget_height_mono limit (by omega)⟩

/-- A strictly smaller original row request fits the preceding rank credit. -/
theorem edge_charge (request : EdgeRequest Symbol Guard) (bounded : EdgeBelow source holds rank request) :
    EdgeCharge source holds limit request (budget limit (rank - 1)) := by
  obtain ⟨scope, complete, smaller⟩ := bounded
  exact ⟨scope, complete, SourceRecursiveIntersectionInstructionProfile.budget_height_mono limit (by omega)⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The literal hash-join row walk pays every original row call and one final constructor. -/
theorem compileRows (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftResident : ∀ row ∈ left, EdgeResident state.heap row)
    (rightResident : ∀ row ∈ right, EdgeResident state.heap row)
    (bounds : ∀ rows ∈ pairs left right, EdgeBelow source holds rank ⟨domain, rows.1, rows.2⟩) :
    At source holds limit (SourceRecursiveIntersectionCode.compileRows domain left right) state
      ((pairs left right).length * budget limit (rank - 1) + 1) (fun after value => Available after.heap value) := by
  let input := fun (current : Machine Symbol Guard) (rows : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain current domain ∧ EdgeResident current.heap rows.1 ∧ EdgeResident current.heap rows.2
  have stable : Stable input := by
    intro before after growth rows ready
    exact ⟨ready.1.grows domain growth, edge_grows _ _ growth.heap _ ready.2.1,
      edge_grows _ _ growth.heap _ ready.2.2⟩
  have original : ∀ rows ∈ pairs left right, input state rows := by
    intro rows member
    have included := (pairs_member left right rows).mp member
    exact ⟨known, leftResident rows.1 included.1, rightResident rows.2 included.2.1⟩
  have walked := SourceRecursiveIntersectionInstructionCredit.walk
    (fun rows => requestEdge domain rows.1 rows.2) (pairs left right) (budget limit (rank - 1))
    input _ stable edge_stable (by
      intro rows member current _ ready
      exact SourceRecursiveIntersectionInstructionCredit.request_edge ⟨domain, rows.1, rows.2⟩ current _ ready (edge_charge _ (bounds rows member)))
    state valid original
  exact SourceRecursiveIntersectionInstructionCredit.bind _ _ state _ 1 valid _ _ walked
    (fun rows after afterValid _ outputs => SourceRecursiveIntersectionInstructionCredit.node rows after afterValid outputs.2)

/-- Each immutable union member pays one complete call before the final union constructor. -/
theorem compileUnion (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value)
    (bounds : ∀ member ∈ members, if left then NodeBelow source holds rank ⟨domain, member, other⟩
      else NodeBelow source holds rank ⟨domain, other, member⟩) :
    At source holds limit ((SourceRecursiveIntersectionCode.walk
      (fun member => if left then requestNode domain member other else requestNode domain other member) members).bind
        fun values => .work (makeUnion values) .pure) state
      (members.length * budget limit (rank - 1) + 1) (fun after value => Available after.heap value) := by
  let input := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap other ∧ Available current.heap value
  have stable : Stable input := by
    intro before after growth value ready
    exact ⟨ready.1.grows domain growth, growth.available _ ready.2.1, growth.available _ ready.2.2⟩
  have calls : ∀ member ∈ members, ∀ current, SourceRecursiveIntersectionKernel.Valid current → input current member →
      At source holds limit (if left then requestNode domain member other else requestNode domain other member)
        current (budget limit (rank - 1)) (fun after value => Available after.heap value) := by
    intro member present current _ ready
    have bounded := bounds member present
    cases left
    · exact SourceRecursiveIntersectionInstructionCredit.request_node ⟨domain, other, member⟩ current _
        ⟨ready.1, ready.2.1, ready.2.2⟩ (node_charge _ bounded)
    · exact SourceRecursiveIntersectionInstructionCredit.request_node ⟨domain, member, other⟩ current _
        ⟨ready.1, ready.2.2, ready.2.1⟩ (node_charge _ bounded)
  have walked := SourceRecursiveIntersectionInstructionCredit.walk
    (fun member => if left then requestNode domain member other else requestNode domain other member)
    members (budget limit (rank - 1)) input _ stable available_stable calls state valid
    (fun member present => ⟨known, available, membersAvailable member present⟩)
  exact SourceRecursiveIntersectionInstructionCredit.bind _ _ state _ 1 valid _ _ walked
    (fun values after afterValid _ outputs => SourceRecursiveIntersectionInstructionCredit.union values after afterValid outputs.2)

/-- Literal Mu entry pays its original body call and one actual optional-binder instruction. -/
theorem compileMu (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right)
    (bounded : SourceRecursiveIntersectionCode.Below source holds rank (SourceRecursiveIntersectionCode.compileMu domain left right) state) :
    At source holds limit (SourceRecursiveIntersectionCode.compileMu domain left right) state
      (budget limit (rank - 1) + 2) (fun after value => Available after.heap value) := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;>
    simp only [SourceRecursiveIntersectionCode.compileMu, first, second, SourceRecursiveIntersectionCode.unsupported, At] at bounded ⊢
  all_goals try trivial
  rename_i firstId secondId
  obtain ⟨_valid, _growth, enteredDomain⟩ :=
    entered state valid domain known left right leftAvailable rightAvailable firstId secondId
  refine ⟨budget limit (rank - 1) + 1, by omega, ?_⟩
  intro afterValid growth
  refine ⟨⟨enteredDomain, growth.available _ (body_available state.heap left leftAvailable),
    growth.available _ (body_available state.heap right rightAvailable)⟩,
    budget limit (rank - 1), 1, node_charge _ bounded.1, Nat.le_refl _, ?_⟩
  intro value after _ _ available
  exact ⟨available, 0, Nat.le_refl _, fun _ _ _ _ present => present⟩

/-- Actual binding readback pays one read and the original strictly smaller node call. -/
theorem compileReference (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other)
    (bounded : SourceRecursiveIntersectionCode.Below source holds rank (SourceRecursiveIntersectionCode.compileReference domain name other left) state) :
    At source holds limit (SourceRecursiveIntersectionCode.compileReference domain name other left) state
      (budget limit (rank - 1) + 1) (fun after value => Available after.heap value) := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name member
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ stored entry.identity rfl
    simp only [SourceRecursiveIntersectionCode.compileReference, member, ite_true, SourceRecursiveIntersectionCode.Below, read] at bounded
    simp only [SourceRecursiveIntersectionCode.compileReference, member, ite_true, At, read]
    refine ⟨budget limit (rank - 1), Nat.le_refl _, ?_⟩
    cases left
    · exact SourceRecursiveIntersectionInstructionCredit.request_node ⟨domain, other, .mu entry body depth ordinary⟩ state _
        ⟨known, available, stored⟩ (node_charge _ bounded.1)
    · exact SourceRecursiveIntersectionInstructionCredit.request_node ⟨domain, .mu entry body depth ordinary, other⟩ state _
        ⟨known, stored, available⟩ (node_charge _ bounded.1)
  · simp only [SourceRecursiveIntersectionCode.compileReference, member, ite_false, At]

private theorem body_room (limit rank : Nat) (positive : 1 ≤ limit) :
    budget limit (rank - 1) + 2 ≤ 2 + limit * budget limit (rank - 1) := by
  have enough := Nat.mul_le_mul_right (budget limit (rank - 1)) positive
  simp only [Nat.one_mul] at enough
  omega

/-- Every actual node branch derives body credit from its initial original semantic rank and source profile. -/
theorem compileNode (source : State Symbol Guard) (facts : Facts source) (holds : Guard → Language.Term Symbol → Bool)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    At source holds (sourceBranching source) (SourceRecursiveIntersectionCode.compileNode request) state
      (2 + sourceBranching source * budget (sourceBranching source)
        (requiredFuel (view source holds) (nodeSemantic request) complete - 1))
      (fun after value => Available after.heap value) := by
  let rank := requiredFuel (view source holds) (nodeSemantic request) complete
  let limit := sourceBranching source
  have positive : 1 ≤ limit := SourceRecursiveIntersectionInstructionProfile.sourceBranching_pos source
  have localRoom := body_room limit rank positive
  have bounded := SourceRecursiveIntersectionCode.compileNode_below source facts holds request scope complete state valid ready growth history
  cases request with
  | mk domain left right =>
    obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
    cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
    | empty => simpa only [SourceRecursiveIntersectionCode.compileNode, selected, At] using empty_available state.heap
    | self => simpa only [SourceRecursiveIntersectionCode.compileNode, selected, At] using leftAvailable
    | repeated key =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected, At]
      apply reference_available state.heap (.intersection key.1 key.2)
      intro name member
      simp [Value.free] at member
    | reset =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected] at bounded
      simp only [SourceRecursiveIntersectionCode.compileNode, selected]
      apply SourceRecursiveIntersectionInstructionCredit.mono _ _
        (SourceRecursiveIntersectionInstructionCredit.request_node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ state _
          ⟨empty_domain state, leftAvailable, rightAvailable⟩ (node_charge _ bounded.1))
      change budget limit (rank - 1) ≤ 2 + limit * budget limit (rank - 1)
      omega
    | swap =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected] at bounded
      simp only [SourceRecursiveIntersectionCode.compileNode, selected]
      apply SourceRecursiveIntersectionInstructionCredit.mono _ _
        (SourceRecursiveIntersectionInstructionCredit.request_node ⟨domain, right, left⟩ state _
          ⟨known, rightAvailable, leftAvailable⟩ (node_charge _ bounded.1))
      change budget limit (rank - 1) ≤ 2 + limit * budget limit (rank - 1)
      omega
    | bothMu | leftMu | rightMu =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected] at bounded ⊢
      exact SourceRecursiveIntersectionInstructionCredit.mono _ _
        (compileMu domain left right state valid known leftAvailable rightAvailable bounded) localRoom
    | leftUnion =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected]
      cases left with
      | union entry members depth free =>
        have width : members.length ≤ limit := by
          exact SourceRecursiveIntersectionInstructionProfile.left_members source facts ⟨domain, .union entry members depth free, right⟩ scope
        have calls := fun child member =>
          SourceRecursiveIntersectionCode.leftUnion_member_below source facts holds domain entry members depth free right scope complete selected child member
        have own := compileUnion (limit := limit) domain members right true state valid known rightAvailable
          (fun child member => leftAvailable.children child member) calls
        apply SourceRecursiveIntersectionInstructionCredit.mono _ _ own
        change members.length * budget limit (rank - 1) + 1 ≤ 2 + limit * budget limit (rank - 1)
        have enough := Nat.mul_le_mul_right (budget limit (rank - 1)) width
        omega
      | empty | reference | node | mu => trivial
    | rightUnion =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected]
      cases right with
      | union entry members depth free =>
        have width : members.length ≤ limit := by
          exact SourceRecursiveIntersectionInstructionProfile.right_members source facts ⟨domain, left, .union entry members depth free⟩ scope
        have calls := fun child member =>
          SourceRecursiveIntersectionCode.rightUnion_member_below source facts holds domain left entry members depth free scope complete selected child member
        have own := compileUnion (limit := limit) domain members left false state valid known leftAvailable
          (fun child member => rightAvailable.children child member) calls
        apply SourceRecursiveIntersectionInstructionCredit.mono _ _ own
        change members.length * budget limit (rank - 1) + 1 ≤ 2 + limit * budget limit (rank - 1)
        have enough := Nat.mul_le_mul_right (budget limit (rank - 1)) width
        omega
      | empty | reference | node | mu => trivial
    | leftReference =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected] at bounded ⊢
      cases left <;> try trivial
      rename_i name
      cases name <;> try trivial
      rename_i identity
      apply SourceRecursiveIntersectionInstructionCredit.mono _ _
        (compileReference domain identity right true state valid known rightAvailable bounded)
      change budget limit (rank - 1) + 1 ≤ 2 + limit * budget limit (rank - 1)
      omega
    | rightReference =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected] at bounded ⊢
      cases right <;> try trivial
      rename_i name
      cases name <;> try trivial
      rename_i identity
      apply SourceRecursiveIntersectionInstructionCredit.mono _ _
        (compileReference domain identity left false state valid known leftAvailable bounded)
      change budget limit (rank - 1) + 1 ≤ 2 + limit * budget limit (rank - 1)
      omega
    | ordinary =>
      simp only [SourceRecursiveIntersectionCode.compileNode, selected]
      cases left <;> cases right <;> try trivial
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      have width : (pairs firstEdges secondEdges).length ≤ limit :=
        SourceRecursiveIntersectionInstructionProfile.row_pairs source facts
          ⟨domain, .node first firstEdges firstDepth firstFree, .node second secondEdges secondDepth secondFree⟩ scope
      have own := compileRows (limit := limit) domain firstEdges secondEdges state valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
        (fun rows member => SourceRecursiveIntersectionCode.rows_member_below source facts holds domain
          first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree scope complete selected rows member)
      apply SourceRecursiveIntersectionInstructionCredit.mono _ _ own
      change (pairs firstEdges secondEdges).length * budget limit (rank - 1) + 1 ≤ 2 + limit * budget limit (rank - 1)
      have enough := Nat.mul_le_mul_right (budget limit (rank - 1)) width
      omega
    | unsupported => simp only [SourceRecursiveIntersectionCode.compileNode, selected, SourceRecursiveIntersectionCode.unsupported, At]

end MicroCFTA.SourceRecursiveIntersectionCompileInstructionCredit
