import MicroCFTA.SourceRecursiveIntersectionCompileNodeBounds
import MicroCFTA.SourceRecursiveIntersectionCompileSafety
import MicroCFTA.SourceCurrentAllocatedNativeRequestBounds
import MicroCFTA.SourceCurrentAllocatedNativeFieldClosure

/-!
# Physical input certificates for actual checked source code

The original code safety and request bounds are structural certificates.
They do not require the old eager interpreter. This module derives current
physical operands for the same node code and actual checked edge prefixes.
It does not assume recursive completion or install semantic finish receipts.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCodeProgress
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Physical checks follow exact effects. Recursive continuations require only resident returned values. -/
def Operands [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard A) (state : Machine Symbol Guard) : Prop :=
  match code with
  | .pure _ | .fail _ => True
  | .work job next =>
      WorkInputs state.heap job ∧ ∀ value after, work job state = .done value after → Operands (next value) after
  | .enter domain left right first second next =>
      Domain state domain ∧ Available state.heap left ∧ Available state.heap right ∧
        let entered := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
        Operands (next entered.1) {state with domains := entered.2}
  | .read name next => Operands (next (SourcePreparedSharedRows.read state.heap name)) state
  | .optionalBinder key body next =>
      Available state.heap body ∧ ∀ value after,
        construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after →
          Operands (next value) after
  | .node request next => NodeReady state request ∧ ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        Available after.heap value → Operands (next value) after
  | .edge request next => EdgeReady state request ∧ ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        EdgeResident after.heap value → Operands (next value) after
  | .finishNode .. | .finishEdge .. => False

private theorem operands_bind [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (intermediate : Machine Symbol Guard → A → Prop) (safe : Safe code state intermediate)
    (operands : Operands code state)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      intermediate after value → Operands (next value) after) : Operands (code.bind next) state := by
  induction code generalizing state with
  | pure value => exact continuation value state valid (.refl state) safe
  | fail failure => trivial
  | work job resume ih | optionalBinder key body resume ih =>
      refine ⟨operands.1, ?_⟩
      intro value after done
      have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [done, Result.state] using safe.1
      have growth : Extension state after := by simpa only [done, Result.state] using safe.2.1
      exact ih value after afterValid (safe.2.2 value after done) (operands.2 value after done)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | enter domain left right first second resume ih =>
      refine ⟨operands.1, operands.2.1, operands.2.2.1, ?_⟩
      exact ih _ _ safe.1 safe.2.2 operands.2.2.2
        (fun result final finalValid later property => continuation result final finalValid (safe.2.1.trans later) property)
  | read name resume ih => exact ih _ state valid safe operands continuation
  | node request resume ih | edge request resume ih =>
      refine ⟨operands.1, ?_⟩
      intro value after afterValid growth available
      exact ih value after afterValid (safe.2 value after afterValid growth available)
        (operands.2 value after afterValid growth available)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | finishNode | finishEdge => cases safe

private theorem operands_walk [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (safeCalls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state →
      input state request → Safe (call request) state output)
    (operandCalls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state →
      input state request → Operands (call request) state)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (inputs : ∀ request ∈ requests, input state request) : Operands (walk call requests) state := by
  induction requests generalizing state with
  | nil => trivial
  | cons first rest ih =>
      apply operands_bind _ _ state valid output
        (safeCalls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
        (operandCalls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
      intro value after afterValid growth available
      have tailInputs := fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member))
      have tailSafe := safe_walk call rest input output inputStable outputStable
        (fun request member => safeCalls request (List.mem_cons_of_mem _ member)) after afterValid tailInputs
      have tailOperands := ih (fun request member => safeCalls request (List.mem_cons_of_mem _ member))
        (fun request member => operandCalls request (List.mem_cons_of_mem _ member)) after afterValid tailInputs
      exact operands_bind _ _ after afterValid _ tailSafe tailOperands (fun _ _ _ _ _ => trivial)

private theorem operands_requestNode [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (ready : NodeReady state ⟨domain, left, right⟩) : Operands (requestNode domain left right) state :=
  ⟨ready, fun _ _ _ _ _ => trivial⟩

private theorem operands_requestEdge [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (ready : EdgeReady state ⟨domain, left, right⟩) : Operands (requestEdge domain left right) state :=
  ⟨ready, fun _ _ _ _ _ => trivial⟩

private theorem operands_edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (available : ∀ value ∈ values, Available state.heap value) :
    Operands (.work (makeEdge symbol guard values) .pure) state :=
  ⟨.edge symbol guard values available, fun _ _ _ => trivial⟩

private theorem operands_node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (resident : ∀ edge ∈ edges, EdgeResident state.heap edge) :
    Operands (.work (makeNode edges) .pure) state := ⟨.node edges resident, fun _ _ _ => trivial⟩

private theorem operands_union [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (available : ∀ value ∈ values, Available state.heap value) :
    Operands (.work (makeUnion values) .pure) state := ⟨.union values available, fun _ _ _ => trivial⟩

private theorem operands_optionalBinder [DecidableEq (EdgeKey Symbol Guard)]
    (key : Nat × Nat) (body : Value Symbol Guard) (state : Machine Symbol Guard)
    (available : Available state.heap body) : Operands (.optionalBinder key body .pure) state :=
  ⟨available, fun _ _ _ => trivial⟩

private theorem compileMu_operands [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) :
    Operands (compileMu domain left right) state := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;> simp only [compileMu, first, second]
  all_goals try trivial
  rename_i firstId secondId
  obtain ⟨afterValid, growth, afterDomain⟩ := entered state valid domain known left right leftAvailable rightAvailable firstId secondId
  refine ⟨known, leftAvailable, rightAvailable,
    ⟨afterDomain, body_available _ left leftAvailable, body_available _ right rightAvailable⟩, ?_⟩
  intro value final finalValid later available
  exact operands_optionalBinder _ value final available

private theorem compileReference_operands [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) :
    Operands (compileReference domain name other left) state := by
  by_cases bound : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name bound
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ stored entry.identity rfl
    simp only [compileReference, bound, ite_true, Operands, read]
    cases left
    · exact operands_requestNode domain other (.mu entry body depth ordinary) state ⟨known, available, stored⟩
    · exact operands_requestNode domain (.mu entry body depth ordinary) other state ⟨known, stored, available⟩
  · simp only [compileReference, bound, ite_false, Operands]


private theorem compileRows_operands [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge)
    (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge) :
    Operands (compileRows domain left right) state := by
  let input := fun (current : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain current domain ∧ EdgeResident current.heap pair.1 ∧ EdgeResident current.heap pair.2
  have stable : Stable input := by
    intro before after growth pair known
    exact ⟨known.1.grows _ growth, edge_grows _ _ growth.heap _ known.2.1, edge_grows _ _ growth.heap _ known.2.2⟩
  have rows := safe_walk (fun pair => requestEdge domain pair.1 pair.2) (pairs left right) input _ stable edge_stable
    (fun pair _ current currentValid known => safe_requestEdge domain pair.1 pair.2 current known)
    state valid (by
      intro pair member
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
      exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩)
  have rowsOperands := operands_walk (fun pair => requestEdge domain pair.1 pair.2) (pairs left right) input _ stable edge_stable
    (fun pair _ current currentValid known => safe_requestEdge domain pair.1 pair.2 current known)
    (fun pair _ current currentValid known => operands_requestEdge domain pair.1 pair.2 current known)
    state valid (by
      intro pair member
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
      exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩)
  apply operands_bind _ _ state valid _ rows rowsOperands
  intro values after afterValid growth resident
  exact operands_node values after resident

/-- Ordered compiled union requests retain available members before source union construction. -/
private theorem union_operands [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value) :
    Operands ((walk (fun member => if left then requestNode domain member other else requestNode domain other member) members).bind
      fun values => .work (makeUnion values) .pure) state := by
  let input := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap other ∧ Available current.heap value
  have stable : Stable input := by
    intro before after growth value known
    exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have requests := safe_walk (fun member => if left then requestNode domain member other else requestNode domain other member)
    members input _ stable available_stable (by
      intro member present current currentValid known
      cases left
      · exact safe_requestNode domain other member current ⟨known.1, known.2.1, known.2.2⟩
      · exact safe_requestNode domain member other current ⟨known.1, known.2.2, known.2.1⟩)
    state valid (fun member present => ⟨known, available, membersAvailable member present⟩)
  have requestsOperands := operands_walk (fun member => if left then requestNode domain member other else requestNode domain other member)
    members input _ stable available_stable (by
      intro member present current currentValid known
      cases left
      · exact safe_requestNode domain other member current ⟨known.1, known.2.1, known.2.2⟩
      · exact safe_requestNode domain member other current ⟨known.1, known.2.2, known.2.1⟩)
    (by
      intro member present current currentValid known
      cases left
      · exact operands_requestNode domain other member current ⟨known.1, known.2.1, known.2.2⟩
      · exact operands_requestNode domain member other current ⟨known.1, known.2.2, known.2.1⟩)
    state valid (fun member present => ⟨known, available, membersAvailable member present⟩)
  apply operands_bind _ _ state valid _ requests requestsOperands
  intro values after afterValid growth present
  exact operands_union values after present

/-- Every actual compiled node body derives its current physical operand checks. -/
theorem compileNode_operands [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (request : NodeRequest Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request) :
    Operands (compileNode request) state := by
  cases request with
  | mk domain left right =>
    obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
    cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
    | empty => simp only [compileNode, selected, Operands]
    | reset =>
      simp only [compileNode, selected]
      exact operands_requestNode IntersectionEmptyDomain.emptyDomain left right state ⟨empty_domain state, leftAvailable, rightAvailable⟩
    | self => simp only [compileNode, selected, Operands]
    | swap =>
      simp only [compileNode, selected]
      exact operands_requestNode domain right left state ⟨known, rightAvailable, leftAvailable⟩
    | repeated key => simp only [compileNode, selected, Operands]
    | bothMu | leftMu | rightMu => simpa only [compileNode, selected] using compileMu_operands domain left right state valid known leftAvailable rightAvailable
    | leftUnion =>
      simp only [compileNode, selected]
      cases left with
      | union entry members depth free =>
        exact union_operands domain members right true state valid known rightAvailable
          (fun value member => leftAvailable.children value (by simpa only [children] using member))
      | empty | reference | node | mu => trivial
    | rightUnion =>
      simp only [compileNode, selected]
      cases right with
      | union entry members depth free =>
        exact union_operands domain members left false state valid known leftAvailable
          (fun value member => rightAvailable.children value (by simpa only [children] using member))
      | empty | reference | node | mu => trivial
    | leftReference =>
      simp only [compileNode, selected]
      cases left <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_operands _ _ _ _ state valid known rightAvailable | trivial
    | rightReference =>
      simp only [compileNode, selected]
      cases right <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_operands _ _ _ _ state valid known leftAvailable | trivial
    | ordinary =>
      simp only [compileNode, selected]
      cases left <;> cases right <;> try trivial
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      exact compileRows_operands domain firstEdges secondEdges state valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
    | unsupported => simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, Operands]

/-- Actual accepted code derives ordered child operands and its final physical edge construction. -/
theorem children_certified [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ready : EdgeReady state request) :
    Safe (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)
      state (fun after value => EdgeResident after.heap value) ∧
    Operands (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state := by
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  have stable : Stable input := by
    intro before after growth pair known
    exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have inputs : ∀ pair ∈ request.left.children.zip request.right.children, input state pair := by
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 inside.1,
      valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 inside.2⟩
  have safeCalls : ∀ pair ∈ request.left.children.zip request.right.children, ∀ current,
      SourceRecursiveIntersectionKernel.Valid current → input current pair →
        Safe (requestNode request.domain pair.1 pair.2) current (fun after value => Available after.heap value) := by
    intro pair _ current _ known
    exact safe_requestNode request.domain pair.1 pair.2 current known
  have childSafe := safe_walk (fun pair => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) input _ stable available_stable safeCalls state valid inputs
  have childOperands := operands_walk (fun pair => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) input _ stable available_stable safeCalls
    (fun pair _ current _ known => operands_requestNode request.domain pair.1 pair.2 current known) state valid inputs
  constructor
  · apply safe_bind _ _ state valid _ _ childSafe
    intro values after afterValid growth available
    exact safe_work _ after afterValid EdgeResident
      (InternedNestedFacts.edge_verified _ _ values after.heap afterValid.1 available)
  · apply operands_bind _ _ state valid _ childSafe childOperands
    intro values after afterValid growth available
    exact operands_edge _ _ values after available

/-- The source sentinel has a physical constructor check and no recursive operand. -/
theorem sentinel_certified [DecidableEq (EdgeKey Symbol Guard)]
    (left : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Safe (SourceEqualityNativeCheckedCode.sentinel left) state (fun after value => EdgeResident after.heap value) ∧
      Operands (SourceEqualityNativeCheckedCode.sentinel left) state := by
  have available : ∀ value ∈ ([.empty] : List (Value Symbol Guard)), Available state.heap value := by
    intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact empty_available state.heap
  exact ⟨safe_work _ state valid EdgeResident
    (InternedNestedFacts.edge_verified _ _ [.empty] state.heap valid.1 available),
    operands_edge _ _ [.empty] state available⟩

/-- Every actual checked body yield derives safety and operands for the emitted branch only. -/
theorem body_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before =
      .yielded (.code code) after) :
    Safe code after.native.machine (fun final value => EdgeResident final.heap value) ∧
      Operands code after.native.machine := by
  have same : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request .pure before
  rw [same]
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact sentinel_certified _ _ valid
  · split at yielded
    · cases yielded
    · cases yielded
    · split at yielded
      · cases yielded
      · cases yielded
      · dsimp only at yielded
        split at yielded
        · cases yielded
        · simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
          cases yielded
          exact sentinel_certified _ _ valid
        · simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
          cases yielded
          exact sentinel_certified _ _ valid
        · simp only [SourceEqualityNativeDemand.code_bind_pure] at yielded
          cases yielded
          exact children_certified request _ _ valid ready

/-- Loaded resident fields derive a checked body prefix with actual allocation and strict request bounds. -/
theorem body_prefix [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard)
    (scope : EdgeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (before : Checked width) (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (ready : EdgeReady before.native.machine request)
    (operations : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (heap : SourceCurrentConjunctionEquality.Fields before.operations before.native.machine.heap) :
    ∃ code after, SourceEqualityNativeDemand.body request .pure before =
        .yielded (.code code) {before with operations := after} ∧
      SourceEqualityConstraintMemoAllocation.Valid after ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after ∧
      SourceCurrentConjunctionEquality.Fields after before.native.machine.heap ∧
      SourceCurrentAllocatedNativeCodeFields.Fields after code ∧
      Safe code before.native.machine (fun final value => EdgeResident final.heap value) ∧
      Operands code before.native.machine ∧
      Below source holds
        (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete)
        code before.native.machine := by
  obtain ⟨code, after, yielded, afterValid, growth, retained, annotations⟩ :=
    SourceCurrentAllocatedNativeFieldClosure.body_complete request .pure before operations heap ready (fun _ => trivial)
  have certified := body_certified request before {before with operations := after} code valid ready yielded
  have bounded := SourceCurrentAllocatedNativeRequestBounds.body_below source facts holds request scope complete
    before code {before with operations := after} valid ready yielded
  exact ⟨code, after, yielded, afterValid, growth, retained, annotations,
    certified.1, certified.2, bounded⟩

/-- Original node inputs derive all three structural certificates without old native execution. -/
theorem node_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard)
    (scope : NodeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request))
    (before : Checked width) (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (ready : NodeReady before.native.machine request) (growth : Grows source before.native.machine.heap)
    (history : Extends source.nodes.issued before.native.machine.heap.nodes.issued) :
    Safe (compileNode request) before.native.machine (fun final value => Available final.heap value) ∧
      Operands (compileNode request) before.native.machine ∧
      Below source holds
        (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete)
        (compileNode request) before.native.machine ∧
      SourceCurrentAllocatedNativeCodeFields.Fields before.operations (compileNode request) :=
  ⟨compileNode_safe request before.native.machine valid ready,
    compileNode_operands request before.native.machine valid ready,
    compileNode_below source facts holds request scope complete before.native.machine valid ready growth history,
    SourceCurrentAllocatedNativeCodeFields.compileNode_fields before.operations request⟩

/-- Closed original roots derive their independent schedule bound and actual code certificates. -/
theorem initial_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (before : Checked width)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
    ∃ complete : Completes (view before.native.machine.heap holds)
        (SourceRecursiveIntersectionNative.nodeSemantic request),
      Safe (compileNode request) before.native.machine (fun final value => Available final.heap value) ∧
      Operands (compileNode request) before.native.machine ∧
      Below before.native.machine.heap holds
        (requiredFuel (view before.native.machine.heap holds)
          (SourceRecursiveIntersectionNative.nodeSemantic request) complete)
        (compileNode request) before.native.machine ∧
      SourceCurrentAllocatedNativeCodeFields.Fields before.operations (compileNode request) := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have complete : Completes (view before.native.machine.heap holds)
      (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete before.native.machine.heap valid.1 holds
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  exact ⟨complete, node_certified before.native.machine.heap valid.1 holds request
    (initial_scope before.native.machine.heap left right leftOriginal rightOriginal leftAvailable rightAvailable)
    complete before valid ⟨empty_domain _, leftAvailable, rightAvailable⟩ (grows_refl _) (extends_refl _)⟩

/-- Source operands derive the current primitive heap checks without a future input plan. -/
theorem current_heap_inputs [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard A) (state : Checked width) (operands : Operands code state.native.machine) :
    SourceEqualityNativeDemandHeap.Inputs (.code code) state := by
  cases code <;> first | exact operands.1 | trivial

/-- Original scoped operands turn conditional node word checks into the actual current input checks. -/
theorem current_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (code : Code Symbol Guard A) (state : Checked width)
    (operands : Operands code state.native.machine)
    (bounded : Below source holds bound code state.native.machine)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code code)) :
    SourceEqualityNativeDemandValidity.Inputs holds (.code code) state := by
  cases code with
  | pure | fail | read => trivial
  | work => exact operands.1
  | enter => exact ⟨operands.1, operands.2.1, operands.2.2.1⟩
  | optionalBinder => exact operands.1
  | edge => exact ⟨operands.1, words⟩
  | finishNode | finishEdge => cases operands
  | node request next =>
      have first := bounded.1.1.left.codec request.left
      have second := bounded.1.1.right.codec request.right
      have requested := IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain
        request.left.referenceOf request.right.referenceOf (inputOf request.left) (inputOf request.right) first second
      exact ⟨operands.1, words _ requested⟩

end MicroCFTA.SourceCurrentAllocatedNativeCodeProgress
