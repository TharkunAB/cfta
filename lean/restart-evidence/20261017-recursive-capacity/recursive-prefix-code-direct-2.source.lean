import MicroCFTA.SourceCurrentAllocatedNativeAdmissionNodeCertificates
import MicroCFTA.SourceCurrentAllocatedNativeAdmissionEdgeCertificates
import MicroCFTA.SourceRecursiveIntersectionSourceInventory

/-!
# Original request scope and finite domains in current compiled code

The certificate uses one fixed source heap for operands. Domains belong to
an explicit key inventory. Actual entry records the key passed to allocation.
Reads and primitive returns use their literal current machine. This local
compiler result does not assume word checks or recursive completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveDomainCode
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceRecursiveIntersectionInputView
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- The inventory contains empty and actual extensions of original operands. -/
structure Closed (source : InternedConstructorTemplates.State Symbol Guard) (inventory : List DomainKey) : Prop where
  empty : IntersectionEmptyDomain.emptyKey ∈ inventory
  extend : ∀ domain ∈ inventory, ∀ left right,
    Available source left → Available source right → ∀ first second,
    SourceRecursiveIntersectionControl.identity left = some first →
    SourceRecursiveIntersectionControl.identity right = some second →
    SourceRecursiveIntersectionDomain.extend domain
      ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair first second) ∈ inventory

/-- The computed initial source inventory has the required closure. -/
theorem source_closed (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source) :
    Closed source (SourceRecursiveIntersectionSourceInventory.domains source) :=
  ⟨SourceRecursiveIntersectionSourceInventory.empty_mem source,
    fun domain member left right leftAvailable rightAvailable first second leftId rightId =>
      SourceRecursiveIntersectionSourceInventory.extend_mem source facts domain member left right
        leftAvailable rightAvailable first second leftId rightId⟩

variable (source : InternedConstructorTemplates.State Symbol Guard) (inventory : List DomainKey)

/-- Source requests establish source scope before the native interpreter can publish them. -/
def Certified [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next => ∀ value after,
      SourceRecursiveIntersectionKernel.work job state = .done value after →
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      Certified (next value) after post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
        (SourceRecursiveIntersectionControl.pair first second) ∈ inventory ∧
      SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ Certified (next actual.1) after post
  | .read name next => Certified (next (SourcePreparedSharedRows.read state.heap name)) state post
  | .optionalBinder key body next => ∀ value after,
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after →
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      Certified (next value) after post
  | .node request next => NodeScope source request ∧ request.domain.key ∈ inventory ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
        Available after.heap value → Certified (next value) after post
  | .edge request next => EdgeScope source request ∧ request.domain.key ∈ inventory ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
        EdgeResident after.heap value → Certified (next value) after post
  | .finishNode _ _ next | .finishEdge _ _ next => Certified next state post

/-- Local source scope composes source continuations at their actual returned machine. -/
theorem certified_bind [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : Certified source inventory code state intermediate)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      SemanticReady after.heap → intermediate after value → Certified source inventory (next value) after post) :
    Certified source inventory (code.bind next) state post := by
  induction code generalizing state with
  | pure value => exact continuation value state valid (.refl _) semantic certificate
  | fail => trivial
  | work job resume ih | optionalBinder key body resume ih =>
      intro value after done afterValid growth afterSemantic
      exact ih value after afterValid afterSemantic
        (certificate value after done afterValid growth afterSemantic)
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (growth.trans later) finalSemantic middle)
  | enter domain left right first second resume ih =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      refine ⟨certificate.1, certificate.2.1, certificate.2.2.1, ?_⟩
      exact ih actual.1 after certificate.2.1 semantic certificate.2.2.2
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (certificate.2.2.1.trans later) finalSemantic middle)
  | read name resume ih => exact ih _ state valid semantic certificate continuation
  | node request resume ih | edge request resume ih =>
      refine ⟨certificate.1, certificate.2.1, ?_⟩
      intro value after afterValid growth afterSemantic available
      exact ih value after afterValid afterSemantic
        (certificate.2.2 value after afterValid growth afterSemantic available)
        (fun result final finalValid later finalSemantic middle =>
          continuation result final finalValid (growth.trans later) finalSemantic middle)
  | finishNode handle value rest ih | finishEdge handle value rest ih =>
      exact ih state valid semantic certificate continuation

/-- A source node call derives its source scope and resident-return continuation directly. -/
theorem requestNode_certified [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (scope : NodeScope source request) (member : request.domain.key ∈ inventory) :
    Certified source inventory (requestNode request.domain request.left request.right) state
      (fun after value => Available after.heap value) :=
  ⟨scope, member, fun _ _ _ _ _ available => available⟩

/-- A source edge call retains both original row scopes and child source scope. -/
theorem requestEdge_certified [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (scope : EdgeScope source request) (member : request.domain.key ∈ inventory) :
    Certified source inventory (requestEdge request.domain request.left request.right) state
      (fun after value => EdgeResident after.heap value) :=
  ⟨scope, member, fun _ _ _ _ _ resident => resident⟩

/-- Ordered source calls retain source scope and each returned physical output fact. -/
theorem walk_certified [DecidableEq (EdgeKey Symbol Guard)]
    (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state →
      SemanticReady state.heap → input state request → Certified source inventory (call request) state output)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (known : ∀ request ∈ requests, input state request) :
    Certified source inventory (walk call requests) state (fun after values => ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => intro value absent; cases absent
  | cons first rest ih =>
      apply certified_bind source inventory _ _ state valid semantic output _
        (calls first List.mem_cons_self state valid semantic (known first List.mem_cons_self))
      intro value after afterValid growth afterSemantic available
      have tailKnown := fun request member => inputStable state after growth request
        (known request (List.mem_cons_of_mem _ member))
      have tail := ih (fun request member => calls request (List.mem_cons_of_mem _ member))
        after afterValid afterSemantic tailKnown
      apply certified_bind source inventory _ _ after afterValid afterSemantic _ _ tail
      intro values final _ later _ all
      intro found member
      rcases List.mem_cons.mp member with rfl | member
      · exact outputStable after final later found available
      · exact all found member

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem work_certified (job : Work Symbol Guard A) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (property : InternedConstructorTemplates.State Symbol Guard → A → Prop)
    (verified : InternedNestedFacts.Verified state.heap (InternedNestedConstruction.work job state.heap) property) :
    Certified source inventory (.work job .pure) state (fun after value => property after.heap value) := by
  intro value after done _ _ _
  exact (safe_work job state valid property verified).2.2 value after done

private theorem node_walk_certified (request : A → NodeRequest Symbol Guard) (values : List A)
    (known : ∀ value ∈ values, NodeScope source (request value) ∧ (request value).domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source inventory (SourceRecursiveIntersectionCode.walk
      (fun value => .node (request value) .pure) values) state (fun after outputs => Values after.heap outputs) := by
  exact walk_certified source inventory _ values
    (fun _ value => NodeScope source (request value) ∧ (request value).domain.key ∈ inventory)
    (fun after value => Available after.heap value) (by intro _ _ _ _ known; exact known) available_stable
    (fun value _ current _ _ known =>
      requestNode_certified source inventory (request value) current known.1 known.2)
    state valid semantic known

private theorem edge_walk_certified (request : A → EdgeRequest Symbol Guard) (values : List A)
    (known : ∀ value ∈ values, EdgeScope source (request value) ∧ (request value).domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source inventory (SourceRecursiveIntersectionCode.walk
      (fun value => .edge (request value) .pure) values) state (fun after outputs => Edges after.heap outputs) := by
  exact walk_certified source inventory _ values
    (fun _ value => EdgeScope source (request value) ∧ (request value).domain.key ∈ inventory)
    (fun after value => EdgeResident after.heap value) (by intro _ _ _ _ known; exact known) edge_stable
    (fun value _ current _ _ known =>
      requestEdge_certified source inventory (request value) current known.1 known.2)
    state valid semantic known

/-- Literal hash-joined rows retain source scope and domain membership. -/
theorem rows_certified [DecidableEq Symbol] (facts : Facts source)
    (domain : Interned DomainKey)
    (first : Interned NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (scope : NodeScope source ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩)
    (known : domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source inventory (compileRows domain left right) state (fun after value => Available after.heap value) := by
  unfold compileRows
  have calls : ∀ pair ∈ pairs left right, EdgeScope source ⟨domain, pair.1, pair.2⟩ ∧
      domain.key ∈ inventory := by
    intro pair member
    have inside := (pairs_member left right pair).mp member
    exact ⟨scope.rows source facts domain first left leftDepth leftFree second right rightDepth rightFree
      pair.1 pair.2 inside.1 inside.2.1, known⟩
  apply certified_bind source inventory _ _ state valid semantic _ _
    (edge_walk_certified source inventory (fun pair => ⟨domain, pair.1, pair.2⟩) (pairs left right) calls state valid semantic)
  intro values middle middleValid _ _ children
  exact work_certified source inventory (makeNode values) middle middleValid Available
    (InternedNestedFacts.node_verified values middle.heap middleValid.1 children)

/-- Each left-union request uses its literal member and the original right operand. -/
theorem left_union_certified (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (right : Value Symbol Guard) (scope : NodeScope source ⟨domain, .union entry members depth free, right⟩)
    (known : domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source inventory
      ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain member right) members).bind
        (fun values => .work (makeUnion values) .pure)) state (fun after value => Available after.heap value) := by
  have calls : ∀ member ∈ members, NodeScope source ⟨domain, member, right⟩ ∧
      domain.key ∈ inventory := by
    intro member present
    exact ⟨scope.leftUnion source domain entry members depth free right member present, known⟩
  apply certified_bind source inventory _ _ state valid semantic _ _
    (node_walk_certified source inventory (fun member => ⟨domain, member, right⟩) members calls state valid semantic)
  intro values middle middleValid _ _ children
  exact work_certified source inventory (makeUnion values) middle middleValid Available
    (InternedNestedFacts.union_verified values middle.heap middleValid.1 children)

/-- Each right-union request retains the original left operand and literal member. -/
theorem right_union_certified (domain : Interned DomainKey)
    (left : Value Symbol Guard) (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (scope : NodeScope source ⟨domain, left, .union entry members depth free⟩)
    (known : domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source inventory
      ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain left member) members).bind
        (fun values => .work (makeUnion values) .pure)) state (fun after value => Available after.heap value) := by
  have calls : ∀ member ∈ members, NodeScope source ⟨domain, left, member⟩ ∧
      domain.key ∈ inventory := by
    intro member present
    exact ⟨scope.rightUnion source domain left entry members depth free member present, known⟩
  apply certified_bind source inventory _ _ state valid semantic _ _
    (node_walk_certified source inventory (fun member => ⟨domain, left, member⟩) members calls state valid semantic)
  intro values middle middleValid _ _ children
  exact work_certified source inventory (makeUnion values) middle middleValid Available
    (InternedNestedFacts.union_verified values middle.heap middleValid.1 children)

/-- Actual Mu entry uses an inventory key before its body request. -/
theorem mu_certified (closed : Closed source inventory) (request : NodeRequest Symbol Guard)
    (scope : NodeScope source request) (known : request.domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request) :
    Certified source inventory (compileMu request.domain request.left request.right) state
      (fun after value => Available after.heap value) := by
  cases first : SourceRecursiveIntersectionControl.identity request.left <;>
    cases second : SourceRecursiveIntersectionControl.identity request.right <;>
    simp only [compileMu, first, second]
  all_goals try trivial
  rename_i firstName secondName
  have entered := SourceRecursiveIntersectionKernel.entered state valid request.domain ready.1
    request.left request.right ready.2.1 ready.2.2 firstName secondName
  have member := closed.extend request.domain.key known request.left request.right
    scope.leftAvailable scope.rightAvailable firstName secondName first second
  have key := SourceRecursiveIntersectionSchedule.entered_key state.domains valid.2 request.domain.key
    request.left request.right firstName secondName
  have child := scope.mu source request.domain _ request.left request.right firstName secondName key
  refine ⟨member, entered.1, entered.2.1, child, ?_, ?_⟩
  · rw [key]
    exact member
  · intro value after afterValid _ _ available result final done _ _ _
    exact (safe_optionalBinder _ value after afterValid available).2.2 result final done

/-- The exact later binder read supplies its original available source payload. -/
theorem reference_certified (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool)
    (bindings : OriginalBindings source domain.key) (original : Original other) (available : Available source other)
    (known : domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified source inventory (compileReference domain name other left) state
      (fun after value => Available after.heap value) := by
  unfold compileReference
  split
  · rename_i member
    obtain ⟨bound, found, boundOriginal, boundAvailable, _⟩ :=
      bindings.read source state.heap valid.1 growth history domain.key name member
    simp only [Certified, found]
    cases left
    · exact requestNode_certified source inventory _ state
        ⟨original, boundOriginal, available, boundAvailable, bindings⟩ known
    · exact requestNode_certified source inventory _ state
        ⟨boundOriginal, original, boundAvailable, available, bindings⟩ known
  · trivial

/-- Every actual node branch derives child admission without a completed callback or result law. -/
theorem node_certified [DecidableEq Symbol]
    (facts : Facts source) (closed : Closed source inventory) (request : NodeRequest Symbol Guard)
    (scope : NodeScope source request) (known : request.domain.key ∈ inventory)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified source inventory (compileNode request) state (fun after value => Available after.heap value) := by
  cases request with
  | mk domain left right =>
    cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
    | empty => simpa only [compileNode, selected, Certified] using empty_available state.heap
    | reset =>
        simpa only [compileNode, selected] using requestNode_certified source inventory _ state
          (scope.reset source domain left right) closed.empty
    | self => simpa only [compileNode, selected, Certified] using ready.2.1
    | swap =>
        simpa only [compileNode, selected] using requestNode_certified source inventory _ state
          (scope.swap source domain left right)
          known
    | repeated key =>
        simp only [compileNode, selected, Certified]
        apply reference_available state.heap (.intersection key.1 key.2)
        intro name member
        simp [Value.free] at member
    | bothMu | leftMu | rightMu =>
        simpa only [compileNode, selected] using mu_certified source inventory closed ⟨domain, left, right⟩ scope known state valid ready
    | leftUnion =>
        simp only [compileNode, selected]
        cases left <;> try trivial
        exact left_union_certified source inventory _ _ _ _ _ _ scope known state valid semantic
    | rightUnion =>
        simp only [compileNode, selected]
        cases right <;> try trivial
        exact right_union_certified source inventory _ _ _ _ _ _ scope known state valid semantic
    | leftReference =>
        simp only [compileNode, selected]
        cases left <;> try trivial
        rename_i name
        cases name <;> first
          | exact reference_certified source inventory _ _ _ true scope.bindings scope.right scope.rightAvailable known state valid growth history
          | trivial
    | rightReference =>
        simp only [compileNode, selected]
        cases right <;> try trivial
        rename_i name
        cases name <;> first
          | exact reference_certified source inventory _ _ _ false scope.bindings scope.left scope.leftAvailable known state valid growth history
          | trivial
    | ordinary =>
        simp only [compileNode, selected]
        cases left <;> cases right <;> try trivial
        exact rows_certified source inventory facts _ _ _ _ _ _ _ _ _ scope known state valid semantic
    | unsupported => simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, Certified]

private theorem edge_work_certified
    (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (available : Values state.heap values) :
    Certified source inventory (.work (makeEdge symbol guard values) .pure) state
      (fun after value => EdgeResident after.heap value) := by
  intro value after done _ _ _
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact (InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available).result _ _ rfl

/-- Accepted child code derives admission of every actual ordered child request. -/
theorem children_certified
    (facts : Facts source)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request) (known : request.domain.key ∈ inventory)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (ready : EdgeReady state request) :
    Certified source inventory
      (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun after value => EdgeResident after.heap value) := by
  let physical := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  have stable : Stable physical := by
    intro before after growth pair resident
    exact ⟨resident.1.grows _ growth, growth.available _ resident.2.1, growth.available _ resident.2.2⟩
  have reached : ∀ pair ∈ request.left.children.zip request.right.children, physical state pair := by
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 inside.1,
      valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 inside.2⟩
  have children := walk_certified source inventory
    (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) physical (fun after value => Available after.heap value)
    stable available_stable (by
      intro pair member current _ _ _
      exact requestNode_certified source inventory ⟨request.domain, pair.1, pair.2⟩ current
        (scope.child source facts request pair member) known) state valid semantic reached
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind source inventory _ _ state valid semantic _ _ children
  intro values after afterValid _ _ available
  exact edge_work_certified source inventory request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values after afterValid available

/-- The literal stopped sentinel has no recursive request to admit. -/
theorem sentinel_certified
    (left : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Certified source inventory (SourceEqualityNativeCheckedCode.sentinel left) state
      (fun after value => EdgeResident after.heap value) := by
  apply edge_work_certified source inventory left.entry.key.symbol SourceEqualityConstraintConstructors.top
    [.empty] state valid
  intro value member
  simp only [List.mem_singleton] at member
  subst value
  exact empty_available _

/-- An actual checked body yield certifies only its literal emitted code and returned machine. -/
theorem body_certified [DecidableEq Symbol]
    (facts : Facts source)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request) (known : request.domain.key ∈ inventory)
    (before after : Checked width) (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    Certified source inventory code after.native.machine (fun final value => EdgeResident final.heap value) := by
  have same : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request .pure before
  rw [same]
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact sentinel_certified source inventory _ _ valid
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
          exact sentinel_certified source inventory _ _ valid
        · simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
          cases yielded
          exact sentinel_certified source inventory _ _ valid
        · simp only [SourceEqualityNativeDemand.code_bind_pure] at yielded
          cases yielded
          exact children_certified source inventory facts request scope known _ _ valid semantic ready


end MicroCFTA.SourceCurrentAllocatedRecursiveDomainCode
