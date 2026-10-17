import MicroCFTA.SourceCurrentConstrainedCapGuardNative
import MicroCFTA.SourceRecursiveIntersectionKernelScope

/-!
# Guard heaps through actual bounded source intersection

The proof follows the actual recursive calls and constructor effects.
It retains the stopping heap on success, exhaustion, and pending writes.
The initial operands and domain require only their physical representation.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapKernelGuardHeap
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConstrainedCapGuardHeap (Heap)
variable {Symbol Guard : Type}

private theorem bind_heap (annotation : Guard → Prop) (result : Result Symbol Guard A)
    (next : A → Machine Symbol Guard → Result Symbol Guard B)
    (heap : Heap annotation result.state.heap)
    (later : ∀ value after, result = .done value after → Heap annotation after.heap →
      Heap annotation (next value after).state.heap) : Heap annotation (result.bind next).state.heap := by
  cases result with
  | failed failure state => exact heap
  | done value state => exact later value state rfl heap

private theorem walk_heap (annotation : Guard → Prop)
    (call : A → Machine Symbol Guard → Result Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (physical : Machine Symbol Guard → B → Prop)
    (stable : Stable input)
    (checked : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request →
      Checked state (call request state) physical)
    (observed : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request →
      SemanticHeap state.heap → ∀ value after, call request state = .done value after → SemanticHeap after.heap)
    (retained : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request →
      SemanticHeap state.heap → Heap annotation state.heap → Heap annotation (call request state).state.heap)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (inputs : ∀ request ∈ requests, input state request) (semantic : SemanticHeap state.heap)
    (heap : Heap annotation state.heap) : Heap annotation (walk call requests state).state.heap := by
  induction requests generalizing state with
  | nil => exact heap
  | cons first rest ih =>
      have firstChecked := checked first List.mem_cons_self state valid (inputs first List.mem_cons_self)
      rw [walk]
      apply bind_heap annotation _ _ (retained first List.mem_cons_self state valid
        (inputs first List.mem_cons_self) semantic heap)
      intro value after done afterHeap
      have afterValid : SourceRecursiveIntersectionKernel.Valid after := by
        simpa only [done, Result.state] using firstChecked.valid
      have growth : Extension state after := by simpa only [done, Result.state] using firstChecked.extension
      have afterSemantic := observed first List.mem_cons_self state valid (inputs first List.mem_cons_self) semantic value after done
      have tailHeap := ih (fun request member => checked request (List.mem_cons_of_mem first member))
        (fun request member => observed request (List.mem_cons_of_mem first member))
        (fun request member => retained request (List.mem_cons_of_mem first member)) after afterValid
        (fun request member => stable state after growth request (inputs request (List.mem_cons_of_mem first member)))
        afterSemantic afterHeap
      exact bind_heap annotation _ _ tailHeap (fun _ _ _ finalHeap => finalHeap)

private def GuardCalls (annotation : Guard → Prop)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ domain left right state, SourceRecursiveIntersectionKernel.Valid state → Domain state domain →
    Available state.heap left → Available state.heap right → SemanticHeap state.heap → Heap annotation state.heap →
    Heap annotation (call domain left right state).state.heap

private theorem children_heap (annotation : Guard → Prop)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call) (guards : GuardCalls annotation call)
    (domain : Interned DomainKey) (requests : List (Value Symbol Guard × Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (inputs : ∀ pair ∈ requests, Available state.heap pair.1 ∧ Available state.heap pair.2)
    (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation (walk (fun pair => call domain pair.1 pair.2) requests state).state.heap := by
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  apply walk_heap annotation _ requests input (fun after value => Available after.heap value)
    (fun _ _ growth _ known => ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩)
    (fun pair _ current currentValid known => calls domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    (fun pair _ current currentValid known sem value after done =>
      (scopes domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2 sem value after done).1)
    (fun pair _ current currentValid known => guards domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    state valid (fun pair member => ⟨known, inputs pair member⟩) semantic heap

private theorem edge_heap [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call) (guards : GuardCalls annotation call)
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation (edge emptyGuard conjoin (call domain) left right state).state.heap := by
  unfold edge
  split
  · have inputs : ∀ pair ∈ left.children.zip right.children, Available state.heap pair.1 ∧ Available state.heap pair.2 := by
      intro pair member
      have contained := List.of_mem_zip member
      exact ⟨valid.1.cached.edges left.entry.key left leftResident pair.1 contained.1,
        valid.1.cached.edges right.entry.key right rightResident pair.2 contained.2⟩
    exact bind_heap annotation _ _
      (children_heap annotation call calls scopes guards domain _ state valid known inputs semantic heap)
      (fun _ _ _ afterHeap => afterHeap)
  · exact heap

private theorem rows_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call) (guards : GuardCalls annotation call)
    (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation (walk (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) state).state.heap := by
  let input := fun (current : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain current domain ∧ EdgeResident current.heap pair.1 ∧ EdgeResident current.heap pair.2
  apply walk_heap annotation _ _ input (fun after value => EdgeResident after.heap value)
    (fun _ _ growth _ known => ⟨known.1.grows _ growth, edge_grows _ _ growth.heap _ known.2.1,
      edge_grows _ _ growth.heap _ known.2.2⟩)
    (fun pair _ current currentValid known => edge_checked emptyGuard conjoin call calls domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    (fun pair _ current currentValid known sem value after done =>
      (SourceRecursiveIntersectionScopeCalls.edge_scoped emptyGuard conjoin call calls scopes domain pair.1 pair.2 current
        currentValid known.1 known.2.1 known.2.2 sem value after done).1)
    (fun pair _ current currentValid known => edge_heap annotation emptyGuard conjoin call calls scopes guards domain
      pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    state valid (by
      intro pair member
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
      exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩) semantic heap

private theorem node_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call) (guards : GuardCalls annotation call)
    (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation (node emptyGuard conjoin (call domain) left right state).state.heap := by
  rw [node]
  exact bind_heap annotation _ _
    (rows_heap annotation emptyGuard conjoin call calls scopes guards domain left right state valid known leftResident rightResident semantic heap)
    (fun values after _ afterHeap => SourceCurrentConstrainedCapGuardHeap.preserve annotation after.heap _ afterHeap
      (InternedShallowHeap.makeNode_noNewMu values after.heap))

private theorem union_heap [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call) (guards : GuardCalls annotation call)
    (domain : Interned DomainKey) (members : List (Value Symbol Guard)) (other : Value Symbol Guard) (left : Bool)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value)
    (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation ((walk (fun member => if left then call domain member other else call domain other member) members state).bind
      fun values after => work (makeUnion values) after).state.heap := by
  let input := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap other ∧ Available current.heap value
  have retained := walk_heap annotation
    (fun member => if left then call domain member other else call domain other member) members input
    (fun after value => Available after.heap value)
    (fun _ _ growth _ known => ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩)
    (by intro member _ current currentValid known; cases left
        · exact calls domain other member current currentValid known.1 known.2.1 known.2.2
        · exact calls domain member other current currentValid known.1 known.2.2 known.2.1)
    (by intro member _ current currentValid known sem value after done; cases left
        · exact (scopes domain other member current currentValid known.1 known.2.1 known.2.2 sem value after done).1
        · exact (scopes domain member other current currentValid known.1 known.2.2 known.2.1 sem value after done).1)
    (by intro member _ current currentValid known; cases left
        · exact guards domain other member current currentValid known.1 known.2.1 known.2.2
        · exact guards domain member other current currentValid known.1 known.2.2 known.2.1)
    state valid (fun member present => ⟨known, available, membersAvailable member present⟩) semantic heap
  exact bind_heap annotation _ _ retained
    (fun values after _ afterHeap => SourceCurrentConstrainedCapGuardHeap.preserve annotation after.heap _ afterHeap
      (InternedShallowHeap.makeUnion_noNewMu values after.heap))

private theorem mu_heap [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call) (guards : GuardCalls annotation call)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right)
    (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation (mu call domain left right state).state.heap := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;> simp only [mu, first, second]
  all_goals try exact heap
  rename_i firstId secondId
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right firstId secondId
  let after : Machine Symbol Guard := {state with domains := actual.2}
  obtain ⟨afterValid, _, afterDomain⟩ := entered state valid domain known left right leftAvailable rightAvailable firstId secondId
  have leftBody := body_available state.heap left leftAvailable
  have rightBody := body_available state.heap right rightAvailable
  have requested := calls actual.1 (body left) (body right) after afterValid afterDomain leftBody rightBody
  have observed := scopes actual.1 (body left) (body right) after afterValid afterDomain leftBody rightBody semantic
  apply bind_heap annotation _ _ (guards actual.1 (body left) (body right) after afterValid afterDomain leftBody rightBody semantic heap)
  intro value final done finalHeap
  have kept := SourceCurrentConstrainedCapGuardNative.optional_heap annotation _ value final.heap
    (observed value final done).1 (requested.result value final done) finalHeap
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu _ value final.heap <;> exact kept

private theorem reference_heap (annotation : Guard → Prop)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (guards : GuardCalls annotation call) (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (available : Available state.heap other) (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation (reference call domain name other left state).state.heap := by
  by_cases bound : name ∈ names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name bound
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ stored entry.identity rfl
    simp only [reference, bound, ite_true, read]
    cases left
    · exact guards domain other (.mu entry body depth ordinary) state valid known available stored semantic heap
    · exact guards domain (.mu entry body depth ordinary) other state valid known stored available semantic heap
  · simp only [reference, bound, ite_false]
    exact heap

private theorem onNode_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call) (guards : GuardCalls annotation call)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right)
    (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation (onNode emptyGuard conjoin call domain left right state).state.heap := by
  cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
  | empty =>
      simp only [onNode, selected]
      exact heap
  | reset =>
      simp only [onNode, selected]
      exact guards _ left right state valid (empty_domain state) leftAvailable rightAvailable semantic semantic heap
  | self =>
      simp only [onNode, selected]
      exact heap
  | swap =>
      simp only [onNode, selected]
      exact guards domain right left state valid known rightAvailable leftAvailable semantic semantic heap
  | repeated key =>
      simp only [onNode, selected]
      exact heap
  | bothMu | leftMu | rightMu =>
      simp only [onNode, selected]
      exact mu_heap annotation call calls scopes guards domain left right state valid known leftAvailable rightAvailable semantic heap
  | leftUnion =>
      simp only [onNode, selected]
      cases left with
      | union entry members depth free =>
          exact union_heap annotation call calls scopes guards domain members right true state valid known rightAvailable
            (fun value member => leftAvailable.children value (by simpa only [children] using member)) semantic heap
      | empty | reference | node | mu => exact heap
  | rightUnion =>
      simp only [onNode, selected]
      cases right with
      | union entry members depth free =>
          exact union_heap annotation call calls scopes guards domain members left false state valid known leftAvailable
            (fun value member => rightAvailable.children value (by simpa only [children] using member)) semantic heap
      | empty | reference | node | mu => exact heap
  | leftReference =>
      simp only [onNode, selected]
      cases left with
      | reference name =>
          cases name <;> try exact heap
          rename_i identity
          exact reference_heap annotation call guards domain identity right true state valid known rightAvailable semantic heap
      | empty | node | union | mu => exact heap
  | rightReference =>
      simp only [onNode, selected]
      cases right with
      | reference name =>
          cases name <;> try exact heap
          rename_i identity
          exact reference_heap annotation call guards domain identity left false state valid known leftAvailable semantic heap
      | empty | node | union | mu => exact heap
  | ordinary =>
      simp only [onNode, selected]
      cases left <;> cases right <;> try exact heap
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      exact node_heap annotation emptyGuard conjoin call calls scopes guards domain firstEdges secondEdges state valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member) semantic heap
  | unsupported =>
      simp only [onNode, selected]
      exact heap

/-- Every bounded source call retains causal guard observations at its actual stopping heap. -/
theorem execute_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right)
    (semantic : SemanticHeap state.heap) (heap : Heap annotation state.heap) :
    Heap annotation (execute emptyGuard conjoin fuel domain left right state).state.heap := by
  induction fuel generalizing domain left right state with
  | zero => exact heap
  | succ fuel ih =>
      exact onNode_heap annotation emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel)
        (SourceRecursiveIntersectionScopeCalls.execute_scoped emptyGuard conjoin fuel) ih
        domain left right state valid known leftAvailable rightAvailable semantic heap

end MicroCFTA.SourceCurrentConstrainedCapKernelGuardHeap
