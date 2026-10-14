import MicroCFTA.SourceRecursiveIntersectionKernelFacts

/-!
# Complete physical requests in the recursive source caller

Mu requests allocate the actual canonical domain before the body call.
References recover the original complete binder. Guarded edges retain
ordered child calls, conjoined constraints, and actual canonical readback.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionDomain

/-- Each recursive request preserves source facts and returns an available complete record. -/
def Calls
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ domain left right state, Valid state → Domain state domain → Available state.heap left → Available state.heap right →
    Checked state (call domain left right state) (fun after value => Available after.heap value)

/-- Unsupported source operands retain their exact current cache. -/
theorem unsupported_checked (left right : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) :
    Checked state (unsupported left right state) (fun after value => Available after.heap value) :=
  checked_failed state valid _ _

/-- Domain interning retains every earlier canonical domain identity. -/
theorem make_domain_grows (cache : Cache.State DomainKey) (key : DomainKey) :
    Extends cache.table (IntersectionEmptyDomain.make cache key).2.table := by
  by_cases empty : key = IntersectionEmptyDomain.emptyKey
  · simp only [IntersectionEmptyDomain.make, empty, ite_true]
    exact extends_refl _
  · simp only [IntersectionEmptyDomain.make, empty, ite_false]
    exact InternedBinderProtocol.intern_grows _ _

/-- Actual Mu-domain allocation derives validity, exact growth, and the new complete binding invariant. -/
theorem entered (state : Machine Symbol Guard) (valid : Valid state) (domain : Interned DomainKey) (known : Domain state domain)
    (left right : Value Symbol Guard) (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right)
    (first second : Nat) :
    let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
    let after : Machine Symbol Guard := {state with domains := actual.2}
    Valid after ∧ Extension state after ∧ Domain after actual.1 := by
  obtain ⟨domainValid, represented, canonical, typed, bindings⟩ := SourceRecursiveIntersectionEnvironment.enter_correct
    state.heap state.domains valid.2 domain.key known.bindings left right leftAvailable rightAvailable first second
  have growth := make_domain_grows state.domains
    (extend domain.key ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair first second))
  refine ⟨⟨valid.1, domainValid⟩, ⟨grows_refl _, extends_refl _, growth⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [represented.1]
    exact represented
  · rw [represented.1]
    exact canonical
  · rw [represented.1]
    exact typed
  · rw [represented.1]
    exact bindings

/-- A Mu exposes an available original body; every other source operand stays available. -/
theorem body_available (state : InternedConstructorTemplates.State Symbol Guard) (value : Value Symbol Guard)
    (available : Available state value) : Available state (body value) := by
  cases value with
  | empty | reference | node | union => exact available
  | mu entry stored depth ordinary =>
      exact available.children stored (by simp [children])

/-- Actual Mu calls compose domain allocation, original body requests, and the checked optional-binder constructor. -/
theorem mu_checked [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : Valid state) (known : Domain state domain) (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) :
    Checked state (mu call domain left right state) (fun after value => Available after.heap value) := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;> simp only [mu, first, second]
  all_goals try exact unsupported_checked left right state valid
  rename_i firstId secondId
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right firstId secondId
  let after : Machine Symbol Guard := {state with domains := actual.2}
  obtain ⟨afterValid, extension, afterDomain⟩ := entered state valid domain known left right leftAvailable rightAvailable firstId secondId
  have requested := calls actual.1 (body left) (body right) after afterValid afterDomain
    (body_available state.heap left leftAvailable) (body_available state.heap right rightAvailable)
  apply Checked.prepend extension
  apply checked_bind after _ _ _ _ requested
  intro value final returned finalValid available
  exact construction_checked final finalValid _ Available
    (SourceRecursiveIntersectionMaybeMu.verified _ value final.heap finalValid.1 available)

/-- Available source bindings exclude missing physical payloads and provide the complete next operands. -/
theorem reference_checked
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool)
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain) (available : Available state.heap other) :
    Checked state (reference call domain name other left state) (fun after value => Available after.heap value) := by
  by_cases bound : name ∈ names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name bound
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ stored entry.identity rfl
    simp only [reference, bound, ite_true, read]
    cases left
    · exact calls domain other (.mu entry body depth ordinary) state valid known available stored
    · exact calls domain (.mu entry body depth ordinary) other state valid known stored available
  · simp only [reference, bound, ite_false]
    exact checked_failed state valid _ _

/-- Ordered original child pairs retain complete returned records at their actual final cache. -/
theorem children_checked
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (requests : List (Value Symbol Guard × Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (inputs : ∀ pair ∈ requests, Available state.heap pair.1 ∧ Available state.heap pair.2) :
    Checked state (walk (fun pair => call domain pair.1 pair.2) requests state)
      (fun after values => ∀ value ∈ values, Available after.heap value) := by
  let input := fun (state : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain state domain ∧ Available state.heap pair.1 ∧ Available state.heap pair.2
  have stable : Stable input := by
    intro before after extension pair known
    exact ⟨known.1.grows domain extension, extension.available _ known.2.1, extension.available _ known.2.2⟩
  exact walk_checked (fun pair => call domain pair.1 pair.2) requests input _ stable available_stable
    (fun pair _ current currentValid known => calls domain pair.1 pair.2 current currentValid known.1 known.2.1 known.2.2)
    state valid (fun pair member => ⟨known, inputs pair member⟩)

/-- Guarded edge calls retain complete ordered child records and canonical physical edge results. -/
theorem edge_checked [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (valid : Valid state) (known : Domain state domain) (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right) :
    Checked state (edge emptyGuard conjoin (call domain) left right state) (fun after value => EdgeResident after.heap value) := by
  unfold edge
  split
  · have children := children_checked call calls domain (left.children.zip right.children) state valid known (by
      intro pair member
      have contained := List.of_mem_zip member
      exact ⟨valid.1.cached.edges left.entry.key left leftResident pair.1 contained.1,
        valid.1.cached.edges right.entry.key right rightResident pair.2 contained.2⟩)
    apply checked_bind state _ _ _ _ children
    intro values after returned afterValid available
    exact work_checked after afterValid _ EdgeResident
      (InternedNestedFacts.edge_verified _ _ values after.heap afterValid.1 available)
  · exact work_checked state valid _ EdgeResident
      (InternedNestedFacts.edge_verified _ _ [.empty] state.heap valid.1
        (by intro value member; simp only [List.mem_singleton] at member; subst value; exact empty_available state.heap))

/-- Source hash joining has exactly the equal-symbol physical row occurrences. -/
theorem pairs_member [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard)) (pair) :
    pair ∈ pairs left right ↔ pair.1 ∈ left ∧ pair.2 ∈ right ∧ pair.1.entry.key.symbol = pair.2.entry.key.symbol := by
  rw [pairs, SymbolicHashJoin.hashJoin_member]
  constructor
  · rintro ⟨first, firstIn, second, secondIn, same, rfl⟩
    exact ⟨firstIn, secondIn, same⟩
  · rintro ⟨firstIn, secondIn, same⟩
    exact ⟨pair.1, firstIn, pair.2, secondIn, same, rfl⟩

/-- Ordered matched source row requests retain complete resident edge records. -/
theorem rows_checked [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge) :
    Checked state (walk (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) state)
      (fun after values => ∀ value ∈ values, EdgeResident after.heap value) := by
  let input := fun (state : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain state domain ∧ EdgeResident state.heap pair.1 ∧ EdgeResident state.heap pair.2
  have stable : Stable input := by
    intro before after extension pair known
    exact ⟨known.1.grows domain extension, InternedEdgeResidency.edge_grows _ _ extension.heap _ known.2.1,
      InternedEdgeResidency.edge_grows _ _ extension.heap _ known.2.2⟩
  exact walk_checked (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right)
    input _ stable edge_stable
    (fun pair _ current currentValid known => edge_checked emptyGuard conjoin call calls domain pair.1 pair.2 current
      currentValid known.1 known.2.1 known.2.2)
    state valid (by
      intro pair member
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
      exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩)

/-- Ordered guarded row calls and canonical node construction retain complete source records. -/
theorem node_checked [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge) :
    Checked state (node emptyGuard conjoin (call domain) left right state) (fun after value => Available after.heap value) := by
  have rows := rows_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  unfold node
  apply checked_bind state _ _ _ _ rows
  intro values after returned afterValid resident
  exact work_checked after afterValid _ Available (InternedNestedFacts.node_verified values after.heap afterValid.1 resident)

end MicroCFTA.SourceRecursiveIntersectionKernel
