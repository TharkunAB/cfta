import MicroCFTA.SourceRecursiveIntersectionNativeDemandProgress

/-!
# Original operand scope of recursive source requests

Recursive requests use original physical operands and original binders.
Constructor results remain in continuations. They do not become operands
of later source requests. Original scope is fixed in the initial heap.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open InternedProbeProvenance InternedNestedFacts SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionEnvironment

/-- Every bound source name retains an original available Mu in the fixed input heap. -/
def OriginalBindings (source : InternedConstructorTemplates.State Symbol Guard) (domain : DomainKey) : Prop :=
  ∀ name ∈ SourceRecursiveIntersectionDomain.names domain, OriginalInput source (.mu name)

/-- A node request retains original available operands and original source bindings. -/
structure NodeScope (source : InternedConstructorTemplates.State Symbol Guard) (request : NodeRequest Symbol Guard) : Prop where
  left : Original request.left
  right : Original request.right
  leftAvailable : Available source request.left
  rightAvailable : Available source request.right
  bindings : OriginalBindings source request.domain.key

/-- A row request retains original resident edges, complete original children, and source bindings. -/
structure EdgeScope (source : InternedConstructorTemplates.State Symbol Guard) (request : EdgeRequest Symbol Guard) : Prop where
  leftResident : InternedEdgeResidency.EdgeResident source request.left
  rightResident : InternedEdgeResidency.EdgeResident source request.right
  left : ∀ child ∈ request.left.children, Original child
  right : ∀ child ∈ request.right.children, Original child
  bindings : OriginalBindings source request.domain.key

/-- Actual closed original roots start with empty original binder scope. -/
theorem initial_scope (source : InternedConstructorTemplates.State Symbol Guard) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right) (leftAvailable : Available source left)
    (rightAvailable : Available source right) : NodeScope source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := by
  refine ⟨leftOriginal, rightOriginal, leftAvailable, rightAvailable, ?_⟩
  intro name member
  cases member

/-- Actual source swaps retain the original operand and binding scope. -/
theorem NodeScope.swap (source : InternedConstructorTemplates.State Symbol Guard) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (scope : NodeScope source ⟨domain, left, right⟩) : NodeScope source ⟨domain, right, left⟩ :=
  ⟨scope.right, scope.left, scope.rightAvailable, scope.leftAvailable, scope.bindings⟩

/-- An actual empty-domain reset retains the same original operands. -/
theorem NodeScope.reset (source : InternedConstructorTemplates.State Symbol Guard) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (scope : NodeScope source ⟨domain, left, right⟩) :
    NodeScope source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
  initial_scope source left right scope.left scope.right scope.leftAvailable scope.rightAvailable

/-- An original physical Mu retains its original stored body. -/
theorem body_original (value : Value Symbol Guard) (original : Original value) : Original (SourceRecursiveIntersectionKernel.body value) := by
  cases original <;> first | assumption | constructor <;> assumption

/-- Actual Mu binding entries retain original syntax rather than probe metadata. -/
theorem bindings_original (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) : Original binding.2 := by
  rcases List.mem_append.mp member with first | second
  · cases leftOriginal <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at first <;> try contradiction
    subst binding
    exact .mu _ _ _ _ (by assumption)
  · cases rightOriginal <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at second <;> try contradiction
    subst binding
    exact .mu _ _ _ _ (by assumption)

/-- Source canonical domain extension retains original binders at all old and new names. -/
theorem OriginalBindings.extend (source : InternedConstructorTemplates.State Symbol Guard) (domain : DomainKey)
    (original : OriginalBindings source domain) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right) (key : Nat × Nat) :
    OriginalBindings source (SourceRecursiveIntersectionDomain.extend domain ((bindings left right).map Prod.fst) key) := by
  intro name member
  rcases (SourceRecursiveIntersectionDomain.extend_names domain _ key name).mp member with added | old
  · obtain ⟨binding, present, rfl⟩ := List.mem_map.mp added
    obtain ⟨entry, body, depth, ordinary, same, available⟩ := bindings_available source left right leftAvailable rightAvailable binding present
    have retained := bindings_original left right leftOriginal rightOriginal binding present
    subst binding
    exact ⟨.mu entry body depth ordinary, retained, available, rfl⟩
  · exact original name old

/-- Actual Mu entry retains original bodies and original canonical bindings in the fixed input heap. -/
theorem NodeScope.mu (source : InternedConstructorTemplates.State Symbol Guard) (domain entered : Interned DomainKey)
    (left right : Value Symbol Guard) (scope : NodeScope source ⟨domain, left, right⟩) (first second : Nat)
    (key : entered.key = SourceRecursiveIntersectionDomain.extend domain.key ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair first second)) :
    NodeScope source ⟨entered, SourceRecursiveIntersectionKernel.body left, SourceRecursiveIntersectionKernel.body right⟩ := by
  refine ⟨body_original left scope.left, body_original right scope.right, body_available source left scope.leftAvailable,
    body_available source right scope.rightAvailable, ?_⟩
  rw [key]
  exact scope.bindings.extend source domain.key left right scope.left scope.right scope.leftAvailable scope.rightAvailable _

/-- Original union syntax retains every actual original member. -/
theorem union_member_original (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (original : Original (.union entry members depth free)) (child : Value Symbol Guard) (member : child ∈ members) : Original child := by
  cases original with | union _ _ _ _ originals => exact originals child member

/-- Original node syntax retains every actual original ordered edge child. -/
theorem node_child_original (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (original : Original (.node entry edges depth free)) (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (child : Value Symbol Guard) (member : child ∈ edge.children) : Original child := by
  cases original with | node _ _ _ _ originals => exact originals edge present child member

/-- Actual left union requests retain their fixed original operand scope. -/
theorem NodeScope.leftUnion (source : InternedConstructorTemplates.State Symbol Guard) (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (right : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, .union entry members depth free, right⟩) (child : Value Symbol Guard) (member : child ∈ members) :
    NodeScope source ⟨domain, child, right⟩ :=
  ⟨union_member_original entry members depth free scope.left child member, scope.right,
    scope.leftAvailable.children child member, scope.rightAvailable, scope.bindings⟩

/-- Actual right union requests retain their fixed original operand scope. -/
theorem NodeScope.rightUnion (source : InternedConstructorTemplates.State Symbol Guard) (domain : Interned DomainKey)
    (left : Value Symbol Guard) (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (scope : NodeScope source ⟨domain, left, .union entry members depth free⟩) (child : Value Symbol Guard) (member : child ∈ members) :
    NodeScope source ⟨domain, left, child⟩ :=
  ⟨scope.left, union_member_original entry members depth free scope.right child member,
    scope.leftAvailable, scope.rightAvailable.children child member, scope.bindings⟩

/-- Actual source row requests retain original resident rows and all original children. -/
theorem NodeScope.rows (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source) (domain : Interned DomainKey)
    (first : Interned NodeKey) (leftEdges : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned NodeKey) (rightEdges : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (scope : NodeScope source ⟨domain, .node first leftEdges leftDepth leftFree, .node second rightEdges rightDepth rightFree⟩)
    (left right : EdgeValue Symbol Guard) (leftMember : left ∈ leftEdges) (rightMember : right ∈ rightEdges) :
    EdgeScope source ⟨domain, left, right⟩ :=
  ⟨facts.linked first.key _ (scope.leftAvailable.resident first rfl) left leftMember,
    facts.linked second.key _ (scope.rightAvailable.resident second rfl) right rightMember,
    node_child_original first leftEdges leftDepth leftFree scope.left left leftMember,
    node_child_original second rightEdges rightDepth rightFree scope.right right rightMember, scope.bindings⟩

/-- Ordered physical edge children retain their original node-request scope. -/
theorem EdgeScope.child (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request) (children : Value Symbol Guard × Value Symbol Guard)
    (member : children ∈ request.left.children.zip request.right.children) : NodeScope source ⟨request.domain, children.1, children.2⟩ := by
  have inside := List.of_mem_zip member
  exact ⟨scope.left children.1 inside.1, scope.right children.2 inside.2,
    facts.cached.edges request.left.entry.key request.left scope.leftResident children.1 inside.1,
    facts.cached.edges request.right.entry.key request.right scope.rightResident children.2 inside.2, scope.bindings⟩

/-- Actual later reads of bound original names retain the original complete Mu payload. -/
theorem OriginalBindings.read (source current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (domain : DomainKey) (bindings : OriginalBindings source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Original value ∧ Available source value ∧ inputOf value = .mu name := by
  obtain ⟨value, original, available, complete⟩ := bindings name member
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case mu entry body depth ordinary original =>
    cases complete
    exact ⟨.mu entry body depth ordinary,
      SourcePreparedSharedRows.read_identity current facts _ (available.grows source current growth history) entry.identity rfl,
      .mu entry body depth ordinary original, available, rfl⟩

end MicroCFTA.SourceRecursiveIntersectionCode
