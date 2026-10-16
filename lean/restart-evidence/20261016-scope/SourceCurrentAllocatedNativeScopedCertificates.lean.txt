import MicroCFTA.SourceCurrentAllocatedNativeScopedCode
import MicroCFTA.SourceRecursiveIntersectionResultScope
import MicroCFTA.SourceEqualityNativeDemandContinuation

/-!
# Static scope certificates for ordinary checked branches

Ordered child requests supply only their own result scope and physical
record. Actual constructor readback retains those names. Every yielded
checked edge prefix has a certificate. No parent scope or completed trace
supplies that certificate. Mu and reference dispatch remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeScopedCertificates
open Language Cache InternedBinderProtocol InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
open SourceCurrentAllocatedNativeScopedCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Ordered node requests collect their available results and incoming pair scope. -/
theorem node_walk_certified (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (operands : A → Value Symbol Guard × Value Symbol Guard) (inputs : List A)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (SourceRecursiveIntersectionCode.walk (fun input => requestNode domain (operands input).1 (operands input).2) inputs)
      state (fun after values => Values after.heap values ∧ ∀ value ∈ values, Scope domain.key.seen value) := by
  induction inputs generalizing state with
  | nil => exact ⟨(by intro value member; cases member), (by intro value member; cases member)⟩
  | cons first rest ih =>
      simp only [SourceRecursiveIntersectionCode.walk, requestNode, Code.bind, Certified]
      intro value middle middleValid growth middleSemantic available scope
      apply certified_bind _ _ middle middleValid middleSemantic _ _ (ih middle middleValid middleSemantic)
      intro values after afterValid later afterSemantic tail
      constructor
      · intro child member
        cases member with
        | head => exact later.available value available
        | tail _ member => exact tail.1 child member
      · intro child member
        cases member with
        | head => exact scope
        | tail _ member => exact tail.2 child member

/-- Ordered edge requests collect resident rows without a symbol-match requirement. -/
theorem edge_walk_certified (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (operands : A → EdgeValue Symbol Guard × EdgeValue Symbol Guard) (inputs : List A)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (SourceRecursiveIntersectionCode.walk (fun input => requestEdge domain (operands input).1 (operands input).2) inputs)
      state (fun after values => Edges after.heap values ∧ ∀ value ∈ values, EdgeScope domain.key.seen value) := by
  induction inputs generalizing state with
  | nil => exact ⟨(by intro value member; cases member), (by intro value member; cases member)⟩
  | cons first rest ih =>
      simp only [SourceRecursiveIntersectionCode.walk, requestEdge, Code.bind, Certified]
      intro value middle middleValid growth middleSemantic resident scope
      apply certified_bind _ _ middle middleValid middleSemantic _ _ (ih middle middleValid middleSemantic)
      intro values after afterValid later afterSemantic tail
      constructor
      · intro edge member
        cases member with
        | head => exact edge_grows _ _ later.heap value resident
        | tail _ member => exact tail.1 edge member
      · intro edge member
        cases member with
        | head => exact scope
        | tail _ member => exact tail.2 edge member

private theorem edge_work_certified (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : Values state.heap values) (resultScope : ∀ value ∈ values, Scope domain.key.seen value) :
    Certified (.work (makeEdge symbol guard values) .pure) state
      (fun _ value => EdgeScope domain.key.seen value) := by
  intro value after done afterValid growth afterSemantic
  rw [(work_done _ state value after done).1]
  exact SourceRecursiveIntersectionResultScope.edge domain.key.seen symbol guard values state.heap valid.1 available resultScope

/-- The literal actual row join and node constructor retain only the incoming pair names. -/
theorem compileRows_certified [DecidableEq Symbol] (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap) :
    Certified (compileRows domain left right) state (fun _ value => Scope domain.key.seen value) := by
  unfold compileRows
  apply certified_bind _ _ state valid semantic _ _
    (edge_walk_certified domain (fun pair => pair) (pairs left right) state valid semantic)
  intro values middle middleValid growth middleSemantic children
  intro value after done afterValid later afterSemantic
  rw [(work_done _ middle value after done).1]
  exact SourceRecursiveIntersectionResultScope.node domain.key.seen values middle.heap middleValid.1 children.1 children.2

/-- A left-union source walk retains scope through the actual union normalization. -/
theorem left_union_certified (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (members : List (Value Symbol Guard)) (right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap) :
    Certified ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain member right) members).bind
      (fun values => .work (makeUnion values) .pure)) state (fun _ value => Scope domain.key.seen value) := by
  apply certified_bind _ _ state valid semantic _ _
    (node_walk_certified domain (fun member => (member, right)) members state valid semantic)
  intro values middle middleValid growth middleSemantic children
  intro value after done afterValid later afterSemantic
  rw [(work_done _ middle value after done).1]
  exact SourceRecursiveIntersectionResultScope.union domain.key.seen values middle.heap
    middleSemantic.ready.semantic.1.normal children.1 children.2

/-- A right-union source walk retains the same incoming pair scope. -/
theorem right_union_certified (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (members : List (Value Symbol Guard)) (left : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap) :
    Certified ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain left member) members).bind
      (fun values => .work (makeUnion values) .pure)) state (fun _ value => Scope domain.key.seen value) := by
  apply certified_bind _ _ state valid semantic _ _
    (node_walk_certified domain (fun member => (left, member)) members state valid semantic)
  intro values middle middleValid growth middleSemantic children
  intro value after done afterValid later afterSemantic
  rw [(work_done _ middle value after done).1]
  exact SourceRecursiveIntersectionResultScope.union domain.key.seen values middle.heap
    middleSemantic.ready.semantic.1.normal children.1 children.2

/-- Actual accepted child code retains scope for every literal combined constraint. -/
theorem children_certified (request : EdgeRequest Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap) :
    Certified (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun _ value => EdgeScope request.domain.key.seen value) := by
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind _ _ state valid semantic _ _
    (node_walk_certified request.domain (fun pair => pair) (request.left.children.zip request.right.children) state valid semantic)
  intro values middle middleValid growth middleSemantic children
  exact edge_work_certified request.domain request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
    values middle middleValid children.1 children.2

/-- The stopped branch's literal empty child has scope without a recursive call. -/
theorem sentinel_certified (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) :
    Certified (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ value => EdgeScope request.domain.key.seen value) := by
  apply edge_work_certified request.domain request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty] state valid
  · intro value member
    cases member with
    | head => exact empty_available _
    | tail _ member => cases member
  · intro value member
    cases member with
    | head => exact SourceRecursiveIntersectionResultScope.closed _ _ rfl
    | tail _ member => cases member

/-- Empty rejection has no free names at any current machine. -/
theorem empty_certified (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard) :
    Certified (.pure (.empty : Value Symbol Guard)) state (fun _ value => Scope domain.key.seen value) :=
  SourceRecursiveIntersectionResultScope.closed _ _ rfl

/-- Reset receives an empty-domain child scope and weakens it to the incoming scope. -/
theorem reset_certified (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard) :
    Certified (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right) state
      (fun _ value => Scope request.domain.key.seen value) := by
  intro value after afterValid growth afterSemantic available resultScope
  exact SourceRecursiveIntersectionResultScope.weaken [] request.domain.key.seen
    (fun _ member => False.elim (List.not_mem_nil member)) value resultScope

/-- A swap's child uses exactly the same incoming pair set. -/
theorem swap_certified (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard) :
    Certified (requestNode request.domain request.right request.left) state
      (fun _ value => Scope request.domain.key.seen value) := by
  intro value after afterValid growth afterSemantic available resultScope
  exact resultScope

/-- Source self reuse selects a closed original value before any recursive call. -/
theorem self_certified (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    Certified (.pure request.left) state (fun _ value => Scope request.domain.key.seen value) :=
  SourceRecursiveIntersectionResultScope.closed _ _
    (SourceRecursiveIntersectionResultScope.self_closed _ _ _ selected)

/-- Repeated cutoff returns the actual pair already present in the incoming domain. -/
theorem repeated_certified (request : NodeRequest Symbol Guard) (pair : Nat × Nat) (state : Machine Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .repeated pair) :
    Certified (.pure (SourceRecursiveIntersectionControl.repeatedValue pair : Value Symbol Guard)) state
      (fun _ value => Scope request.domain.key.seen value) :=
  SourceRecursiveIntersectionResultScope.repeated request.domain.key.seen pair
    (SourceRecursiveIntersectionResultScope.repeated_seen _ _ _ _ selected)

/-- Every actual yielded checked prefix derives its certificate from its own branch shape. -/
theorem prefix_certified [DecidableEq Symbol] (request : EdgeRequest Symbol Guard)
    (before : SourceEqualityNativeDemand.State width) (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (semantic : SemanticReady before.native.machine.heap)
    (one : SourceEqualityNativeDemand.step (.edgeBody request .pure) before =
      .yielded (.code code) {before with operations := operations}) :
    Certified code before.native.machine (fun _ value => EdgeScope request.domain.key.seen value) := by
  change SourceEqualityNativeDemand.body request .pure before = _ at one
  unfold SourceEqualityNativeDemand.body at one
  split at one
  · simp only [SourceEqualityNativeDemand.sentinel] at one
    have same := SourceEqualityNativeDemand.Control.code.inj (SourceEqualityNativeDemand.Outcome.yielded.inj one).1
    rw [← same, SourceEqualityNativeDemand.code_bind_pure]
    exact sentinel_certified request before.native.machine valid
  · split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · dsimp only at one
        split at one
        · cases one
        · simp only [SourceEqualityNativeDemand.sentinel] at one
          have same := SourceEqualityNativeDemand.Control.code.inj (SourceEqualityNativeDemand.Outcome.yielded.inj one).1
          rw [← same, SourceEqualityNativeDemand.code_bind_pure]
          exact sentinel_certified request before.native.machine valid
        · simp only [SourceEqualityNativeDemand.sentinel] at one
          have same := SourceEqualityNativeDemand.Control.code.inj (SourceEqualityNativeDemand.Outcome.yielded.inj one).1
          rw [← same, SourceEqualityNativeDemand.code_bind_pure]
          exact sentinel_certified request before.native.machine valid
        · have same := SourceEqualityNativeDemand.Control.code.inj (SourceEqualityNativeDemand.Outcome.yielded.inj one).1
          rw [← same, SourceEqualityNativeDemand.code_bind_pure]
          exact children_certified request _ before.native.machine valid semantic

end MicroCFTA.SourceCurrentAllocatedNativeScopedCertificates
