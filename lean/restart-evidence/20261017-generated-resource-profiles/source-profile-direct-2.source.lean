import MicroCFTA.SourceRecursiveIntersectionSourceInventory
import MicroCFTA.SourceCurrentConstrainedCapSourceWeightTransport

/-!
# Branching limits from actual source payloads

The initial issued ranges contain finitely many successful payload reads.
Their literal row, union-member, and edge-child counts give source limits.
Mu bodies and probes remain covered through actual availability.
Successful earlier reads retain these limits after record and issued-key growth.
An absent earlier identity has no readback or profile guarantee.
-/
namespace MicroCFTA.SourceRecursiveIntersectionSourceProfile
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedEdgeResidency SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
variable {Symbol Guard : Type}

/-- The three limits bound literal source branching. -/
structure Limits where
  /-- Maximum number of literal rows at one source node. -/
  rows : Nat
  /-- Maximum number of literal members at one source union. -/
  members : Nat
  /-- Maximum number of ordered children at one source edge. -/
  arity : Nat

/-- Read the complete edge payload under its actual issued key. -/
def edgeRead (source : State Symbol Guard) (identity : Nat) : Option (EdgeValue Symbol Guard) :=
  (source.edges.issued identity).bind source.edgeRecords

/-- Keep every successful node payload read in the initial issued range. -/
def nodePayloads (source : State Symbol Guard) : List (Value Symbol Guard) :=
  (List.range source.nodes.next).filterMap (SourcePreparedSharedRows.read source)

/-- Keep every successful edge payload read in the independent issued range. -/
def edgePayloads (source : State Symbol Guard) : List (EdgeValue Symbol Guard) :=
  (List.range source.edges.next).filterMap (edgeRead source)

/-- Only an explicit union has a literal member list. -/
def memberCount : Value Symbol Guard → Nat
  | .union _ members _ _ => members.length
  | _ => 0

/-- Sums give conservative limits without a distinct-payload assumption. -/
def limits (source : State Symbol Guard) : Limits :=
  ⟨((nodePayloads source).map (fun value => (nodeEdges value).length)).sum,
    ((nodePayloads source).map memberCount).sum,
    ((edgePayloads source).map (fun edge => edge.children.length)).sum⟩

/-- Count the complete stored node syntax, including Mu bodies and probes. -/
noncomputable def nodeSize (source : State Symbol Guard) : Nat :=
  ((nodePayloads source).map sizeOf).sum

/-- Count the complete stored edge syntax and its actual children. -/
noncomputable def edgeSize (source : State Symbol Guard) : Nat :=
  ((edgePayloads source).map sizeOf).sum

/-- A node profile bounds its literal rows and explicit union members. -/
def Node (bounds : Limits) (value : Value Symbol Guard) : Prop :=
  (nodeEdges value).length ≤ bounds.rows ∧ memberCount value ≤ bounds.members

/-- An edge profile bounds the actual ordered child list. -/
def Edge (bounds : Limits) (edge : EdgeValue Symbol Guard) : Prop :=
  edge.children.length ≤ bounds.arity

private theorem member_sum {Item : Type} (measure : Item → Nat) (items : List Item)
    (item : Item) (member : item ∈ items) : measure item ≤ (items.map measure).sum := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · simp only [List.map_cons, List.sum_cons]
      omega
    · have lower := ih later
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Every successful node read is included under its actual issued identity. -/
theorem node_mem (source : State Symbol Guard) (facts : Facts source) (identity : Nat)
    (value : Value Symbol Guard) (found : SourcePreparedSharedRows.read source identity = some value) :
    value ∈ nodePayloads source := by
  obtain ⟨key, issued, _stored⟩ := Option.bind_eq_some_iff.mp found
  exact List.mem_filterMap.mpr ⟨identity,
    List.mem_range.mpr (facts.coherent.valid.2.1 identity key issued), found⟩

/-- Every successful edge read is included under its independent issued identity. -/
theorem edge_mem (source : State Symbol Guard) (facts : Facts source) (identity : Nat)
    (edge : EdgeValue Symbol Guard) (found : edgeRead source identity = some edge) :
    edge ∈ edgePayloads source := by
  obtain ⟨key, issued, _stored⟩ := Option.bind_eq_some_iff.mp found
  exact List.mem_filterMap.mpr ⟨identity,
    List.mem_range.mpr (facts.coherent.valid.1.1 identity key issued), found⟩

/-- Actual successful node reads satisfy both computed branching limits. -/
theorem read_bound (source : State Symbol Guard) (facts : Facts source) (identity : Nat)
    (value : Value Symbol Guard) (found : SourcePreparedSharedRows.read source identity = some value) :
    Node (limits source) value :=
  ⟨member_sum (fun value => (nodeEdges value).length) _ _ (node_mem source facts identity value found),
    member_sum memberCount _ _ (node_mem source facts identity value found)⟩

/-- The complete syntax of an actual node read is bounded by the initial payload sum. -/
theorem read_size (source : State Symbol Guard) (facts : Facts source) (identity : Nat)
    (value : Value Symbol Guard) (found : SourcePreparedSharedRows.read source identity = some value) :
    sizeOf value ≤ nodeSize source :=
  member_sum _ _ _ (node_mem source facts identity value found)

/-- Actual successful edge reads satisfy the computed arity limit. -/
theorem edge_read_bound (source : State Symbol Guard) (facts : Facts source) (identity : Nat)
    (edge : EdgeValue Symbol Guard) (found : edgeRead source identity = some edge) :
    Edge (limits source) edge :=
  member_sum (fun edge => edge.children.length) _ _ (edge_mem source facts identity edge found)

/-- The complete syntax of an actual edge read is bounded by the initial payload sum. -/
theorem edge_read_size (source : State Symbol Guard) (facts : Facts source) (identity : Nat)
    (edge : EdgeValue Symbol Guard) (found : edgeRead source identity = some edge) :
    sizeOf edge ≤ edgeSize source :=
  member_sum _ _ _ (edge_mem source facts identity edge found)

/-- Residency supplies the exact edge payload read, including cache hits. -/
theorem resident_read (source : State Symbol Guard) (facts : Facts source)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident source edge) :
    edgeRead source edge.entry.identity = some edge := by
  have stored := (facts.coherent.edges edge.entry.key edge resident).1
  have issued := (facts.coherent.valid.1.2 edge.entry.key edge.entry stored).2
  simp only [edgeRead, issued, Option.bind_some]
  exact resident

/-- Every available source value has bounded literal branching, including Mu and references. -/
theorem available (source : State Symbol Guard) (facts : Facts source)
    (value : Value Symbol Guard) (known : Available source value) : Node (limits source) value := by
  cases value with
  | empty | reference => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | node entry edges depth free | union entry edges depth free | mu entry edges depth free =>
    exact read_bound source facts entry.identity _
      (SourcePreparedSharedRows.read_identity source facts _ known entry.identity rfl)

/-- Every available recorded value has a bounded complete stored syntax. -/
theorem available_size (source : State Symbol Guard) (facts : Facts source)
    (value : Value Symbol Guard) (known : Available source value) (identity : Nat)
    (recorded : SourcePreparedSharedRows.reference value = some identity) :
    sizeOf value ≤ nodeSize source :=
  read_size source facts identity value (SourcePreparedSharedRows.read_identity source facts value known identity recorded)

/-- Every resident source edge has bounded arity and complete stored syntax. -/
theorem resident (source : State Symbol Guard) (facts : Facts source)
    (edge : EdgeValue Symbol Guard) (known : EdgeResident source edge) :
    Edge (limits source) edge ∧ sizeOf edge ≤ edgeSize source :=
  ⟨edge_read_bound source facts _ edge (resident_read source facts edge known),
    edge_read_size source facts _ edge (resident_read source facts edge known)⟩

/-- Every physical child of an available value remains within the same source profile. -/
theorem child (source : State Symbol Guard) (facts : Facts source)
    (value : Value Symbol Guard) (known : Available source value) (next : Value Symbol Guard)
    (member : next ∈ InternedProbeProvenance.children value) : Node (limits source) next :=
  available source facts next (known.children next member)

/-- The actual stored Mu body remains within the original source profile. -/
theorem body (source : State Symbol Guard) (facts : Facts source)
    (value : Value Symbol Guard) (known : Available source value) :
    Node (limits source) (SourceRecursiveIntersectionKernel.body value) :=
  available source facts _ (SourceRecursiveIntersectionCode.body_available source value known)

/-- Both original node operands satisfy the same computed source branching limits. -/
theorem node_scope (source : State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) :
    Node (limits source) request.left ∧ Node (limits source) request.right :=
  ⟨available source facts request.left scope.leftAvailable,
    available source facts request.right scope.rightAvailable⟩

/-- Both original row operands satisfy the same independent source arity limit. -/
theorem edge_scope (source : State Symbol Guard) (facts : Facts source)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request) :
    Edge (limits source) request.left ∧ Edge (limits source) request.right :=
  ⟨(resident source facts request.left scope.leftResident).1,
    (resident source facts request.right scope.rightResident).1⟩

/-- Actual edge records retain their payload under record and issued-key growth. -/
theorem edge_read_grows (source current : State Symbol Guard) (growth : Grows source current)
    (history : Extends source.edges.issued current.edges.issued) (identity : Nat)
    (edge : EdgeValue Symbol Guard) (found : edgeRead source identity = some edge) :
    edgeRead current identity = some edge := by
  obtain ⟨key, issued, stored⟩ := Option.bind_eq_some_iff.mp found
  simp only [edgeRead, history identity key issued, Option.bind_some]
  exact growth.edgeRecords key edge stored

/-- A current read of an earlier payload retains its initial profile and syntax bound. -/
theorem read_current (source current : State Symbol Guard) (facts : Facts source)
    (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (identity : Nat) (original value : Value Symbol Guard)
    (captured : SourcePreparedSharedRows.read source identity = some original)
    (found : SourcePreparedSharedRows.read current identity = some value) :
    value = original ∧ Node (limits source) value ∧ sizeOf value ≤ nodeSize source := by
  have retained := SourceCurrentConstrainedCapSourceWeightTransport.read_grows
    source current growth history identity original captured
  have same := Option.some.inj (found.symm.trans retained)
  subst value
  exact ⟨rfl, read_bound source facts identity original captured, read_size source facts identity original captured⟩

/-- A current edge read retains its earlier exact ordered children and initial bounds. -/
theorem edge_read_current (source current : State Symbol Guard) (facts : Facts source)
    (growth : Grows source current) (history : Extends source.edges.issued current.edges.issued)
    (identity : Nat) (original edge : EdgeValue Symbol Guard)
    (captured : edgeRead source identity = some original)
    (found : edgeRead current identity = some edge) :
    edge = original ∧ Edge (limits source) edge ∧ sizeOf edge ≤ edgeSize source := by
  have retained := edge_read_grows source current growth history identity original captured
  have same := Option.some.inj (found.symm.trans retained)
  subst edge
  exact ⟨rfl, edge_read_bound source facts identity original captured, edge_read_size source facts identity original captured⟩

/-- Dereferencing an original binding returns the same bounded initial Mu payload. -/
theorem binding_read (source current : State Symbol Guard) (facts : Facts source) (currentFacts : Facts current)
    (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ value, SourcePreparedSharedRows.read current name = some value ∧
      Node (limits source) value ∧ sizeOf value ≤ nodeSize source ∧
      SourceRecursiveIntersectionInputView.Original value ∧ Available source value ∧
      SourceRecursiveIntersectionInputView.inputOf value = .mu name := by
  obtain ⟨value, found, original, known, input⟩ :=
    bindings.read source current currentFacts growth history domain name member
  have recorded : SourcePreparedSharedRows.reference value = some name := by
    cases value <;> simp_all [SourceRecursiveIntersectionInputView.inputOf, Value.referenceOf,
      IntersectionFlatMemoKey.input, SourcePreparedSharedRows.reference]
    case reference name => cases name <;> simp_all
  exact ⟨value, found, available source facts value known, available_size source facts value known name recorded,
    original, known, input⟩

end MicroCFTA.SourceRecursiveIntersectionSourceProfile
