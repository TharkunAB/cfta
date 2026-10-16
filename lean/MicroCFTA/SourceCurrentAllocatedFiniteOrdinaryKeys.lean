import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
import MicroCFTA.SourceRecursiveIntersectionEdgeMemo

/-!
# Initial finite ordinary operand keys

The certificates bound identities in complete initial operand records.
The word width is bits plus two. Guards and equality classes are unrestricted.
Coherent resident records derive the bounds from current cache counters.
No future trace, completed result, or later identity set is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryKeys
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedEdgeResidency
open InternedBinderProtocol
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {Symbol Guard : Type}

mutual
/-- Each ordinary node identity fits below its two-bit tag boundary. -/
inductive Node (bits : Nat) : Value Symbol Guard → Prop where
  | empty : Node bits .empty
  | ordinary (fits : entry.identity < 2 ^ bits) (rows : Rows bits edges) :
      Node bits (.node entry edges depth free)

/-- Each original row identity fits in the complete raw edge word. -/
inductive Rows (bits : Nat) : List (EdgeValue Symbol Guard) → Prop where
  | nil : Rows bits []
  | cons (fits : edge.entry.identity < 2 ^ (bits + 2))
      (children : Children bits edge.children) (rest : Rows bits edges) : Rows bits (edge :: edges)

/-- Each initial ordered child has the same recursive key certificate. -/
inductive Children (bits : Nat) : List (Value Symbol Guard) → Prop where
  | nil : Children bits []
  | cons (first : Node bits value) (rest : Children bits values) : Children bits (value :: values)
end

/-- A complete edge retains its raw identity bound and all original child keys. -/
def Edge (bits : Nat) (edge : EdgeValue Symbol Guard) : Prop :=
  edge.entry.identity < 2 ^ (bits + 2) ∧ Children bits edge.children

/-- Initial key certificates derive the finite ordinary domain independently of execution. -/
theorem Node.domain {bits : Nat} {value : Value Symbol Guard} (keys : Node bits value) : DNode value := by
  apply Node.rec
    (motive_1 := fun value _ => DNode value)
    (motive_2 := fun edges _ => DRows edges)
    (motive_3 := fun values _ => DChildren values) (t := keys)
  all_goals intros
  all_goals first
    | exact .empty
    | exact .ordinary ‹DRows _›
    | exact .nil
    | exact .cons ‹DChildren _› ‹DRows _›
    | exact .cons ‹DNode _› ‹DChildren _›

/-- Child membership retains the exact immutable initial record. -/
theorem Children.member {bits : Nat} {values : List (Value Symbol Guard)}
    (keys : Children bits values) (value : Value Symbol Guard) (member : value ∈ values) : Node bits value := by
  cases keys with
  | nil => cases member
  | cons first rest =>
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ first
      · exact rest.member value later
termination_by values.length

/-- Pointwise initial child bounds construct their ordered certificate. -/
theorem Children.of_members (bits : Nat) (values : List (Value Symbol Guard))
    (keys : ∀ value ∈ values, Node bits value) : Children bits values := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (keys value List.mem_cons_self) (ih (fun child member => keys child (List.mem_cons_of_mem _ member)))

/-- Every initial row retains both its raw word and recursive child bounds. -/
theorem Rows.member {bits : Nat} {edges : List (EdgeValue Symbol Guard)}
    (keys : Rows bits edges) (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) : Edge bits edge := by
  cases keys with
  | nil => cases member
  | cons fits children rest =>
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ ⟨fits, children⟩
      · exact rest.member edge later
termination_by edges.length

/-- Pointwise original row bounds construct their ordered certificate. -/
theorem Rows.of_members (bits : Nat) (edges : List (EdgeValue Symbol Guard))
    (keys : ∀ edge ∈ edges, Edge bits edge) : Rows bits edges := by
  induction edges with
  | nil => exact .nil
  | cons edge edges ih =>
      exact .cons (keys edge List.mem_cons_self).1 (keys edge List.mem_cons_self).2
        (ih (fun row member => keys row (List.mem_cons_of_mem _ member)))

/-- The actual ordinary rows retain the initial certificate. -/
theorem Node.rows {bits : Nat} {entry : Interned NodeKey} {edges : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List Reference} (keys : Node bits (.node entry edges depth free)) : Rows bits edges := by
  cases keys
  assumption

/-- Empty contributes no rows and ordinary nodes retain their literal rows. -/
theorem Node.nodeEdges {bits : Nat} {value : Value Symbol Guard} (keys : Node bits value) :
    Rows bits (InternedEdgeResidency.nodeEdges value) := by
  cases keys with
  | empty => exact .nil
  | ordinary _ rows => exact rows

/-- An original row child has the exact same initial key certificate. -/
theorem Node.child {bits : Nat} {value : Value Symbol Guard} (keys : Node bits value)
    (edge : EdgeValue Symbol Guard) (present : edge ∈ InternedEdgeResidency.nodeEdges value)
    (child : Value Symbol Guard) (member : child ∈ edge.children) : Node bits child :=
  (keys.nodeEdges.member edge present).2.member child member

/-- Ordered key children derive the finite ordinary child domain. -/
theorem Children.domain {bits : Nat} {values : List (Value Symbol Guard)} (keys : Children bits values) :
    DChildren values :=
  SourceCurrentAllocatedFiniteOrdinaryDomain.Children.of_members values (fun value member => (keys.member value member).domain)

/-- Ordered key rows derive the finite ordinary row domain. -/
theorem Rows.domain {bits : Nat} {edges : List (EdgeValue Symbol Guard)} (keys : Rows bits edges) : DRows edges :=
  SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members edges (fun edge member => (keys.member edge member).2.domain)

/-- Edge key bounds derive its complete finite ordinary child domain. -/
theorem Edge.domain {bits : Nat} {edge : EdgeValue Symbol Guard} (keys : Edge bits edge) : DEdge edge := keys.2.domain

/-- Every finite ordinary node has a present source encoding within the exact tagged range. -/
theorem Node.safe {bits : Nat} {value : Value Symbol Guard} (keys : Node bits value) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input ∧
      IntersectionFlatMemoKey.Safe (bits + 2) input := by
  cases keys with
  | empty => exact ⟨.empty, rfl, trivial⟩
  | ordinary fits _ => exact ⟨.node _, rfl, (IntersectionFlatMemoKey.safe_range bits _).1.mpr fits⟩

/-- A represented source encoding inherits the complete initial key bound. -/
theorem Node.safe_encoded {bits : Nat} {value : Value Symbol Guard} (keys : Node bits value)
    (input : IntersectSchedule.Input) (encoded : IntersectionFlatMemoKey.input value.referenceOf = some input) :
    IntersectionFlatMemoKey.Safe (bits + 2) input := by
  obtain ⟨actual, same, safe⟩ := keys.safe
  cases Option.some.inj (same.symm.trans encoded)
  exact safe

/-- An unchanged domain needs only its explicit signed nonnegative first-key bound. -/
theorem node_key_safe {bits : Nat} (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (bounded : domain.identity < 2 ^ (bits + 1))
    {left right : Value Symbol Guard} (first : Node bits left) (second : Node bits right) :
    SourceRecursiveIntersectionMemo.KeySafe (bits + 2) domain left right := by
  obtain ⟨a, leftInput, leftSafe⟩ := first.safe
  obtain ⟨b, rightInput, rightSafe⟩ := second.safe
  exact ⟨by omega, by simpa only [show bits + 2 - 1 = bits + 1 from by omega] using bounded,
    a, b, leftInput, rightInput, leftSafe, rightSafe⟩

/-- Empty-domain node requests need no domain allocation or future result bound. -/
theorem node_key_safe_empty {bits : Nat} {left right : Value Symbol Guard}
    (first : Node bits left) (second : Node bits right) :
    SourceRecursiveIntersectionMemo.KeySafe (bits + 2) IntersectionEmptyDomain.emptyDomain left right :=
  node_key_safe _ (Nat.two_pow_pos _) first second

/-- Both raw edge words remain safe in the same bounded domain. -/
theorem edge_key_safe {bits : Nat} (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (bounded : domain.identity < 2 ^ (bits + 1))
    {left right : EdgeValue Symbol Guard} (first : Edge bits left) (second : Edge bits right) :
    SourceRecursiveIntersectionEdgeMemo.KeySafe (bits + 2) domain left right :=
  ⟨by omega, by simpa only [show bits + 2 - 1 = bits + 1 from by omega] using bounded, first.1, second.1⟩

/-- Empty-domain edge requests retain the literal raw edge keys. -/
theorem edge_key_safe_empty {bits : Nat} {left right : EdgeValue Symbol Guard}
    (first : Edge bits left) (second : Edge bits right) :
    SourceRecursiveIntersectionEdgeMemo.KeySafe (bits + 2) IntersectionEmptyDomain.emptyDomain left right :=
  edge_key_safe _ (Nat.two_pow_pos _) first second

/-- Swapping original node operands retains their complete source key bounds. -/
theorem node_key_safe_swap {bits : Nat} (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (bounded : domain.identity < 2 ^ (bits + 1))
    {left right : Value Symbol Guard} (first : Node bits left) (second : Node bits right) :
    SourceRecursiveIntersectionMemo.KeySafe (bits + 2) domain right left :=
  (node_key_safe domain bounded first second).swap

/-- Swapping original rows retains both raw edge words. -/
theorem edge_key_safe_swap {bits : Nat} (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (bounded : domain.identity < 2 ^ (bits + 1))
    {left right : EdgeValue Symbol Guard} (first : Edge bits left) (second : Edge bits right) :
    SourceRecursiveIntersectionEdgeMemo.KeySafe (bits + 2) domain right left :=
  (edge_key_safe domain bounded first second).swap

/-- Current coherent linked inputs derive every recursive initial key from the two supplies. -/
theorem of_available (bits : Nat) (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (nodes : state.nodes.next ≤ 2 ^ bits) (edges : state.edges.next ≤ 2 ^ (bits + 2))
    (value : Value Symbol Guard) (available : Available state value) (domain : DNode value) : Node bits value := by
  induction available with
  | intro value resident issued children ih =>
      cases domain with
      | empty => exact .empty
      | @ordinary rows entry depth free rowDomains =>
          have stored := resident entry rfl
          obtain ⟨actual, canonical, fields⟩ := coherent.nodes entry.key _ stored
          have same : entry = actual := fields.1
          have nodeBelow : entry.identity < state.nodes.next := by
            rw [same]
            exact coherent.valid.2.1 actual.identity entry.key ((coherent.valid.2.2 entry.key actual canonical).2)
          apply Node.ordinary (Nat.lt_of_lt_of_le nodeBelow nodes)
          apply Rows.of_members bits rows
          intro edge member
          have rowResident := linked entry.key _ stored edge member
          have rowCanonical := (coherent.edges edge.entry.key edge rowResident).1
          have rowBelow : edge.entry.identity < state.edges.next :=
            coherent.valid.1.1 edge.entry.identity edge.entry.key
              ((coherent.valid.1.2 edge.entry.key edge.entry rowCanonical).2)
          refine ⟨Nat.lt_of_lt_of_le rowBelow edges, Children.of_members bits edge.children ?_⟩
          intro child present
          exact ih child (List.mem_flatMap.mpr ⟨edge, member, present⟩)
            ((rowDomains.member edge member).member child present)

/-- Available ordered input forests derive recursive bounds without a future heap. -/
theorem children_of_available (bits : Nat) (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (nodes : state.nodes.next ≤ 2 ^ bits) (edges : state.edges.next ≤ 2 ^ (bits + 2))
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available state value)
    (domain : DChildren values) : Children bits values :=
  Children.of_members bits values (fun value member =>
    of_available bits state coherent linked nodes edges value (available value member) (domain.member value member))

/-- A resident original row derives its raw identity and all actual child keys. -/
theorem of_resident (bits : Nat) (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (nodes : state.nodes.next ≤ 2 ^ bits) (edges : state.edges.next ≤ 2 ^ (bits + 2))
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident state edge) (domain : DEdge edge) : Edge bits edge := by
  have canonical := (facts.coherent.edges edge.entry.key edge resident).1
  have below : edge.entry.identity < state.edges.next :=
    facts.coherent.valid.1.1 edge.entry.identity edge.entry.key
      ((facts.coherent.valid.1.2 edge.entry.key edge.entry canonical).2)
  exact ⟨Nat.lt_of_lt_of_le below edges,
    children_of_available bits state facts.coherent facts.linked nodes edges edge.children
      (facts.cached.edges edge.entry.key edge resident) domain⟩

/-- Resident ordered rows derive all initial row and descendant bounds. -/
theorem rows_of_resident (bits : Nat) (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (nodes : state.nodes.next ≤ 2 ^ bits) (edges : state.edges.next ≤ 2 ^ (bits + 2))
    (rows : List (EdgeValue Symbol Guard)) (resident : ∀ edge ∈ rows, EdgeResident state edge)
    (domain : DRows rows) : Rows bits rows :=
  Rows.of_members bits rows (fun edge member =>
    of_resident bits state facts nodes edges edge (resident edge member) (domain.member edge member))

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryKeys
