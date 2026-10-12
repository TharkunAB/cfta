import MicroCFTA.EnumerationBuilderCaches

/-!
# Finite bounded traversal through both concrete caches

The traversal uses the edge-cache pass and the sorted edge-identity node key.
Readback compares row membership, since source node construction changes row
order and removes duplicates. Canonical identities may still be shared.
-/
namespace MicroCFTA.EnumerationBuilderRuntime
open Language EnumerationState EnumerationSemantics EnumerationCorrectness EnumerationSharedRows EnumerationInternedRows
open EnumerationBuilder (Key shallow children dependencies closure)
open EnumerationBuilderCaches (Caches rows CanonicalNode)
open SymbolicGraphView

/-- A bounded traversal retains the two constructor caches and its memo table. -/
structure State (Symbol Guard : Type) where
  caches : Caches Symbol Guard
  memo : Cache.Table Key Nat

def encode (state : State Symbol Guard) (key : Key) : Nat := (state.memo key).getD 0

def Scope (state : State Symbol Guard) (key : Key) : Prop := ∃ identity, state.memo key = some identity

/-- All final readback and child-read obligations of a populated memo entry. -/
structure Valid (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard) : Prop where
  caches : EnumerationBuilderCaches.Valid state.caches
  checked : ∀ identity edge, state.caches.edges.issued identity = some edge → ValidEdge edge
  canonical : ∀ key identity, state.memo key = some identity → CanonicalNode state.caches identity
  ready : ∀ key, Scope state key → ∀ child ∈ dependencies source key, Scope state child
  readback : ∀ key identity, state.memo key = some identity → ∀ edge,
    edge ∈ rows state.caches identity ↔ edge ∈ construct (encode state) (rows state.caches) source key.1 key.2

/-- Cache and memo entries remain immutable after their first completed insertion. -/
structure Grows (before after : State Symbol Guard) : Prop where
  memo : Cache.Extends before.memo after.memo
  caches : EnumerationBuilderCaches.Grows before.caches after.caches

/-- The source starts each bounded traversal with an empty memo. -/
def empty : State Symbol Guard := ⟨⟨Cache.emptyState, Cache.emptyState⟩, fun _ => none⟩

theorem empty_valid (source : Nat → RowKey Symbol Guard) : Valid source empty := by
  constructor
  · exact ⟨Cache.empty_valid, Cache.empty_valid, by intro identity ids absent; cases absent⟩
  · intro identity edge absent; cases absent
  · intro key identity absent; cases absent
  · rintro key ⟨identity, absent⟩; cases absent
  · intro key identity absent; cases absent

theorem grows_refl (state : State Symbol Guard) : Grows state state :=
  ⟨Cache.extends_refl _, ⟨Cache.extends_refl _, Cache.extends_refl _, Cache.extends_refl _, Cache.extends_refl _⟩⟩

theorem grows_trans (first : Grows before middle) (second : Grows middle after) : Grows before after :=
  ⟨Cache.extends_trans first.memo second.memo,
    ⟨Cache.extends_trans first.caches.edgeIssued second.caches.edgeIssued,
      Cache.extends_trans first.caches.edgeTable second.caches.edgeTable,
      Cache.extends_trans first.caches.nodeIssued second.caches.nodeIssued,
      Cache.extends_trans first.caches.nodeTable second.caches.nodeTable⟩⟩

theorem scope_grows (growth : Grows before after) (present : Scope before key) : Scope after key := by
  obtain ⟨identity, found⟩ := present
  exact ⟨identity, growth.memo key identity found⟩

theorem encode_grows (growth : Grows before after) (present : Scope before key) : encode before key = encode after key := by
  obtain ⟨identity, found⟩ := present
  simp [encode, found, growth.memo key identity found]

/-- Cache growth retains the rows of every complete child used by this constructor. -/
theorem construct_grows (source : Nat → RowKey Symbol Guard) (key : Key)
    (before after : State Symbol Guard) (valid : Valid source before) (growth : Grows before after)
    (ready : ∀ child ∈ dependencies source key, Scope before child) :
    construct (encode before) (rows before.caches) source key.1 key.2 =
      construct (encode after) (rows after.caches) source key.1 key.2 := by
  apply EnumerationBuilder.construct_congr
  · intro child member
    exact encode_grows growth (ready child member)
  · intro child member
    obtain ⟨identity, found⟩ := ready child member
    simpa [encode, found, growth.memo child identity found] using
      EnumerationBuilderCaches.rows_stable before.caches after.caches valid.caches growth.caches identity (valid.canonical child identity found)

/-- Copy all retained source children before the node constructor removes empty edges. -/
def copied (source : Nat → RowKey Symbol Guard) (encode : Key → Nat) : Nat → Nat → RowKey Symbol Guard
  | 0, _ => []
  | remaining + 1, node => (shallow source remaining node).map (EnumerationBoundedRows.copyEdge encode remaining)

/-- The copied edge pass retains source equality-path validity. -/
theorem copied_valid (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (encode : Key → Nat) (height node : Nat) (edge : EnumerationState.Edge Symbol Guard)
    (member : edge ∈ copied source encode height node) : ValidEdge edge := by
  cases height with
  | zero => simp [copied] at member
  | succ remaining =>
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact EnumerationConstructors.setChildren_valid original _ (by simp)
      (sourceValid node original (List.mem_filter.mp present).1)

/-- The concrete EmptyNode test is the abstract empty-child row test at completed children. -/
theorem copied_retained (source : Nat → RowKey Symbol Guard) (key : Key)
    (state : State Symbol Guard) (valid : Valid source state)
    (ready : ∀ child ∈ dependencies source key, Scope state child) (edge : EnumerationState.Edge Symbol Guard) :
    (edge ∈ copied source (encode state) key.1 key.2 ∧ 0 ∉ edge.children) ↔
      edge ∈ construct (encode state) (rows state.caches) source key.1 key.2 := by
  obtain ⟨height, node⟩ := key
  cases height with
  | zero => simp [copied, construct]
  | succ remaining =>
    have test : ∀ original ∈ shallow source remaining node,
        (0 ∉ (EnumerationBoundedRows.copyEdge (encode state) remaining original).children) ↔
          original.children.all (fun child => !(rows state.caches (encode state (remaining, child))).isEmpty) = true := by
      intro original member
      have empties : ∀ child ∈ original.children,
          rows state.caches (encode state (remaining, child)) = [] ↔ encode state (remaining, child) = 0 := by
        intro child childMember
        obtain ⟨identity, found⟩ := ready _ (EnumerationBuilder.child_dependency source remaining node original member child childMember)
        simpa [encode, found] using EnumerationBuilderCaches.rows_empty_iff state.caches valid.caches identity
          (valid.canonical (remaining, child) identity found)
      simp only [EnumerationBoundedRows.copyEdge, List.mem_map, not_exists, not_and, List.all_eq_true,
        Bool.not_eq_true', List.isEmpty_eq_false_iff]
      constructor
      · intro noEmpty child childMember empty
        exact noEmpty child childMember ((empties child childMember).mp empty)
      · intro nonempty child childMember same
        exact nonempty child childMember ((empties child childMember).mpr same)
    constructor
    · rintro ⟨member, live⟩
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨original, List.mem_filter.mpr ⟨present, (test original present).mp live⟩, rfl⟩
    · intro member
      obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
      obtain ⟨present, live⟩ := List.mem_filter.mp filtered
      exact ⟨List.mem_map.mpr ⟨original, present, rfl⟩, (test original present).mpr live⟩

/-- Construct copied edges through both caches and record the canonical result. -/
def finish [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (key : Key) (state : State Symbol Guard) : State Symbol Guard :=
  let result := EnumerationBuilderCaches.construct (copied source (encode state) key.1 key.2) state.caches
  ⟨result.2, Cache.keepFirst state.memo key result.1⟩

theorem finish_grows [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (key : Key) (state : State Symbol Guard) (valid : Valid source state) : Grows state (finish source key state) :=
  ⟨Cache.keepFirst_extends _ _ _, EnumerationBuilderCaches.construct_grows _ _ valid.caches.edges valid.caches.nodes⟩

theorem finish_scope [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (key : Key) (state : State Symbol Guard) : Scope (finish source key state) key := Cache.keepFirst_present _ _ _

/-- A constructor can add only its own memo key. -/
theorem finish_entries [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (key : Key) (state : State Symbol Guard) (other : Key) (identity : Nat)
    (present : (finish source key state).memo other = some identity) :
    state.memo other = some identity ∨ other = key ∧
      identity = (EnumerationBuilderCaches.construct (copied source (encode state) key.1 key.2) state.caches).1 := by
  cases found : state.memo key with
  | some existing => exact Or.inl (by simpa [finish, Cache.keepFirst, found] using present)
  | none =>
    by_cases same : other = key
    · exact Or.inr ⟨same, by simpa [finish, Cache.keepFirst, found, Cache.put, same] using present.symm⟩
    · exact Or.inl (by simpa [finish, Cache.keepFirst, found, Cache.put, same] using present)

/-- Both concrete cache passes derive the new parent's scoped row equation. -/
theorem finish_valid [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (key : Key) (state : State Symbol Guard) (valid : Valid source state)
    (ready : ∀ child ∈ dependencies source key, Scope state child) : Valid source (finish source key state) := by
  have growth := finish_grows source key state valid
  have current := construct_grows source key state _ valid growth ready
  constructor
  · exact EnumerationBuilderCaches.construct_valid _ _ valid.caches
  · exact EnumerationBuilderCaches.construct_checked _ _ valid.checked (copied_valid source sourceValid _ _ _)
  · intro other identity present
    rcases finish_entries source key state other identity present with old | ⟨rfl, rfl⟩
    · exact EnumerationBuilderCaches.canonical_grows growth.caches (valid.canonical other identity old)
    · exact EnumerationBuilderCaches.construct_canonical _ _ valid.caches.nodes
  · rintro other ⟨identity, present⟩ child member
    rcases finish_entries source key state other identity present with old | ⟨rfl, _⟩
    · exact scope_grows growth (valid.ready other ⟨identity, old⟩ child member)
    · exact scope_grows growth (ready child member)
  · intro other identity present edge
    rcases finish_entries source key state other identity present with old | ⟨rfl, rfl⟩
    · rw [← EnumerationBuilderCaches.rows_stable state.caches _ valid.caches growth.caches identity (valid.canonical other identity old)]
      rw [valid.readback other identity old edge]
      rw [construct_grows source other state _ valid growth (valid.ready other ⟨identity, old⟩)]
    · change edge ∈ rows (EnumerationBuilderCaches.construct _ state.caches).2 _ ↔ _
      rw [EnumerationBuilderCaches.construct_rows _ _ valid.caches.edges valid.caches.nodes edge,
        copied_retained source other state valid ready edge, current]

/-- Visit ordered finite child lists without changing their source order. -/
def visitMany (visit : Request → State Symbol Guard → State Symbol Guard) : List Request → State Symbol Guard → State Symbol Guard
  | [], state => state
  | request :: rest, state => visitMany visit rest (visit request state)

theorem visitMany_correct (source : Nat → RowKey Symbol Guard) (keyOf : Request → Key)
    (visit : Request → State Symbol Guard → State Symbol Guard)
    (correct : ∀ request state, Valid source state →
      Valid source (visit request state) ∧ Grows state (visit request state) ∧ Scope (visit request state) (keyOf request))
    (requests : List Request) (state : State Symbol Guard) (valid : Valid source state) :
    Valid source (visitMany visit requests state) ∧ Grows state (visitMany visit requests state) ∧
      ∀ request ∈ requests, Scope (visitMany visit requests state) (keyOf request) := by
  induction requests generalizing state with
  | nil => exact ⟨valid, grows_refl _, by simp⟩
  | cons first rest ih =>
    obtain ⟨nextValid, nextGrowth, present⟩ := correct first state valid
    obtain ⟨lastValid, lastGrowth, reached⟩ := ih (visit first state) nextValid
    refine ⟨lastValid, grows_trans nextGrowth lastGrowth, ?_⟩
    intro request member
    rcases List.mem_cons.mp member with rfl | member
    · exact scope_grows lastGrowth present
    · exact reached request member

/-- The finite depth-first traversal uses the source's memo-before-children order. -/
def build [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard) :
    Nat → Nat → State Symbol Guard → State Symbol Guard
  | 0, node, state =>
      match state.memo (0, node) with
      | some _ => state
      | none => finish source (0, node) state
  | remaining + 1, node, state =>
      match state.memo (remaining + 1, node) with
      | some _ => state
      | none => finish source (remaining + 1, node)
          (visitMany (build source remaining) (children source remaining node) state)

/-- Finite traversal establishes canonical output, exact row membership, and child closure. -/
theorem build_correct [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (height node : Nat) (state : State Symbol Guard) (valid : Valid source state) :
    Valid source (build source height node state) ∧ Grows state (build source height node state) ∧
      Scope (build source height node state) (height, node) := by
  induction height generalizing node state with
  | zero =>
    cases found : state.memo (0, node) with
    | some identity => simp only [build, found]; exact ⟨valid, grows_refl state, identity, found⟩
    | none =>
      simp only [build, found]
      exact ⟨finish_valid source sourceValid _ state valid (by simp [dependencies]),
        finish_grows source _ state valid, finish_scope source _ state⟩
  | succ remaining ih =>
    cases found : state.memo (remaining + 1, node) with
    | some identity => simp only [build, found]; exact ⟨valid, grows_refl state, identity, found⟩
    | none =>
      simp only [build, found]
      obtain ⟨childrenValid, childrenGrowth, childrenReady⟩ :=
        visitMany_correct source (remaining, ·) (build source remaining) ih (children source remaining node) state valid
      have ready : ∀ child ∈ dependencies source (remaining + 1, node),
          Scope (visitMany (build source remaining) (children source remaining node) state) child := by
        intro child member
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact childrenReady original present
      exact ⟨finish_valid source sourceValid _ _ childrenValid ready,
        grows_trans childrenGrowth (finish_grows source _ _ childrenValid), finish_scope source _ _⟩

/-- Build a finite request batch with shared edge and node caches. -/
def buildAll [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (requests : List Key) : State Symbol Guard := visitMany (fun key => build source key.1 key.2) requests empty

theorem buildAll_correct [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge) (requests : List Key) :
    Valid source (buildAll source requests) ∧ ∀ key ∈ requests, Scope (buildAll source requests) key := by
  obtain ⟨valid, _, reached⟩ := visitMany_correct source id (fun key => build source key.1 key.2)
    (fun key state valid => build_correct source sourceValid key.1 key.2 state valid) requests empty (empty_valid source)
  exact ⟨valid, reached⟩

/-- Read concrete node-cache output as an enumeration graph. -/
def graph (state : State Symbol Guard) (meet : Nat → Nat → Nat) : Graph Symbol Guard where
  node identity := match rows state.caches identity with | [] => .empty | first :: rest => .alternatives (first :: rest)
  intersect := meet

theorem graph_rows (state : State Symbol Guard) (meet : Nat → Nat → Nat) (identity : Nat) :
    nodeRows (graph state meet) identity = rows state.caches identity := by
  cases found : rows state.caches identity <;> simp [nodeRows, graph, found]

/-- Every concrete row still has checked equality paths. -/
theorem rows_valid (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard)
    (valid : Valid source state) (identity : Nat) (edge : EnumerationState.Edge Symbol Guard)
    (member : edge ∈ rows state.caches identity) : ValidEdge edge := by
  cases identity with
  | zero => simp [rows] at member
  | succ identity =>
    obtain ⟨edgeId, _, issued⟩ := List.mem_filterMap.mp member
    exact valid.checked edgeId edge issued

/-- The concrete cache-derived graph meets every enumeration constructor invariant. -/
theorem complete (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard)
    (valid : Valid source state) (meet : Nat → Nat → Nat) : CompleteGraph (graph state meet) := by
  constructor
  · intro identity body
    cases found : rows state.caches identity <;> simp [graph, found]
  · intro identity edges view edge member
    have present : edge ∈ rows state.caches identity := by
      cases found : rows state.caches identity with
      | nil => simp [graph, found] at view
      | cons first rest =>
        simp only [graph, found, Node.alternatives.injEq] at view
        simpa only [view] using member
    exact rows_valid source state valid identity edge present

/-- Smart-constructor cleanup tests the rows of each copied child. -/
def keep (state : State Symbol Guard) (_ : Key) (edge : Language.Edge Key Other) : Bool :=
  edge.children.all (fun child => !(rows state.caches (encode state child)).isEmpty)

/-- A populated memo domain is closed under the bounded source graph. -/
theorem scope_closed (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard)
    (valid : Valid source state) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (present : Scope state key)
    (edge : Language.Edge Key Symbol)
    (member : edge ∈ BoundDepth.bound (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key)
    (child : Key) (childMember : child ∈ edge.children) : Scope state child := by
  apply valid.ready key present child
  obtain ⟨height, node⟩ := key
  cases height with
  | zero => simp [BoundDepth.bound] at member
  | succ remaining =>
    obtain ⟨base, filtered, rfl⟩ := List.mem_map.mp member
    obtain ⟨mapped, shallowMember⟩ := List.mem_filter.mp filtered
    obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp mapped
    obtain ⟨originalChild, inside, rfl⟩ := List.mem_map.mp childMember
    exact EnumerationBuilder.child_dependency source remaining node original
      (List.mem_filter.mpr ⟨sourceMember, shallowMember⟩) originalChild inside

/-- Final constructor rows are exactly the surviving renamed bounded source rows. -/
theorem scoped_members (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard)
    (valid : Valid source state) (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (present : Scope state key) (edge : Language.Edge Nat Symbol) :
    edge ∈ EnumerationLanguage.automaton (graph state meet) meaning (encode state key) ↔
      ∃ original ∈ BoundDepth.bound (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key,
        keep state key original = true ∧ edge = renameEdge (encode state) original := by
  obtain ⟨identity, found⟩ := present
  have readback : ∀ original, original ∈ rows state.caches (encode state key) ↔
      original ∈ construct (encode state) (rows state.caches) source key.1 key.2 := by
    intro original
    simpa [encode, found] using valid.readback key identity found original
  rw [EnumerationSharedRows.automaton_rows, graph_rows]
  have mapped : edge ∈ (rows state.caches (encode state key)).map (EnumerationLanguage.edgeView meaning) ↔
      edge ∈ (construct (encode state) (rows state.caches) source key.1 key.2).map (EnumerationLanguage.edgeView meaning) := by
    constructor
    · rintro member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨original, (readback original).mp present, rfl⟩
    · rintro member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨original, (readback original).mpr present, rfl⟩
  rw [mapped]
  obtain ⟨height, node⟩ := key
  cases height with
  | zero => simp [construct, BoundDepth.bound]
  | succ remaining =>
    constructor
    · intro member
      obtain ⟨bounded, listed, rfl⟩ := List.mem_map.mp member
      obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp listed
      obtain ⟨sourceFiltered, childrenKept⟩ := List.mem_filter.mp filtered
      obtain ⟨sourceMember, shallowMember⟩ := List.mem_filter.mp sourceFiltered
      refine ⟨BoundDepth.copyEdge remaining (EnumerationLanguage.edgeView meaning original), ?_, ?_,
        EnumerationBoundedRows.copy_view _ _ _ _⟩
      · exact List.mem_map.mpr ⟨EnumerationLanguage.edgeView meaning original,
          List.mem_filter.mpr ⟨List.mem_map.mpr ⟨original, sourceMember, rfl⟩, shallowMember⟩, rfl⟩
      · simpa [keep, BoundDepth.copyEdge, EnumerationLanguage.edgeView, List.all_map, Function.comp_def] using childrenKept
    · rintro ⟨original, member, kept, rfl⟩
      obtain ⟨base, filtered, rfl⟩ := List.mem_map.mp member
      obtain ⟨mapped, shallowMember⟩ := List.mem_filter.mp filtered
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp mapped
      rw [← EnumerationBoundedRows.copy_view]
      apply List.mem_map.mpr
      refine ⟨EnumerationBoundedRows.copyEdge (encode state) remaining original, ?_, rfl⟩
      apply List.mem_map.mpr
      refine ⟨original, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨sourceMember, shallowMember⟩, ?_⟩, rfl⟩
      simpa [keep, BoundDepth.copyEdge, EnumerationLanguage.edgeView, List.all_map, Function.comp_def] using kept

/-- A rejected row contains an empty final child, so no complete term is lost. -/
theorem scoped_rejected (state : State Symbol Guard) (meet : Nat → Nat → Nat)
    (meaning : Guard → Term Symbol → Prop) (key : Key) (edge : Language.Edge Key Symbol)
    (rejected : keep state key edge = false) :
    DropReason (EnumerationLanguage.automaton (graph state meet) meaning) (encode state) edge := by
  have empty : ∃ child ∈ edge.children, rows state.caches (encode state child) = [] := by
    simpa [keep] using rejected
  obtain ⟨child, member, absent⟩ := empty
  exact Or.inr ⟨child, member, by simp [automaton_rows, graph_rows, absent]⟩

/-- Every populated key has exactly its original language below the requested height. -/
theorem scoped_accepted_exact (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard)
    (valid : Valid source state) (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (present : Scope state key) (term : Term Symbol) :
    Accepted (graph state meet) meaning (encode state key) term ↔
      Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1 := by
  rw [EnumerationLanguage.accepted_iff _ _ (complete source state valid meet)]
  exact (EnumerationBuilder.normalized_exact_on
    (BoundDepth.bound (fun node => (source node).map (EnumerationLanguage.edgeView meaning)))
    (EnumerationLanguage.automaton (graph state meet) meaning) (encode state) (Scope state)
    (scope_closed source state valid meaning) (keep state)
    (scoped_members source state valid meet meaning)
    (fun _ _ _ _ rejected => scoped_rejected state meet meaning _ _ rejected) key present term).trans
    (BoundDepth.bound_exact _ key.1 key.2 term)

/-- A finite executable batch derives complete requested-root language equivalence. -/
theorem requested_accepted_exact [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge) (requests : List Key)
    (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (member : key ∈ requests) (term : Term Symbol) :
    Accepted (graph (buildAll source requests) meet) meaning (encode (buildAll source requests) key) term ↔
      Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1 := by
  obtain ⟨valid, reached⟩ := buildAll_correct source sourceValid requests
  exact scoped_accepted_exact source _ valid meet meaning key (reached key member) term

/-- A sequence cannot populate keys outside its initial domain and its finite visits. -/
theorem visitMany_scope (visit : Request → State Symbol Guard → State Symbol Guard)
    (keys : Request → List Key)
    (bounded : ∀ request state key, Scope (visit request state) key → Scope state key ∨ key ∈ keys request)
    (requests : List Request) (state : State Symbol Guard) (key : Key)
    (present : Scope (visitMany visit requests state) key) :
    Scope state key ∨ key ∈ requests.flatMap keys := by
  induction requests generalizing state with
  | nil => exact Or.inl present
  | cons first rest ih =>
    rcases ih (visit first state) present with earlier | later
    · rcases bounded first state key earlier with original | new
      · exact Or.inl original
      · exact Or.inr (by simp [new])
    · exact Or.inr (by simp [later])

/-- Every memo insertion belongs to the finite child traversal of its requested root. -/
theorem build_scope [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (height node : Nat) (state : State Symbol Guard) (key : Key)
    (present : Scope (build source height node state) key) :
    Scope state key ∨ key ∈ closure source height node := by
  induction height generalizing node state key with
  | zero =>
    cases found : state.memo (0, node) with
    | some identity => exact Or.inl (by simpa [build, found] using present)
    | none =>
      obtain ⟨identity, issued⟩ := present
      have atFinish : (finish source (0, node) state).memo key = some identity := by simpa [build, found] using issued
      rcases finish_entries source (0, node) state key identity atFinish with old | ⟨same, _⟩
      · exact Or.inl ⟨identity, old⟩
      · exact Or.inr (by simp [closure, same])
  | succ remaining ih =>
    cases found : state.memo (remaining + 1, node) with
    | some identity => exact Or.inl (by simpa [build, found] using present)
    | none =>
      obtain ⟨identity, issued⟩ := present
      have atFinish : (finish source (remaining + 1, node)
          (visitMany (build source remaining) (children source remaining node) state)).memo key = some identity := by
        simpa [build, found] using issued
      rcases finish_entries source (remaining + 1, node) _ key identity atFinish with old | ⟨same, _⟩
      · have earlier := visitMany_scope (build source remaining) (closure source remaining)
          (fun child before other => ih child before other) (children source remaining node) state key ⟨identity, old⟩
        rcases earlier with original | inChildren
        · exact Or.inl original
        · exact Or.inr (by simp [closure, inChildren])
      · exact Or.inr (by simp [closure, same])

/-- A completed root already contains all keys that a repeated traversal could read. -/
theorem scope_closure (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard)
    (valid : Valid source state) (height node : Nat) (present : Scope state (height, node))
    (key : Key) (member : key ∈ closure source height node) : Scope state key := by
  induction height generalizing node with
  | zero =>
    have same : key = (0, node) := by simpa [closure] using member
    exact same ▸ present
  | succ remaining ih =>
    rcases List.mem_append.mp member with below | root
    · obtain ⟨child, childMember, member⟩ := List.mem_flatMap.mp below
      have childReady := valid.ready (remaining + 1, node) present (remaining, child)
        (List.mem_map.mpr ⟨child, childMember, rfl⟩)
      exact ih child childReady member
    · have same : key = (remaining + 1, node) := by simpa using root
      exact same ▸ present

/-- The final memo domain is exactly the finite union of the requested child traversals. -/
theorem final_scope_exact [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge) (requests : List Key) (key : Key) :
    Scope (buildAll source requests) key ↔
      key ∈ requests.flatMap (fun root => closure source root.1 root.2) := by
  constructor
  · intro present
    have bounded := visitMany_scope (fun (root : Key) => build source root.1 root.2)
      (fun root => closure source root.1 root.2)
      (fun root state key => build_scope source root.1 root.2 state key) requests empty key present
    rcases bounded with ⟨identity, impossible⟩ | included
    · cases impossible
    · exact included
  · intro included
    obtain ⟨root, requested, member⟩ := List.mem_flatMap.mp included
    obtain ⟨valid, reached⟩ := buildAll_correct source sourceValid requests
    exact scope_closure source _ valid root.1 root.2 (reached root requested) key member

/-- Zero height and source EmptyNode are the source's terminal fast paths. -/
def terminal (source : Nat → RowKey Symbol Guard) (key : Key) : Bool :=
  decide (key.1 = 0) || (source key.2).isEmpty

/-- Terminal constructor requests have no copied edges. -/
theorem terminal_copied (source : Nat → RowKey Symbol Guard) (key : Key) (encode : Key → Nat)
    (isTerminal : terminal source key = true) : copied source encode key.1 key.2 = [] := by
  obtain ⟨height, node⟩ := key
  cases height with
  | zero => rfl
  | succ remaining =>
    have absent : source node = [] := by simpa [terminal] using isTerminal
    simp [copied, shallow, absent]

/-- Terminal row construction accepts no edge. -/
theorem terminal_construct (source : Nat → RowKey Symbol Guard) (key : Key)
    (encode : Key → Nat) (read : Nat → RowKey Symbol Guard) (isTerminal : terminal source key = true) :
    construct encode read source key.1 key.2 = [] := by
  obtain ⟨height, node⟩ := key
  cases height with
  | zero => rfl
  | succ remaining =>
    have absent : source node = [] := by simpa [terminal] using isTerminal
    simp [construct, absent]

/-- A terminal memo entry always records the distinguished EmptyNode reference. -/
theorem terminal_reference (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard)
    (valid : Valid source state) (key : Key) (isTerminal : terminal source key = true)
    (identity : Nat) (present : state.memo key = some identity) : identity = 0 := by
  have empty : rows state.caches identity = [] := by
    cases found : rows state.caches identity with
    | nil => rfl
    | cons edge rest =>
      have retained := (valid.readback key identity present edge).mp (by simp [found])
      rw [terminal_construct source key _ _ isTerminal] at retained
      cases retained
  exact (EnumerationBuilderCaches.rows_empty_iff state.caches valid.caches identity (valid.canonical key identity present)).mp empty

/-- Remove only terminal memo records; both constructor caches remain unchanged. -/
def elide (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard) : State Symbol Guard :=
  {state with memo := fun key => if terminal source key then none else state.memo key}

/-- Default EmptyNode readback makes terminal memo entries observationally redundant. -/
theorem encode_elide (source : Nat → RowKey Symbol Guard) (state : State Symbol Guard) (valid : Valid source state)
    (key : Key) : encode (elide source state) key = encode state key := by
  cases isTerminal : terminal source key with
  | false => simp [elide, encode, isTerminal]
  | true =>
    cases found : state.memo key with
    | none => simp [elide, encode, isTerminal, found]
    | some identity =>
      have zero := terminal_reference source state valid key isTerminal identity found
      simp [elide, encode, isTerminal, found, zero]

/-- The terminal constructor step allocates neither an edge nor a node. -/
theorem finish_terminal_caches [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (key : Key) (state : State Symbol Guard)
    (isTerminal : terminal source key = true) : (finish source key state).caches = state.caches := by
  simp [finish, terminal_copied source key _ isTerminal, EnumerationBuilderCaches.construct,
    EnumerationBuilderCaches.internAll, EnumerationBuilderCaches.surviving, EnumerationBuilderCaches.canonicalIds]

/-- Removing terminal memo entries preserves every requested root's complete bounded language. -/
theorem elided_requested_exact [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (requests : List Key) (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (member : key ∈ requests) (term : Term Symbol) :
    Accepted (graph (elide source (buildAll source requests)) meet) meaning
        (encode (elide source (buildAll source requests)) key) term ↔
      Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1 := by
  rw [encode_elide source _ (buildAll_correct source sourceValid requests).1]
  exact requested_accepted_exact source sourceValid requests meet meaning key member term

end MicroCFTA.EnumerationBuilderRuntime
