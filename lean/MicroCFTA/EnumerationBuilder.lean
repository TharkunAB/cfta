import MicroCFTA.EnumerationInternedRows

/-!
# Finite memoized bounded-row construction

The builder visits the retained source children before it interns a parent.
The memo table stores the returned canonical identity. Equal row keys can
share an identity. All guarantees apply to keys reached by this finite run.
-/
namespace MicroCFTA.EnumerationBuilder
open EnumerationState EnumerationSemantics EnumerationSharedRows EnumerationInternedRows

abbrev Key := Nat × Nat

/-- Constructor rows retained by the source's shallow-depth filter. -/
def shallow (source : Nat → RowKey Symbol Guard) (remaining node : Nat) : RowKey Symbol Guard :=
  (source node).filter (fun edge => decide (0 < remaining) || edge.children.isEmpty)

/-- Ordered child requests made before one parent constructor. -/
def children (source : Nat → RowKey Symbol Guard) (remaining node : Nat) : List Nat :=
  (shallow source remaining node).flatMap Edge.children

/-- The dependencies of one memo key decrease its remaining height. -/
def dependencies (source : Nat → RowKey Symbol Guard) : Key → List Key
  | (0, _) => []
  | (remaining + 1, node) => (children source remaining node).map (remaining, ·)

/-- Runtime identities and memo keys occupy separate finite tables. -/
structure BuildState (Symbol Guard : Type) where
  cache : Cache.State (RowKey Symbol Guard)
  memo : Cache.Table Key Nat

/-- The fallback is read only outside the populated memo domain. -/
def encode (state : BuildState Symbol Guard) (key : Key) : Nat := (state.memo key).getD 0

/-- A completed memo key is in the scope of this finite construction. -/
def Scope (state : BuildState Symbol Guard) (key : Key) : Prop := ∃ identity, state.memo key = some identity

/-- Both tables retain every completed earlier entry. -/
def Grows (before after : BuildState Symbol Guard) : Prop :=
  Cache.Extends before.memo after.memo ∧ Cache.Extends before.cache.issued after.cache.issued

/-- Each completed memo entry has complete children and exact stored rows. -/
structure Valid (source : Nat → RowKey Symbol Guard) (state : BuildState Symbol Guard) : Prop where
  cache : Cache.Valid state.cache
  stored : StoredValid state.cache
  canonical : ∀ key identity, state.memo key = some identity →
    state.cache.table (lookup state.cache identity) = some ⟨identity, lookup state.cache identity⟩
  issued : ∀ key identity, state.memo key = some identity → ∃ rows, state.cache.issued identity = some rows
  ready : ∀ key, Scope state key → ∀ child ∈ dependencies source key, Scope state child
  readback : ∀ key identity, state.memo key = some identity →
    lookup state.cache identity = construct (encode state) (lookup state.cache) source key.1 key.2

/-- Empty tables satisfy the builder invariant without a source-language premise. -/
def empty : BuildState Symbol Guard := ⟨Cache.emptyState, fun _ => none⟩

theorem empty_valid (source : Nat → RowKey Symbol Guard) : Valid source empty := by
  constructor
  · exact Cache.empty_valid
  · intro identity key absent
    cases absent
  · intro key identity absent
    cases absent
  · intro key identity absent
    cases absent
  · rintro key ⟨identity, absent⟩
    cases absent
  · intro key identity absent
    cases absent

theorem grows_refl (state : BuildState Symbol Guard) : Grows state state :=
  ⟨Cache.extends_refl _, Cache.extends_refl _⟩

theorem grows_trans (first : Grows before middle) (second : Grows middle after) : Grows before after :=
  ⟨Cache.extends_trans first.1 second.1, Cache.extends_trans first.2 second.2⟩

theorem scope_grows (growth : Grows before after) (present : Scope before key) : Scope after key := by
  obtain ⟨identity, found⟩ := present
  exact ⟨identity, growth.1 key identity found⟩

theorem encode_grows (growth : Grows before after) (present : Scope before key) :
    encode before key = encode after key := by
  obtain ⟨identity, found⟩ := present
  simp [encode, found, growth.1 key identity found]

/-- One retained source child is in the actual ordered request list. -/
theorem child_dependency (source : Nat → RowKey Symbol Guard) (remaining node : Nat)
    (edge : Edge Symbol Guard) (member : edge ∈ shallow source remaining node)
    (child : Nat) (present : child ∈ edge.children) :
    (remaining, child) ∈ dependencies source (remaining + 1, node) := by
  exact List.mem_map.mpr ⟨child, List.mem_flatMap.mpr ⟨edge, member, present⟩, rfl⟩

/-- A constructor reads only the child identities and rows in its request list. -/
theorem construct_congr (source : Nat → RowKey Symbol Guard) (key : Key)
    (first second : Key → Nat) (left right : Nat → RowKey Symbol Guard)
    (identities : ∀ child ∈ dependencies source key, first child = second child)
    (rows : ∀ child ∈ dependencies source key, left (first child) = right (second child)) :
    construct first left source key.1 key.2 = construct second right source key.1 key.2 := by
  obtain ⟨height, node⟩ := key
  cases height with
  | zero => rfl
  | succ remaining =>
    have filters :
        (shallow source remaining node).filter (fun edge => edge.children.all (fun child => !(left (first (remaining, child))).isEmpty)) =
        (shallow source remaining node).filter (fun edge => edge.children.all (fun child => !(right (second (remaining, child))).isEmpty)) := by
      apply List.filter_congr
      intro edge member
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro kept child present
      · rw [← rows _ (child_dependency source remaining node edge member child present)]
        exact kept child present
      · rw [rows _ (child_dependency source remaining node edge member child present)]
        exact kept child present
    change List.map _ ((shallow source remaining node).filter _) = List.map _ ((shallow source remaining node).filter _)
    rw [filters]
    apply List.map_congr_left
    intro edge filtered
    have member := (List.mem_filter.mp filtered).1
    have mapped : edge.children.map (fun child => first (remaining, child)) = edge.children.map (fun child => second (remaining, child)) := by
      apply List.map_congr_left
      intro child present
      exact identities _ (child_dependency source remaining node edge member child present)
    simp only [EnumerationBoundedRows.copyEdge, mapped]

/-- Cache and memo growth cannot change a constructor whose children are complete. -/
theorem construct_grows (source : Nat → RowKey Symbol Guard) (key : Key)
    (before after : BuildState Symbol Guard) (valid : Valid source before) (growth : Grows before after)
    (ready : ∀ child ∈ dependencies source key, Scope before child) :
    construct (encode before) (lookup before.cache) source key.1 key.2 =
      construct (encode after) (lookup after.cache) source key.1 key.2 := by
  apply construct_congr
  · intro child member
    exact encode_grows growth (ready child member)
  · intro child member
    obtain ⟨identity, found⟩ := ready child member
    obtain ⟨rows, issued⟩ := valid.issued child identity found
    simpa [encode, found, growth.1 child identity found] using
      lookup_stable before.cache after.cache growth.2 identity rows issued

/-- Intern one completed constructor and retain the first memo result for its key. -/
def finish [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (key : Key) (state : BuildState Symbol Guard) : BuildState Symbol Guard :=
  let result := Cache.intern state.cache (construct (encode state) (lookup state.cache) source key.1 key.2)
  ⟨result.2, Cache.keepFirst state.memo key result.1.identity⟩

theorem finish_grows [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (key : Key) (state : BuildState Symbol Guard) (valid : Valid source state) :
    Grows state (finish source key state) :=
  ⟨Cache.keepFirst_extends _ _ _, intern_grows _ valid.cache _⟩

theorem finish_scope [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (key : Key) (state : BuildState Symbol Guard) : Scope (finish source key state) key :=
  Cache.keepFirst_present _ _ _

/-- A constructor insertion retains old memo entries and can add only its own key. -/
theorem finish_entries [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (key : Key) (state : BuildState Symbol Guard) (other : Key) (identity : Nat)
    (present : (finish source key state).memo other = some identity) :
    state.memo other = some identity ∨
      other = key ∧ identity = (Cache.intern state.cache
        (construct (encode state) (lookup state.cache) source key.1 key.2)).1.identity := by
  cases found : state.memo key with
  | some existing => exact Or.inl (by simpa [finish, Cache.keepFirst, found] using present)
  | none =>
    by_cases same : other = key
    · refine Or.inr ⟨same, ?_⟩
      simpa [finish, Cache.keepFirst, found, Cache.put, same] using present.symm
    · exact Or.inl (by simpa [finish, Cache.keepFirst, found, Cache.put, same] using present)

/-- Sequential interning retains every previously canonical table entry. -/
theorem intern_table_grows [DecidableEq (RowKey Symbol Guard)] (state : Cache.State (RowKey Symbol Guard))
    (key : RowKey Symbol Guard) : Cache.Extends state.table (Cache.intern state key).2.table := by
  cases found : state.table key with
  | some entry => simpa [Cache.intern, found] using Cache.extends_refl state.table
  | none => simpa [Cache.intern, found, Cache.install, Cache.reserve] using Cache.keepFirst_extends state.table key ⟨state.next, key⟩

/-- Complete children suffice to establish the next constructor invariant. -/
theorem finish_valid [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (key : Key) (state : BuildState Symbol Guard) (valid : Valid source state)
    (ready : ∀ child ∈ dependencies source key, Scope state child) : Valid source (finish source key state) := by
  have growth := finish_grows source key state valid
  have added := intern_readback state.cache valid.cache (construct (encode state) (lookup state.cache) source key.1 key.2)
  have current : construct (encode state) (lookup state.cache) source key.1 key.2 =
      construct (encode (finish source key state)) (lookup (finish source key state).cache) source key.1 key.2 :=
    construct_grows source key state _ valid growth ready
  constructor
  · exact (Cache.intern_correct _ _ valid.cache).1
  · exact intern_storedValid _ valid.stored _ (construct_valid _ _ source sourceValid _ _)
  · intro other identity present
    rcases finish_entries source key state other identity present with old | ⟨rfl, rfl⟩
    · obtain ⟨rows, issued⟩ := valid.issued other identity old
      rw [← lookup_stable state.cache _ growth.2 identity rows issued]
      exact intern_table_grows state.cache _ _ _ (valid.canonical other identity old)
    · have result := Cache.intern_correct state.cache
        (construct (encode state) (lookup state.cache) source other.1 other.2) valid.cache
      have rows : lookup (finish source other state).cache
          (Cache.intern state.cache (construct (encode state) (lookup state.cache) source other.1 other.2)).1.identity =
          construct (encode state) (lookup state.cache) source other.1 other.2 := by
        simp only [finish, lookup, added, Option.getD_some]
      have entry : (Cache.intern state.cache (construct (encode state) (lookup state.cache) source other.1 other.2)).1 =
          ⟨(Cache.intern state.cache (construct (encode state) (lookup state.cache) source other.1 other.2)).1.identity,
            construct (encode state) (lookup state.cache) source other.1 other.2⟩ := by
        have same := result.2.2
        cases found : (Cache.intern state.cache (construct (encode state) (lookup state.cache) source other.1 other.2)).1 with
        | mk identity rows =>
          simp only [found] at same ⊢
          cases same
          rfl
      rw [rows]
      exact result.2.1.trans (congrArg some entry)

  · intro other identity present
    rcases finish_entries source key state other identity present with old | ⟨rfl, rfl⟩
    · obtain ⟨rows, issued⟩ := valid.issued other identity old
      exact ⟨rows, growth.2 identity rows issued⟩
    · exact ⟨_, added⟩
  · rintro other ⟨identity, present⟩ child member
    rcases finish_entries source key state other identity present with old | ⟨rfl, same⟩
    · exact scope_grows growth (valid.ready other ⟨identity, old⟩ child member)
    · exact scope_grows growth (ready child member)
  · intro other identity present
    rcases finish_entries source key state other identity present with old | ⟨rfl, rfl⟩
    · obtain ⟨rows, issued⟩ := valid.issued other identity old
      rw [← lookup_stable state.cache _ growth.2 identity rows issued, valid.readback other identity old]
      exact construct_grows source other state _ valid growth (valid.ready other ⟨identity, old⟩)
    · change lookup (Cache.intern state.cache _).2 _ = _
      rw [lookup, added, Option.getD_some]
      exact current

/-- Visit a finite request list in its source order. -/
def visitMany (visit : Request → BuildState Symbol Guard → BuildState Symbol Guard) :
    List Request → BuildState Symbol Guard → BuildState Symbol Guard
  | [], state => state
  | request :: rest, state => visitMany visit rest (visit request state)

/-- Sequential child traversal preserves completed entries and reaches every child. -/
theorem visitMany_correct (source : Nat → RowKey Symbol Guard) (keyOf : Request → Key)
    (visit : Request → BuildState Symbol Guard → BuildState Symbol Guard)
    (correct : ∀ request state, Valid source state →
      Valid source (visit request state) ∧ Grows state (visit request state) ∧ Scope (visit request state) (keyOf request))
    (requests : List Request) (state : BuildState Symbol Guard) (valid : Valid source state) :
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

/-- Build one requested bound, with memo hits before ordered child traversal. -/
def build [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard) :
    Nat → Nat → BuildState Symbol Guard → BuildState Symbol Guard
  | 0, node, state =>
      match state.memo (0, node) with
      | some _ => state
      | none => finish source (0, node) state
  | remaining + 1, node, state =>
      match state.memo (remaining + 1, node) with
      | some _ => state
      | none =>
          finish source (remaining + 1, node)
            (visitMany (build source remaining) (children source remaining node) state)

/-- The executable builder establishes readback, child closure, and memo growth. -/
theorem build_correct [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (height node : Nat) (state : BuildState Symbol Guard) (valid : Valid source state) :
    Valid source (build source height node state) ∧ Grows state (build source height node state) ∧
      Scope (build source height node state) (height, node) := by
  induction height generalizing node state with
  | zero =>
    cases found : state.memo (0, node) with
    | some identity =>
      simp only [build, found]
      exact ⟨valid, grows_refl state, identity, found⟩
    | none =>
      simp only [build, found]
      exact ⟨finish_valid source sourceValid _ state valid (by simp [dependencies]),
        finish_grows source _ state valid, finish_scope source _ state⟩
  | succ remaining ih =>
    cases found : state.memo (remaining + 1, node) with
    | some identity =>
      simp only [build, found]
      exact ⟨valid, grows_refl state, identity, found⟩
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

/-- Build any finite collection of roots in one shared cache. -/
def buildAll [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (requests : List Key) : BuildState Symbol Guard :=
  visitMany (fun key => build source key.1 key.2) requests empty

/-- Every root in a finite request list is present in the final valid state. -/
theorem buildAll_correct [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge) (requests : List Key) :
    Valid source (buildAll source requests) ∧
      ∀ key ∈ requests, Scope (buildAll source requests) key := by
  obtain ⟨valid, _, present⟩ := visitMany_correct source id (fun key => build source key.1 key.2)
    (fun key state valid => build_correct source sourceValid key.1 key.2 state valid) requests empty (empty_valid source)
  exact ⟨valid, present⟩

/-- Requested roots have exact readback in the final shared cache. -/
theorem final_readback [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge) (requests : List Key)
    (key : Key) (member : key ∈ requests) :
    lookup (buildAll source requests).cache (encode (buildAll source requests) key) =
      construct (encode (buildAll source requests)) (lookup (buildAll source requests).cache) source key.1 key.2 := by
  obtain ⟨valid, reached⟩ := buildAll_correct source sourceValid requests
  obtain ⟨identity, present⟩ := reached key member
  simpa [encode, present] using valid.readback key identity present

/-- Completed memo keys share an identity exactly when their stored row keys agree. -/
theorem identities_equal_iff (source : Nat → RowKey Symbol Guard) (state : BuildState Symbol Guard)
    (valid : Valid source state) (left right : Key) (leftPresent : Scope state left) (rightPresent : Scope state right) :
    encode state left = encode state right ↔
      lookup state.cache (encode state left) = lookup state.cache (encode state right) := by
  obtain ⟨leftId, leftFound⟩ := leftPresent
  obtain ⟨rightId, rightFound⟩ := rightPresent
  simpa [encode, leftFound, rightFound] using Cache.identity_eq_iff_key_eq state.cache valid.cache
    (valid.canonical left leftId leftFound) (valid.canonical right rightId rightFound)

/-- The final cache issues only finitely many identities. -/
theorem final_cache_bounded [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge) (requests : List Key)
    (identity : Nat) (large : (buildAll source requests).cache.next ≤ identity) :
    (buildAll source requests).cache.issued identity = none := by
  have valid := (buildAll_correct source sourceValid requests).1.cache
  cases found : (buildAll source requests).cache.issued identity with
  | none => rfl
  | some rows => have small := valid.1 identity rows found; omega

/-- A finite list contains every memo key reached by one bounded traversal. -/
def closure (source : Nat → RowKey Symbol Guard) : Nat → Nat → List Key
  | 0, node => [(0, node)]
  | remaining + 1, node =>
      (children source remaining node).flatMap (closure source remaining) ++ [(remaining + 1, node)]

/-- A sequence cannot populate keys outside its initial domain and its finite visits. -/
theorem visitMany_scope (visit : Request → BuildState Symbol Guard → BuildState Symbol Guard)
    (keys : Request → List Key)
    (bounded : ∀ request state key, Scope (visit request state) key → Scope state key ∨ key ∈ keys request)
    (requests : List Request) (state : BuildState Symbol Guard) (key : Key)
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
theorem build_scope [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (height node : Nat) (state : BuildState Symbol Guard) (key : Key)
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
theorem scope_closure (source : Nat → RowKey Symbol Guard) (state : BuildState Symbol Guard)
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
theorem final_scope_exact [DecidableEq (RowKey Symbol Guard)] (source : Nat → RowKey Symbol Guard)
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

end MicroCFTA.EnumerationBuilder
