import MicroCFTA.SymbolicStructuralBudget
import MicroCFTA.Cache

/-!
# Pure interned constructor graph readback

Issued identities name immutable row keys. A new nonrecursive key can refer
only to child identities that were already issued. The allocation supply then
gives a topological rank. Concurrent table growth preserves every old closed
graph language. Hashing, unsafe casts, recursive thunks, and machine integer
overflow remain runtime representation boundaries.
-/
namespace MicroCFTA.SymbolicInternedView
open Language Cache

/-- Read immutable constructor rows by their reserved identity. -/
def rows (shape : Key → List (Language.Edge Nat Symbol)) (state : Cache.State Key) : Automaton Nat Symbol :=
  fun identity => match state.issued identity with
    | none => []
    | some key => shape key

/-- A new constructor key refers only to identities already available. -/
def ChildrenIssued (shape : Key → List (Language.Edge Nat Symbol)) (state : Cache.State Key) (key : Key) : Prop :=
  ∀ edge ∈ shape key, ∀ child ∈ edge.children, ∃ childKey, state.issued child = some childKey

/-- Every issued constructor graph is closed and its children have earlier identities. -/
def Acyclic (shape : Key → List (Language.Edge Nat Symbol)) (state : Cache.State Key) : Prop :=
  ∀ identity key, state.issued identity = some key →
    ∀ edge ∈ shape key, ∀ child ∈ edge.children,
      child < identity ∧ ∃ childKey, state.issued child = some childKey

/-- An empty cache contains no graph references. -/
theorem empty_acyclic (shape : Key → List (Language.Edge Nat Symbol)) : Acyclic shape Cache.emptyState := by
  intro identity key impossible
  cases impossible

/-- Reservation preserves acyclicity when all children already exist. -/
theorem reserve_acyclic (shape : Key → List (Language.Edge Nat Symbol)) (state : Cache.State Key)
    (valid : Cache.Valid state) (acyclic : Acyclic shape state) (key : Key)
    (children : ChildrenIssued shape state key) : Acyclic shape (Cache.reserve state key).2 := by
  intro identity stored issued edge member child present
  by_cases fresh : identity = state.next
  · subst identity
    have same : key = stored := by simpa [Cache.reserve] using issued
    subst stored
    obtain ⟨childKey, found⟩ := children edge member child present
    exact ⟨valid.1 child childKey found, childKey, Cache.reserve_extends state key valid child childKey found⟩
  · have old : state.issued identity = some stored := by simpa [Cache.reserve, fresh] using issued
    obtain ⟨earlier, childKey, found⟩ := acyclic identity stored old edge member child present
    exact ⟨earlier, childKey, Cache.reserve_extends state key valid child childKey found⟩

/-- Installing the canonical winner does not change any reserved graph rows. -/
theorem install_acyclic [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol))
    (state : Cache.State Key) (candidate : Cache.Interned Key) (acyclic : Acyclic shape state) :
    Acyclic shape (Cache.install state candidate) := acyclic

/-- Sequential interning retains the allocation-derived topological order. -/
theorem intern_acyclic [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol))
    (state : Cache.State Key) (valid : Cache.Valid state) (acyclic : Acyclic shape state)
    (key : Key) (children : ChildrenIssued shape state key) : Acyclic shape (Cache.intern state key).2 := by
  cases found : state.table key with
  | some entry => simpa [Cache.intern, found] using acyclic
  | none =>
    simpa only [Cache.intern, found] using
      install_acyclic shape (Cache.reserve state key).2 (Cache.reserve state key).1
        (reserve_acyclic shape state valid acyclic key children)

/-- Canonical readback returns exactly the rows of the requested key. -/
theorem intern_rows [DecidableEq Key] (shape : Key → List (Language.Edge Nat Symbol))
    (state : Cache.State Key) (valid : Cache.Valid state) (key : Key) :
    rows shape (Cache.intern state key).2 (Cache.intern state key).1.identity = shape key := by
  obtain ⟨safe, stored, _⟩ := Cache.intern_correct state key valid
  have issued := (safe.2 key _ stored).2
  simp [rows, issued]

/-- Every constructor child strictly decreases the numeric identity rank. -/
theorem rows_rank (shape : Key → List (Language.Edge Nat Symbol)) (state : Cache.State Key)
    (acyclic : Acyclic shape state) (identity : Nat) (edge : Language.Edge Nat Symbol)
    (member : edge ∈ rows shape state identity) (child : Nat) (present : child ∈ edge.children) :
    child < identity := by
  cases found : state.issued identity with
  | none => simp [rows, found] at member
  | some key => exact (acyclic identity key found edge (by simpa [rows, found] using member) child present).1

/-- Every child of an existing row is available in the same immutable graph view. -/
theorem rows_closed (shape : Key → List (Language.Edge Nat Symbol)) (state : Cache.State Key)
    (acyclic : Acyclic shape state) (identity : Nat) (edge : Language.Edge Nat Symbol)
    (member : edge ∈ rows shape state identity) (child : Nat) (present : child ∈ edge.children) :
    ∃ childKey, state.issued child = some childKey := by
  cases found : state.issued identity with
  | none => simp [rows, found] at member
  | some key => exact (acyclic identity key found edge (by simpa [rows, found] using member) child present).2

/-- Later reservations preserve all earlier row readbacks. -/
theorem rows_stable (shape : Key → List (Language.Edge Nat Symbol)) (before after : Cache.State Key)
    (growth : Cache.Extends before.issued after.issued) (identity : Nat) (key : Key)
    (issued : before.issued identity = some key) : rows shape before identity = rows shape after identity := by
  simp [rows, issued, growth identity key issued]

/-- Transform child runs with a proof available at every actual source child. -/
theorem all₂_scoped_imp (first second : NodeType → Value → Prop) (states : List NodeType) (values : List Value)
    (runs : All₂ first states values)
    (change : ∀ state ∈ states, ∀ value ∈ values, first state value → second state value) :
    All₂ second states values := by
  induction runs with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (change _ (by simp) _ (by simp) head)
      (ih (fun state member value present => change state (by simp [member]) value (by simp [present])))

/-- Reading any later cache snapshot preserves the entire old closed graph language. -/
theorem growth_exact (shape : Key → List (Language.Edge Nat Symbol)) (before after : Cache.State Key)
    (growth : Cache.Extends before.issued after.issued) (acyclic : Acyclic shape before)
    (identity : Nat) (key : Key) (issued : before.issued identity = some key) (term : Term Symbol) :
    Accepts (rows shape after) identity term ↔ Accepts (rows shape before) identity term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ identity key, before.issued identity = some key →
      (Accepts (rows shape after) identity term ↔ Accepts (rows shape before) identity term))
    generalizing identity key with
  | node symbol children ih =>
    rw [accepts_node_iff, accepts_node_iff, ← rows_stable shape before after growth identity key issued]
    have convertRuns : ∀ edge ∈ rows shape before identity,
        All₂ (Accepts (rows shape after)) edge.children children ↔
          All₂ (Accepts (rows shape before)) edge.children children := by
      intro edge member
      have every : ∀ child ∈ edge.children, ∀ tree ∈ children,
          Accepts (rows shape after) child tree ↔ Accepts (rows shape before) child tree := by
        intro child present tree memberTree
        obtain ⟨childKey, found⟩ := rows_closed shape before acyclic identity edge member child present
        exact ih tree memberTree child childKey found
      constructor
      · intro runs
        exact all₂_scoped_imp _ _ _ _ runs (fun child present tree memberTree =>
          (every child present tree memberTree).mp)
      · intro runs
        exact all₂_scoped_imp _ _ _ _ runs (fun child present tree memberTree =>
          (every child present tree memberTree).mpr)
    constructor
    · rintro ⟨edge, member, label, runs, guard⟩
      exact ⟨edge, member, label, (convertRuns edge member).mp runs, guard⟩
    · rintro ⟨edge, member, label, runs, guard⟩
      exact ⟨edge, member, label, (convertRuns edge member).mpr runs, guard⟩
  | nil => simp_all
  | cons first rest head tail =>
    rename_i term member identity key issued
    rcases List.mem_cons.mp member with rfl | member
    · exact head identity key issued
    · exact tail term member identity key issued

end MicroCFTA.SymbolicInternedView
