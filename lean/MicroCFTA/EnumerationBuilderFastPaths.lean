import MicroCFTA.EnumerationBuilderRuntime

/-!
# Source terminal memo fast paths

The source returns EmptyNode before it reads or writes the memo at an empty
source node or a negative depth. The fast builder follows that order. Its
complete result is the concrete builder with terminal memo entries removed.
-/
namespace MicroCFTA.EnumerationBuilderRuntime
open Language EnumerationState EnumerationSemantics EnumerationCorrectness EnumerationInternedRows
open EnumerationBuilder (Key children closure)

/-- A terminal step disappears when terminal memo records are removed. -/
theorem elide_finish_terminal [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (key : Key) (state : State Symbol Guard)
    (isTerminal : terminal source key = true) : elide source (finish source key state) = elide source state := by
  simp only [finish, terminal_copied source key _ isTerminal]
  simp only [EnumerationBuilderCaches.construct, EnumerationBuilderCaches.internAll,
    EnumerationBuilderCaches.surviving, List.filter_nil, List.map_nil, EnumerationBuilderCaches.canonicalIds,
    List.eraseDups_nil, List.mergeSort_nil]
  apply congrArg (State.mk state.caches)
  funext other
  cases test : terminal source other with
  | true => rfl
  | false =>
    have different : other ≠ key := by intro same; subst other; simp_all
    cases found : state.memo key <;> simp [Cache.keepFirst, found, Cache.put, different]

/-- A nonterminal constructor commutes with removal of terminal memo records. -/
theorem elide_finish [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (key : Key) (state : State Symbol Guard)
    (valid : Valid source state) (notTerminal : terminal source key = false) :
    elide source (finish source key state) = finish source key (elide source state) := by
  have encoded : encode (elide source state) = encode state := funext (encode_elide source state valid)
  simp only [finish, encoded]
  apply congrArg (State.mk _)
  funext other
  by_cases same : other = key
  · subst other
    cases found : state.memo key <;> simp [elide, notTerminal, Cache.keepFirst, found, Cache.put]
  · cases test : terminal source other <;> cases found : state.memo key <;>
      simp [elide, notTerminal, test, Cache.keepFirst, found, Cache.put, same]

/-- Use the source EmptyNode and negative-depth exits before memo lookup. -/
def fastBuild [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard) :
    Nat → Nat → State Symbol Guard → State Symbol Guard
  | 0, _, state => state
  | remaining + 1, node, state =>
      if (source node).isEmpty then state else
        match state.memo (remaining + 1, node) with
        | some _ => state
        | none => finish source (remaining + 1, node)
            (visitMany (fastBuild source remaining) (children source remaining node) state)

/-- A per-request memo-elision simulation composes over the complete ordered traversal. -/
theorem visitMany_elide (source : Nat → RowKey Symbol Guard)
    (slow fast : Request → State Symbol Guard → State Symbol Guard)
    (preserves : ∀ request state, Valid source state → Valid source (slow request state))
    (simulates : ∀ request state, Valid source state → fast request (elide source state) = elide source (slow request state))
    (requests : List Request) (state : State Symbol Guard) (valid : Valid source state) :
    visitMany fast requests (elide source state) = elide source (visitMany slow requests state) := by
  induction requests generalizing state with
  | nil => rfl
  | cons first rest ih =>
    simp only [visitMany, simulates first state valid]
    exact ih _ (preserves first state valid)

/-- The source fast paths remove only redundant terminal memo records from the complete run. -/
theorem fastBuild_exact [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (height node : Nat) (state : State Symbol Guard) (valid : Valid source state) :
    fastBuild source height node (elide source state) = elide source (build source height node state) := by
  induction height generalizing node state with
  | zero =>
    cases found : state.memo (0, node) with
    | some identity => simp [fastBuild, build, found]
    | none =>
      simp only [fastBuild, build, found]
      exact (elide_finish_terminal source (0, node) state (by simp [terminal])).symm
  | succ remaining ih =>
    cases isEmpty : (source node).isEmpty with
    | true =>
      have absent : source node = [] := by simpa using isEmpty
      cases found : state.memo (remaining + 1, node) with
      | some identity => simp [fastBuild, isEmpty, build, found]
      | none =>
        simp only [fastBuild, isEmpty, ↓reduceIte, build, found]
        simp only [children, EnumerationBuilder.shallow, absent, List.filter_nil, List.flatMap_nil, visitMany]
        exact (elide_finish_terminal source (remaining + 1, node) state (by simp [terminal, absent])).symm
    | false =>
      have notTerminal : terminal source (remaining + 1, node) = false := by simp [terminal, isEmpty]
      have memo : (elide source state).memo (remaining + 1, node) = state.memo (remaining + 1, node) := by simp [elide, notTerminal]
      cases found : state.memo (remaining + 1, node) with
      | some identity => simp [fastBuild, isEmpty, memo, build, found]
      | none =>
        simp only [fastBuild, isEmpty, Bool.false_eq_true, ↓reduceIte, memo, found, build]
        rw [visitMany_elide source (build source remaining) (fastBuild source remaining)
          (fun child before checked => (build_correct source sourceValid remaining child before checked).1)
          ih (children source remaining node) state valid]
        have childValid := (visitMany_correct source (remaining, ·) (build source remaining)
          (fun child before checked => build_correct source sourceValid remaining child before checked)
          (children source remaining node) state valid).1
        exact (elide_finish source (remaining + 1, node) _ childValid notTerminal).symm

/-- Build requested roots with the exact terminal memo fast paths. -/
def fastBuildAll [DecidableEq (EnumerationState.Edge Symbol Guard)] (source : Nat → RowKey Symbol Guard)
    (requests : List Key) : State Symbol Guard := visitMany (fun key => fastBuild source key.1 key.2) requests empty

/-- The complete fast batch retains both exact caches and every nonterminal memo result. -/
theorem fastBuildAll_exact [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (requests : List Key) : fastBuildAll source requests = elide source (buildAll source requests) := by
  have simulation := visitMany_elide source (fun (key : Key) => build source key.1 key.2)
    (fun key => fastBuild source key.1 key.2)
    (fun key state valid => (build_correct source sourceValid key.1 key.2 state valid).1)
    (fun key state valid => fastBuild_exact source sourceValid key.1 key.2 state valid) requests empty (empty_valid source)
  simpa [fastBuildAll, buildAll, elide, empty] using simulation

/-- Every fast-built requested root has exactly the original bounded finite language. -/
theorem fast_requested_exact [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (requests : List Key) (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (member : key ∈ requests) (term : Term Symbol) :
    Accepted (graph (fastBuildAll source requests) meet) meaning (encode (fastBuildAll source requests) key) term ↔
      Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1 := by
  rw [fastBuildAll_exact source sourceValid requests]
  exact elided_requested_exact source sourceValid requests meet meaning key member term

/-- The fast memo domain contains exactly the nonterminal visited keys. -/
theorem fast_scope_exact [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (requests : List Key) (key : Key) :
    Scope (fastBuildAll source requests) key ↔
      key ∈ requests.flatMap (fun root => closure source root.1 root.2) ∧ terminal source key = false := by
  rw [fastBuildAll_exact source sourceValid requests]
  cases test : terminal source key with
  | true => simp [Scope, elide, test]
  | false =>
    simpa [Scope, elide, test] using final_scope_exact source sourceValid requests key

/-- Every requested key has exact copied-row membership after the source fast paths. -/
theorem fast_requested_readback [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (requests : List Key) (key : Key) (member : key ∈ requests) (edge : EnumerationState.Edge Symbol Guard) :
    edge ∈ EnumerationBuilderCaches.rows (fastBuildAll source requests).caches (encode (fastBuildAll source requests) key) ↔
      edge ∈ EnumerationSharedRows.construct (encode (fastBuildAll source requests))
        (EnumerationBuilderCaches.rows (fastBuildAll source requests).caches) source key.1 key.2 := by
  obtain ⟨valid, reached⟩ := buildAll_correct source sourceValid requests
  obtain ⟨identity, found⟩ := reached key member
  have encoded : encode (elide source (buildAll source requests)) = encode (buildAll source requests) :=
    funext (encode_elide source _ valid)
  rw [fastBuildAll_exact source sourceValid requests, encoded]
  simpa [elide, encode, found] using valid.readback key identity found edge

/-- Source-style cache construction discharges the complete enumeration driver's row adapter. -/
theorem fast_requested_runs_exact [DecidableEq Symbol] [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (requests : List Key) (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (intersection : EnumerationIntersection.HashRows
      (EnumerationLanguage.automaton (graph (fastBuildAll source requests) meet) meaning) meet)
    (marker : Symbol) (key : Key) (member : key ∈ requests) (term : Term Symbol) :
    (Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1) ↔
      ∃ fuel pending after, .ok ((term, pending), after) ∈
        runs (graph (fastBuildAll source requests) meet) marker fuel (encode (fastBuildAll source requests) key) ∧
        ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  have graphEq : graph (fastBuildAll source requests) meet = graph (buildAll source requests) meet := by
    rw [fastBuildAll_exact source sourceValid requests]
    rfl
  have completeFast : CompleteGraph (graph (fastBuildAll source requests) meet) := by
    rw [graphEq]
    exact complete source _ (buildAll_correct source sourceValid requests).1 meet
  rw [← fast_requested_exact source sourceValid requests meet meaning key member term]
  exact EnumerationExact.runs_exact _ meaning completeFast
    (EnumerationIntersection.intersection_correct _ meaning completeFast intersection) marker _ term

/-- An empty memo can reuse any valid preexisting global edge and node caches. -/
theorem initial_valid (source : Nat → RowKey Symbol Guard) (caches : EnumerationBuilderCaches.Caches Symbol Guard)
    (valid : EnumerationBuilderCaches.Valid caches)
    (checked : ∀ identity edge, caches.edges.issued identity = some edge → ValidEdge edge) :
    Valid source ⟨caches, fun _ => none⟩ := by
  constructor
  · exact valid
  · exact checked
  · intro key identity absent; cases absent
  · rintro key ⟨identity, absent⟩; cases absent
  · intro key identity absent; cases absent

/-- A finite fast traversal can share preexisting caches without changing any requested language. -/
theorem fast_requested_from_state [DecidableEq (EnumerationState.Edge Symbol Guard)]
    (source : Nat → RowKey Symbol Guard) (sourceValid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (state : State Symbol Guard) (valid : Valid source state) (requests : List Key)
    (meet : Nat → Nat → Nat) (meaning : Guard → Term Symbol → Prop)
    (key : Key) (member : key ∈ requests) (term : Term Symbol) :
    let final := visitMany (fun key => fastBuild source key.1 key.2) requests (elide source state)
    Accepted (graph final meet) meaning (encode final key) term ↔
      Accepts (fun node => (source node).map (EnumerationLanguage.edgeView meaning)) key.2 term ∧ term.height ≤ key.1 := by
  let slow := visitMany (fun key => build source key.1 key.2) requests state
  obtain ⟨finalValid, _, reached⟩ := visitMany_correct source id (fun key => build source key.1 key.2)
    (fun key before checked => build_correct source sourceValid key.1 key.2 before checked) requests state valid
  have simulation := visitMany_elide source (fun (key : Key) => build source key.1 key.2)
    (fun key => fastBuild source key.1 key.2)
    (fun key before checked => (build_correct source sourceValid key.1 key.2 before checked).1)
    (fun key before checked => fastBuild_exact source sourceValid key.1 key.2 before checked) requests state valid
  dsimp only
  rw [simulation, encode_elide source slow finalValid key]
  exact scoped_accepted_exact source slow finalValid meet meaning key (reached key member) term

end MicroCFTA.EnumerationBuilderRuntime
