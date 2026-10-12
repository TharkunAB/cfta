import MicroCFTA.InternedNestedConstructionGrowth

/-!
# Dense canonical identities in the sequential source executor

Every identity below the next counter has its canonical table entry.
The source uses complete sequential intern operations. It does not expose
an issued candidate before its table installation. The proof covers both
cache families and both outcomes of arbitrary nested construction.
-/
namespace MicroCFTA.Cache

/-- Every earlier identity has its exact canonical entry in the current table. -/
def Dense (state : State Key) : Prop :=
  ∀ identity, identity < state.next → ∃ key, state.table key = some ⟨identity, key⟩

/-- An empty counter has no earlier identities. -/
theorem empty_dense : Dense (emptyState (Key := Key)) := by
  intro identity smaller
  simp [emptyState] at smaller

/-- A sequential cache hit or miss preserves a dense canonical identity supply. -/
theorem intern_dense [DecidableEq Key] (state : State Key) (key : Key) (dense : Dense state) :
    Dense (intern state key).2 := by
  cases found : state.table key with
  | some entry => simpa only [intern, found] using dense
  | none =>
      intro identity bound
      simp only [intern, found, reserve, install] at bound
      by_cases same : identity = state.next
      · subst identity
        exact ⟨key, by simp [intern, found, reserve, install, keepFirst, put]⟩
      · obtain ⟨other, present⟩ := dense identity (by omega)
        have different : other ≠ key := by intro equal; subst other; rw [found] at present; cases present
        exact ⟨other, by simp [intern, found, reserve, install, keepFirst, put, different, present]⟩

end MicroCFTA.Cache

namespace MicroCFTA.InternedNestedDenseIdentities
open Cache InternedConstructorTemplates InternedNestedConstruction

/-- Both independent source caches have dense canonical identities. -/
def Dense (state : State Symbol Guard) : Prop := Cache.Dense state.edges ∧ Cache.Dense state.nodes

/-- Both source identity supplies begin dense. -/
theorem empty_dense : Dense (empty (Symbol := Symbol) (Guard := Guard)) := ⟨Cache.empty_dense, Cache.empty_dense⟩

/-- Finite constructor work uses complete interning operations in each cache. -/
theorem run_dense [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : State Symbol Guard) (dense : Dense state) : Dense (run computation state).2 := by
  induction computation generalizing state with
  | pure value => exact dense
  | edge key identify resume ih =>
      exact ih (edgeStep key identify state).1 _ ⟨Cache.intern_dense state.edges key dense.1, dense.2⟩
  | node key identify resume ih =>
      exact ih (nodeStep key identify state).1 _ ⟨dense.1, Cache.intern_dense state.nodes key dense.2⟩

/-- Source sequencing retains density at its completed or pending state. -/
theorem bind_dense (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : Dense outcome.state)
    (later : ∀ value state, Dense state → Dense (next value state).state) :
    Dense (outcome.bind next).state := by
  cases outcome with
  | pending => exact first
  | done value state => exact later value state first

/-- A Mu reservation installs its canonical entry before evaluating its body. -/
theorem request_dense [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (callback : InternedBinderProtocol.Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (dense : Dense state)
    (bodyDense : ∀ name current, Dense current → Dense (callback name current).state) :
    Dense (request smart depth ordinary callback state).state := by
  unfold request
  dsimp only
  split
  · split <;> exact dense
  · apply bind_dense
    · exact bodyDense _ _ ⟨dense.1, Cache.intern_dense _ _ dense.2⟩
    · intro value after afterDense
      exact afterDense

mutual
/-- Arbitrary nested source construction preserves both complete canonical identity supplies. -/
theorem build_dense [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (dense : Dense state) :
    Dense (build expression environment state).state := by
  cases expression with
  | empty | var index => simpa only [build, Outcome.state] using dense
  | node edges =>
      simp only [build]
      exact bind_dense _ _ (buildEdges_dense edges environment state dense)
        (fun values current currentDense => run_dense (makeNode values) current currentDense)
  | union members =>
      simp only [build]
      exact bind_dense _ _ (buildMany_dense members environment state dense)
        (fun values current currentDense => run_dense (makeUnion values) current currentDense)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have preserved : ∀ name current, Dense current → Dense (callback name current).state := by
        intro name current currentDense
        exact bind_dense _ _ (build_dense body _ current currentDense)
          (fun value after afterDense => run_dense (withoutSelfReference name value) after afterDense)
      rw [build]
      change Dense ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      exact bind_dense _ _ (preserved .depth state dense) (fun depth afterDepth depthDense =>
        bind_dense _ _ (preserved (.uninterned depth.depth) afterDepth depthDense)
          (fun ordinary afterOrdinary ordinaryDense =>
            request_dense smart depth ordinary callback afterOrdinary ordinaryDense preserved))
termination_by sizeOf expression

/-- Ordered child execution preserves both dense identity supplies. -/
theorem buildMany_dense [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (dense : Dense state) :
    Dense (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using dense
  | cons first rest =>
      simp only [buildMany]
      exact bind_dense _ _ (build_dense first environment state dense) (fun value after afterDense =>
        bind_dense _ _ (buildMany_dense rest environment after afterDense) (fun _ _ finalDense => finalDense))
termination_by sizeOf expressions

/-- Edge and child execution preserve both dense identity supplies. -/
theorem buildEdges_dense [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (dense : Dense state) :
    Dense (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using dense
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges]
          exact bind_dense _ _ (buildMany_dense children environment state dense) (fun values after afterDense =>
            bind_dense _ _ (run_dense (makeEdge symbol constraint values) after afterDense) (fun edge next nextDense =>
              bind_dense _ _ (buildEdges_dense rest environment next nextDense) (fun _ _ finalDense => finalDense)))
termination_by sizeOf expressions
end

/-- Every complete or pending first run has no gaps in either canonical identity supply. -/
theorem closed_dense [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Dense (build expression [] empty).state := build_dense expression [] empty empty_dense

end MicroCFTA.InternedNestedDenseIdentities
