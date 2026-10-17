import MicroCFTA.SourceCurrentRequiredUnionNormal
import MicroCFTA.SourceEqualityRequiredExecution
import MicroCFTA.SourceEqualityProjectionWorker

/-!
# Union normality through actual row and selected-path workers

Every repaired unfolding retains the invariant. Ordered reads and actual
constructors therefore retain it on success, pending writes, unresolved
references, and bound exhaustion. No selected-input closure is required.
-/
namespace MicroCFTA.SourceCurrentRequiredUnionNormalRead
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)

private theorem prepend_state (edges : List (EdgeValue Symbol Guard)) (result : MergedSourceExposure.Result Symbol Guard) :
    (result.prepend edges).state = result.state := by cases result <;> rfl
private theorem canonical_state (result : MergedSourceExposure.Result Symbol Guard) :
    result.canonical.state = result.state := by cases result <;> rfl

/-- The literal worklist retains union normality at every stopping state. -/
theorem collect [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (normal : UnionNormal state) :
    UnionNormal (MergedFreshOrdinaryExposure.collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact normal
  | succ fuel ih =>
      cases pending with
      | nil => exact normal
      | cons value rest =>
          cases value with
          | empty => exact ih state seen rest normal
          | reference => exact normal
          | node => simpa only [MergedFreshOrdinaryExposure.collect, prepend_state] using ih state seen rest normal
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_left visited] using ih state seen rest normal
              · simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_right visited] using
                  ih state (entry.identity :: seen) (members ++ rest) normal
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_left visited] using ih state seen rest normal
              · have first := SourceCurrentRequiredUnionNormal.unfold (.mu entry body depth ordinary) state normal
                cases actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                | pending key after =>
                    simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_right visited, actual,
                      MergedSourceExposure.Result.state, InternedNestedConstruction.Outcome.state] using first
                | done result after =>
                    have afterNormal : UnionNormal after := by
                      simpa only [actual, InternedNestedConstruction.Outcome.state] using first
                    simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_right visited, actual] using
                      ih after (entry.identity :: seen) (result :: rest) afterNormal

/-- Both direct exposure and the closure fallback retain the same heap invariant. -/
theorem nodeEdges [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : UnionNormal state) :
    UnionNormal (MergedFreshOrdinaryExposure.nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentNormal : UnionNormal current) :
      UnionNormal (MergedFreshOrdinaryExposure.collect fuel current [] [value]).canonical.state := by
    rw [canonical_state]
    exact collect fuel current [] [value] currentNormal
  cases value with
  | empty | reference | node => exact normal
  | union => exact fallback state normal
  | mu entry body depth ordinary =>
      have first := SourceCurrentRequiredUnionNormal.unfold (.mu entry body depth ordinary) state normal
      cases actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
      | pending key after =>
          simpa only [MergedFreshOrdinaryExposure.nodeEdges, actual, MergedSourceExposure.Result.state,
            InternedNestedConstruction.Outcome.state] using first
      | done result after =>
          have afterNormal : UnionNormal after := by
            simpa only [actual, InternedNestedConstruction.Outcome.state] using first
          have retained := collect fuel after [] [.mu entry body depth ordinary] afterNormal
          cases result with
          | node => simpa only [MergedFreshOrdinaryExposure.nodeEdges, actual, MergedSourceExposure.Result.state] using afterNormal
          | empty | reference | union | mu =>
              simpa only [MergedFreshOrdinaryExposure.nodeEdges, actual, canonical_state] using retained

/-- Source comparison reads retain union normality on successful and failed returns. -/
theorem read [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : UnionNormal state) :
    UnionNormal (MergedFreshOrdinaryExposure.read fuel value state).state := by
  have retained := nodeEdges fuel value state normal
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value state <;>
    simpa only [MergedFreshOrdinaryExposure.read, actual, MergedSourceExposure.Result.state,
      MergedSourceComparison.Result.state] using retained

/-- Every actual Required result retains its stopping heap, including incomplete returns. -/
def StoppedNormal : SourceEqualityRequiredWorker.Result Symbol Guard A → Prop
  | .done _ state | .pending _ state | .unresolved _ state | .exhausted _ state => UnionNormal state

private theorem bind (first : SourceEqualityRequiredWorker.Result Symbol Guard A)
    (next : A → State Symbol Guard → SourceEqualityRequiredWorker.Result Symbol Guard B)
    (normal : StoppedNormal first)
    (continued : ∀ value after, UnionNormal after → StoppedNormal (next value after)) :
    StoppedNormal (first.bind next) := by
  cases first with
  | done value state => exact continued value state normal
  | pending | unresolved | exhausted => exact normal

/-- The actual reader and final ordinary constructor retain normality at every Head outcome. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : UnionNormal state) : StoppedNormal (SourceEqualityRequiredWorker.head fuel value state) := by
  have retained := nodeEdges fuel value state normal
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value state with
  | done edges after =>
      have afterNormal : UnionNormal after := by simpa only [actual, MergedSourceExposure.Result.state] using retained
      simpa only [SourceEqualityRequiredWorker.head, actual, SourceEqualityRequiredWorker.work, StoppedNormal] using
        SourceCurrentRequiredUnionNormal.node edges after afterNormal
  | pending | unresolved | exhausted => simpa only [SourceEqualityRequiredWorker.head, actual, StoppedNormal, MergedSourceExposure.Result.state] using retained

private theorem children_checked
    (call : SourceEqualityNeeded.Needed → Value Symbol Guard → State Symbol Guard → SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard))
    (checked : ∀ needed value state, UnionNormal state → StoppedNormal (call needed value state))
    (entries : List (Int × SourceEqualityNeeded.Needed)) (index : Nat) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityRequiredWorker.children call entries index values state) := by
  induction values generalizing index state with
  | nil => exact normal
  | cons first rest ih =>
      rw [SourceEqualityRequiredWorker.children]
      split
      · exact bind _ _ (ih _ state normal) (fun _ _ afterNormal => afterNormal)
      · apply bind _ _ (checked _ first state normal)
        intro result middle middleNormal
        exact bind _ _ (ih _ middle middleNormal) (fun _ _ afterNormal => afterNormal)

private theorem rows_checked [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityNeeded.Needed → Value Symbol Guard → State Symbol Guard → SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard))
    (checked : ∀ needed value state, UnionNormal state → StoppedNormal (call needed value state))
    (entries : List (Int × SourceEqualityNeeded.Needed)) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityRequiredWorker.rows call entries edges state) := by
  induction edges generalizing state with
  | nil => exact normal
  | cons first rest ih =>
      rw [SourceEqualityRequiredWorker.rows]
      split
      · apply bind _ _ (children_checked call checked entries 0 first.children state normal)
        intro values middle middleNormal
        apply bind _ _ (show StoppedNormal (SourceEqualityRequiredWorker.work
          (makeEdge first.entry.key.symbol first.entry.key.constraint values) middle) from middleNormal)
        intro edge afterEdge edgeNormal
        exact bind _ _ (ih afterEdge edgeNormal) (fun _ _ afterNormal => afterNormal)
      · exact ih state normal

/-- Actual selected-node execution preserves the invariant for arbitrary input syntax and bounds. -/
theorem require [DecidableEq (EdgeKey Symbol Guard)] (fuel reader : Nat) (needed : SourceEqualityNeeded.Needed) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityRequiredWorker.require fuel reader needed value state) := by
  induction fuel generalizing needed value state with
  | zero => exact normal
  | succ fuel ih =>
      cases needed with
      | node entries =>
          simp only [SourceEqualityRequiredWorker.require]
          split
          · exact normal
          · cases value with
            | empty | reference => exact normal
            | node entry edges depth free =>
                exact bind _ _ (rows_checked _ (fun needed value state normal => ih needed value state normal) entries edges state normal)
                  (fun rows after afterNormal => SourceCurrentRequiredUnionNormal.node rows after afterNormal)
            | union | mu => exact bind _ _ (head reader _ state normal) (fun value after afterNormal => ih _ value after afterNormal)

/-- The complete forest worker preserves normality at every actual stopping state. -/
theorem requireAll [DecidableEq (EdgeKey Symbol Guard)] (fuel reader : Nat) (paths : List SourceEqualityNeeded.Path)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityRequiredExecution.requireAll fuel reader paths values state) := by
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simpa only [SourceEqualityRequiredExecution.requireAll, compiled] using
        children_checked _ (fun needed value state normal => require fuel reader needed value state normal) entries 0 values state normal

/-- A successful actual Required graph retains the invariant at its exact final heap. -/
theorem required_node [DecidableEq (EdgeKey Symbol Guard)] {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredGraph.RequireNode needed value before result after)
    (normal : UnionNormal before) : UnionNormal after := by
  obtain ⟨fuel,reader,done⟩ := (SourceEqualityRequiredExecution.node_execution_iff needed value before result after).mp actual
  simpa only [done, StoppedNormal] using require fuel reader needed value before normal

/-- Actual Head graphs retain normality without closure or availability assumptions. -/
theorem head_graph [DecidableEq (EdgeKey Symbol Guard)] {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (normal : UnionNormal before) : UnionNormal after := by
  cases actual with
  | read fuel edges middle exposed built =>
      have retained := nodeEdges fuel value before normal
      have middleNormal : UnionNormal middle := by simpa only [exposed, MergedSourceExposure.Result.state] using retained
      simpa only [built] using SourceCurrentRequiredUnionNormal.node edges middle middleNormal

end MicroCFTA.SourceCurrentRequiredUnionNormalRead
