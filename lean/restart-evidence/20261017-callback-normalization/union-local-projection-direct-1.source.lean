import MicroCFTA.SourceCurrentRequiredUnionNormalRead
import MicroCFTA.SourceCurrentMuEndpoint

/-!
# Normal union records through bounded projections and both current gates

The proofs follow the actual ordered workers and every stopping branch.
Unresolved references and pending unfolds retain their reached heaps.
No selected-domain, closure, or future callback condition is an input.
-/
namespace MicroCFTA.SourceCurrentUnionNormalProjectionGate
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
open SourceCurrentRequiredUnionNormalRead (StoppedNormal)

private theorem bind (first : SourceEqualityRequiredWorker.Result Symbol Guard A)
    (next : A → State Symbol Guard → SourceEqualityRequiredWorker.Result Symbol Guard B)
    (normal : StoppedNormal first)
    (later : ∀ value after, UnionNormal after → StoppedNormal (next value after)) : StoppedNormal (first.bind next) := by
  cases first with
  | done value state => exact later value state normal
  | pending | unresolved | exhausted => exact normal

private theorem readAll [DecidableEq (EdgeKey Symbol Guard)] (reader : Nat)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityProjectionWorker.readAll reader values state) := by
  induction values generalizing state with
  | nil => exact normal
  | cons value values ih =>
      have retained := SourceCurrentRequiredUnionNormalRead.nodeEdges reader value state normal
      cases actual : MergedFreshOrdinaryExposure.nodeEdges reader value state with
      | done edges middle =>
          have middleNormal : UnionNormal middle := by simpa only [actual,MergedSourceExposure.Result.state] using retained
          simpa only [SourceEqualityProjectionWorker.readAll,actual] using
            bind _ _ (ih middle middleNormal) (fun _ _ afterNormal => afterNormal)
      | pending | unresolved | exhausted =>
          simpa only [SourceEqualityProjectionWorker.readAll,actual,StoppedNormal,MergedSourceExposure.Result.state] using retained

private theorem union [DecidableEq (EdgeKey Symbol Guard)] (reader : Nat)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityProjectionWorker.union reader values state) :=
  bind _ _ (readAll reader values state normal)
    (fun rows after afterNormal => SourceCurrentRequiredUnionNormal.node rows after afterNormal)

private theorem rows
    (call : Value Symbol Guard → State Symbol Guard → SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard))
    (checked : ∀ value state, UnionNormal state → StoppedNormal (call value state))
    (index : Int) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityProjectionWorker.rows call index edges state) := by
  induction edges generalizing state with
  | nil => exact normal
  | cons edge edges ih =>
      rw [SourceEqualityProjectionWorker.rows]
      split
      · exact ih state normal
      · exact bind _ _ (checked _ state normal) (fun _ middle middleNormal =>
          bind _ _ (ih middle middleNormal) (fun _ _ afterNormal => afterNormal))

private theorem project [DecidableEq (EdgeKey Symbol Guard)] (worker reader : Nat) (path : List Int)
    (value : Value Symbol Guard) (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityProjectionWorker.project worker reader path value state) := by
  induction worker generalizing path value state with
  | zero => exact normal
  | succ worker ih =>
      cases path with
      | nil => exact normal
      | cons index path =>
          cases value with
          | empty | reference => exact normal
          | node entry edges depth free =>
              exact bind _ _ (rows _ (fun value state normal => ih path value state normal) index edges state normal)
                (fun values after afterNormal => union reader values after afterNormal)
          | union | mu =>
              exact bind _ _ (SourceCurrentRequiredUnionNormalRead.head reader _ state normal)
                (fun exposed after afterNormal => ih (index :: path) exposed after afterNormal)

/-- Actual signed forest projection retains normality at every bounded outcome. -/
theorem forest [DecidableEq (EdgeKey Symbol Guard)] (worker reader : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    StoppedNormal (SourceEqualityProjectionWorker.forest worker reader path values state) := by
  cases path with
  | nil => exact union reader values state normal
  | cons index path =>
      unfold SourceEqualityProjectionWorker.forest
      split
      · exact normal
      · exact project worker reader path _ state normal

private theorem nested_bind (first : InternedNestedConstruction.Outcome Symbol Guard A)
    (next : A → State Symbol Guard → InternedNestedConstruction.Outcome Symbol Guard B)
    (normal : UnionNormal first.state)
    (later : ∀ value after, UnionNormal after → UnionNormal (next value after).state) : UnionNormal (first.bind next).state := by
  cases first with
  | pending => exact normal
  | done value state => exact later value state normal

private theorem anyKnown (test : Item → State Symbol Guard → InternedNestedConstruction.Outcome Symbol Guard (Option Bool))
    (checked : ∀ item state, UnionNormal state → UnionNormal (test item state).state)
    (items : List Item) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (InternedFreshOrdinaryStatefulGate.anyKnown test items state).state := by
  induction items generalizing state with
  | nil => exact normal
  | cons item items ih =>
      apply nested_bind _ _ (checked item state normal)
      intro answer after afterNormal
      cases answer with
      | none => exact afterNormal
      | some answer => cases answer
                       · exact ih after afterNormal
                       · exact afterNormal

private theorem child (call : EqualityNormalize.Path → Value Symbol Guard → State Symbol Guard →
      InternedNestedConstruction.Outcome Symbol Guard (Option Bool))
    (checked : ∀ path value state, UnionNormal state → UnionNormal (call path value state).state)
    (values : List (Value Symbol Guard)) (index : Nat) (path : EqualityNormalize.Path)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (InternedFreshOrdinaryStatefulGate.child call values index path state).state := by
  unfold InternedFreshOrdinaryStatefulGate.child
  split
  · exact normal
  · exact checked path _ state normal

private theorem nodeMeets [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool)
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat) (path : EqualityNormalize.Path)
    (value : Value Symbol Guard) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceCurrentMuEndpoint.nodeMeets belowEnd unconstrained reaches fuel path value state).state := by
  induction fuel generalizing path value state with
  | zero => exact normal
  | succ fuel ih =>
      rw [SourceCurrentMuEndpoint.nodeMeets]
      cases value with
      | empty | reference | union => exact normal
      | node entry edges depth free =>
          unfold SourceCurrentMuEndpoint.dispatch
          split
          · exact normal
          · cases path with
            | nil => exact normal
            | cons index path => exact anyKnown _
                (fun edge state normal => child _ ih edge.children index path state normal) edges state normal
      | mu entry body depth ordinary =>
          unfold SourceCurrentMuEndpoint.dispatch
          split
          · exact normal
          · split
            · cases path with
              | nil => split <;> exact normal
              | cons => exact normal
            · split
              · exact normal
              · exact nested_bind _ _ (SourceCurrentRequiredUnionNormal.unfold _ state normal)
                  (fun value after afterNormal => ih path value after afterNormal)

/-- Both current gate modes retain the invariant through actual ordered paths and unfolds. -/
theorem gate [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool)
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : EqualityNormalize.Class)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceCurrentMuEndpoint.classMeets belowEnd unconstrained reaches fuel values paths state).state := by
  apply anyKnown _ _ paths state normal
  intro path current currentNormal
  cases path with
  | nil => exact currentNormal
  | cons index path => exact child _ (fun path value state normal => nodeMeets belowEnd unconstrained reaches fuel path value state normal)
      values index path current currentNormal
end MicroCFTA.SourceCurrentUnionNormalProjectionGate
