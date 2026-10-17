import MicroCFTA.SourceCurrentRequiredUnionNormalRead
import MicroCFTA.SourceCurrentAllocatedMergeWorker

/-!
# Union normality through actual comparisons and allocated Merge

The proof follows all bounded outcomes and the literal first-writer reread.
The private instruction check is derived for the complete actual Merge body.
It is not a premise of the exported call law.
-/
namespace MicroCFTA.SourceCurrentUnionNormalMerge
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)

private theorem bind (first : MergedSourceComparison.Result Symbol Guard A)
    (next : A → State Symbol Guard → MergedSourceComparison.Result Symbol Guard B)
    (normal : UnionNormal first.state)
    (later : ∀ value after, UnionNormal after → UnionNormal (next value after).state) :
    UnionNormal (first.bind next).state := by
  cases first with
  | failed => exact normal
  | done value state => exact later value state normal

private theorem children
    (call : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → MergedSourceComparison.Result Symbol Guard Bool)
    (checked : ∀ left right state, UnionNormal state → UnionNormal (call left right state).state)
    (left right : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (MergedSourceComparison.children call left right state).state := by
  induction left generalizing right state with
  | nil => exact normal
  | cons value left ih =>
      cases right with
      | nil => exact normal
      | cons other right =>
          apply bind _ _ (checked value other state normal)
          intro accepted after afterNormal
          cases accepted
          · exact afterNormal
          · exact ih right after afterNormal

private theorem anyCover [DecidableEq Symbol] (clear : Guard → Bool)
    (call : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → MergedSourceComparison.Result Symbol Guard Bool)
    (checked : ∀ left right state, UnionNormal state → UnionNormal (call left right state).state)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (MergedSourceComparison.anyCover clear call narrow wides state).state := by
  induction wides generalizing state with
  | nil => exact normal
  | cons wide rest ih =>
      rw [MergedSourceComparison.anyCover]
      split
      · apply bind _ _ (children call checked _ _ state normal)
        intro accepted after afterNormal
        cases accepted
        · exact ih after afterNormal
        · exact afterNormal
      · exact ih state normal

private theorem allRows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (call : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → MergedSourceComparison.Result Symbol Guard Bool)
    (checked : ∀ left right state, UnionNormal state → UnionNormal (call left right state).state)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (MergedFreshOrdinaryComparison.allRows fuel clear call wide narrows state).state := by
  induction narrows generalizing state with
  | nil => exact normal
  | cons narrow rest ih =>
      apply bind _ _ (SourceCurrentRequiredUnionNormalRead.read fuel wide state normal)
      intro wides middle middleNormal
      apply bind _ _ (anyCover clear call checked narrow wides middle middleNormal)
      intro accepted after afterNormal
      cases accepted
      · exact afterNormal
      · exact ih after afterNormal

/-- Every actual comparison branch retains the invariant, including failed covers. -/
theorem comparison [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (MergedFreshOrdinaryComparison.check clear fuel above wide narrow state).state := by
  induction fuel generalizing above wide narrow state with
  | zero =>
      unfold MergedFreshOrdinaryComparison.check
      repeat' first | split | exact normal | contradiction
  | succ fuel ih =>
      rw [MergedFreshOrdinaryComparison.check]
      split
      · exact normal
      · split
        · exact normal
        · split
          · exact normal
          · split
            · exact normal
            · exact normal
            · split
              · exact normal
              · exact bind _ _ (SourceCurrentRequiredUnionNormalRead.read (fuel+1) narrow state normal)
                  (fun narrows after afterNormal => allRows clear (fuel+1) _
                    (fun left right current currentNormal => ih _ left right current currentNormal)
                    wide narrows after afterNormal)

private theorem anyAccepts [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceMergedSelection.anyAccepts clear fuel narrow wides state).state := by
  induction wides generalizing state with
  | nil => exact normal
  | cons wide rest ih =>
      rw [SourceMergedSelection.anyAccepts]
      split
      · apply bind _ _ (comparison clear fuel [] wide narrow state normal)
        intro accepted after afterNormal
        cases accepted
        · exact ih after afterNormal
        · exact afterNormal
      · exact normal

private theorem retain [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (recursive inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceMergedSelection.retain clear fuel recursive inputs state).state := by
  induction inputs generalizing state with
  | nil => exact normal
  | cons value rest ih =>
      rw [SourceMergedSelection.retain]
      split
      · exact bind _ _ (ih state normal) (fun _ _ afterNormal => afterNormal)
      · exact bind _ _ (anyAccepts clear fuel value recursive state normal) (fun _ middle middleNormal =>
          bind _ _ (ih middle middleNormal) (fun _ _ afterNormal => afterNormal))

/-- Ordered retention and final identity deduplication retain the actual stopping heap. -/
theorem selection [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (inputs : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceMergedSelection.select clear fuel inputs state).state :=
  bind _ _ (retain clear fuel _ inputs state normal) (fun _ _ afterNormal => afterNormal)

section Allocated
open SourceCurrentAllocatedMergeGraph (Code Memo)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State

section Programs
variable [DecidableEq (EdgeKey Symbol Guard)]

private def Safe : Code Output → Prop
  | .work job => ∀ state, UnionNormal state → UnionNormal (run job state).2
  | .bind first next => Safe first ∧ ∀ value, Safe (next value)
  | _ => True

private theorem map_safe (call : Input → Code Output) (checked : ∀ input, Safe (call input)) (inputs : List Input) :
    Safe (SourceCurrentAllocatedMergeGraph.map call inputs) := by
  induction inputs with
  | nil => trivial
  | cons input rest ih => exact ⟨checked input, fun _ => ⟨ih, fun _ => trivial⟩⟩

private theorem retained_safe (inputs : List (Value Symbol Guard)) : Safe (SourceCurrentAllocatedMergeGraph.retainedColumn inputs) := by
  unfold SourceCurrentAllocatedMergeGraph.retainedColumn
  split
  · trivial
  · split
    · exact fun state normal => SourceCurrentRequiredUnionNormal.union _ state normal
    · exact ⟨fun state normal => SourceCurrentRequiredUnionNormal.node _ state normal, fun _ => trivial⟩

private theorem small_safe (edge : EdgeValue Symbol Guard) : Safe (SourceCurrentAllocatedMergeGraph.small edge) :=
  ⟨map_safe Code.request (fun _ => trivial) edge.children, fun _ state normal => SourceCurrentRequiredUnionNormal.edge _ _ _ state normal⟩

private theorem column_safe (inputs : List (Value Symbol Guard)) : Safe (SourceCurrentAllocatedMergeGraph.column inputs) :=
  ⟨trivial, retained_safe⟩

private theorem large_safe (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    Safe (SourceCurrentAllocatedMergeGraph.large first rest) := ⟨map_safe _ column_safe _, fun _ => trivial⟩

private theorem group_safe (edges : List (EdgeValue Symbol Guard)) : Safe (SourceCurrentAllocatedMergeGraph.group edges) := by
  unfold SourceCurrentAllocatedMergeGraph.group
  split
  · exact map_safe _ small_safe _
  · cases edges with
    | nil => trivial
    | cons first rest => exact ⟨large_safe first rest, fun _ => trivial⟩

private theorem body_safe [DecidableEq Symbol] (input : Value Symbol Guard) : Safe (SourceCurrentAllocatedMergeGraph.body input) := by
  cases input <;> simp only [SourceCurrentAllocatedMergeGraph.body]
  all_goals first | trivial | skip
  split
  · exact ⟨map_safe _ group_safe _, fun _ state normal => SourceCurrentRequiredUnionNormal.node _ state normal⟩
  · trivial

end Programs

private theorem allocated_bind (first : SourceCurrentAllocatedMergeWorker.Outcome A)
    (next : A → Physical → Memo → SourceCurrentAllocatedMergeWorker.Outcome B)
    (normal : UnionNormal first.state.heap)
    (later : ∀ value after memo, UnionNormal after.heap → UnionNormal (next value after memo).state.heap) :
    UnionNormal (first.bind next).state.heap := by
  cases first with
  | failed => exact normal
  | done value state memo => exact later value state memo normal

/-- Actual allocated Merge retains the invariant through nested misses and warm winners. -/
theorem merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (worker selector : Nat) (input : Value Symbol Guard)
    (state : Physical) (memo : Memo) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentAllocatedMergeWorker.call clear worker selector input state memo).state.heap := by
  have both (fuel : Nat) :
      (∀ (A : Type) (code : Code A) state memo, Safe code → UnionNormal state.heap →
        UnionNormal (SourceCurrentAllocatedMergeWorker.execute clear fuel selector code state memo).state.heap) ∧
      (∀ input state memo, UnionNormal state.heap →
        UnionNormal (SourceCurrentAllocatedMergeWorker.call clear fuel selector input state memo).state.heap) := by
    induction fuel with
    | zero => exact ⟨fun _ _ _ _ _ normal => normal, fun _ _ _ normal => normal⟩
    | succ fuel ih =>
        constructor
        · intro A code state memo safe normal
          cases code with
          | pure => exact normal
          | work job => exact safe state.heap normal
          | topRow symbol children => exact SourceCurrentRequiredUnionNormal.edge symbol _ children state.heap normal
          | select inputs =>
              have retained := selection clear selector inputs state.heap normal
              cases actual : SourceMergedSelection.select clear selector inputs state.heap <;>
                simpa only [SourceCurrentAllocatedMergeWorker.execute,actual,SourceCurrentAllocatedMergeWorker.Outcome.state,
                  MergedSourceComparison.Result.state] using retained
          | request input => exact ih.2 input state memo normal
          | bind first next =>
              exact allocated_bind _ _ (ih.1 _ first state memo safe.1 normal)
                (fun value after memo afterNormal => ih.1 _ (next value) after memo (safe.2 value) afterNormal)
        · intro input state memo normal
          rw [SourceCurrentAllocatedMergeWorker.call]
          split
          · exact normal
          · exact allocated_bind _ _ (ih.1 _ _ state memo (body_safe input) normal)
              (fun _ _ _ afterNormal => afterNormal)
  exact (both worker).2 input state memo normal
end Allocated
end MicroCFTA.SourceCurrentUnionNormalMerge
