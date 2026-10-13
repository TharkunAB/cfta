import MicroCFTA.MergedOrdinaryHeight

/-!
# A well-founded call relation for guarded alternative merging

The merge worker calls itself on an ordinary child or on a union of selected
children from an ordinary parent. The recursive-boundary guard prevents the
second case from unfolding a Mu or an explicit union. This relation permits
any child selection, so filtering and group order do not affect its rank.
It describes recursive merge calls. It does not assert termination of the
subsumption helper or convergence of repeated equality passes.
-/
namespace MicroCFTA.MergedMergeTermination
open Cache InternedConstructorTemplates InternedRecordCoherence InternedFreshProbeKeys
open InternedEdgeResidency MergedOrdinaryHeight
open InternedBinderProtocol (NodeKey Reference)

/-- An overapproximation of the two recursive call forms after the boundary guard. -/
inductive Step [DecidableEq (EdgeKey Symbol Guard)] : Value Symbol Guard → Value Symbol Guard → Prop where
  | child (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
      (depth : Nat) (free : List Reference) (edge : EdgeValue Symbol Guard) (value : Value Symbol Guard)
      (present : edge ∈ edges) (selected : value ∈ edge.children) :
      Step value (.node entry edges depth free)
  | column (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
      (depth : Nat) (free : List Reference) (values : List (Value Symbol Guard))
      (selected : ∀ value ∈ values, ∃ edge ∈ edges, value ∈ edge.children)
      (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
      (resident : ∀ value ∈ values, Resident state value) :
      Step (run (ordinaryUnion values) state).1 (.node entry edges depth free)

/-- Every recursive merge call strictly decreases ordinary constructor height. -/
theorem step_lt [DecidableEq (EdgeKey Symbol Guard)] (next parent : Value Symbol Guard)
    (step : Step next parent) : height next < height parent := by
  cases step with
  | child entry edges depth free edge value present selected =>
      exact child_lt entry edges depth free edge present _ selected
  | column entry edges depth free values selected state coherent linked resident =>
      exact column_union_lt entry edges depth free values selected state coherent linked resident

/-- No infinite chain of guarded recursive merge calls exists in the physical value model. -/
theorem wellFounded [DecidableEq (EdgeKey Symbol Guard)] :
    WellFounded (Step (Symbol := Symbol) (Guard := Guard)) := by
  exact Subrelation.wf (fun {_ _} step => step_lt _ _ step) (InvImage.wf height Nat.lt_wfRel.wf)

/-- Any finite list of required guarded calls has a finite recursive evaluation tree. -/
theorem completes [DecidableEq (EdgeKey Symbol Guard)]
    (requests : Value Symbol Guard → List (Value Symbol Guard))
    (source : ∀ parent next, next ∈ requests parent → Step next parent)
    (value : Value Symbol Guard) :
    Acc (fun next parent => next ∈ requests parent) value := by
  exact (Subrelation.wf (fun {next parent} member => source parent next member) wellFounded).apply value

end MicroCFTA.MergedMergeTermination
