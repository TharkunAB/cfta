import MicroCFTA.SourceCurrentNormalizedPlanCongruence
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.RecursivePlanKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedNestedProvenance (Values)
open SourceCurrentNormalizedPlanRelation
open SourceEqualityRequiredCache (Ready Keeps)

private def rowA (n m k : Nat) : EdgeSyntax Nat Bool := .mk 0 false [.var n,.var m,.var k]
private def rowB (m k : Nat) : EdgeSyntax Nat Bool := .mk 1 true [.var k,.var m]
private def dead (n : Nat) : EdgeSyntax Nat Bool := .mk 2 false [.empty,.var n]
private def leftRows (n m k : Nat) := [rowA n m k,rowB m k,rowA n m k,dead n]
private def rightRows (n m k : Nat) := [dead n,rowB m k,rowA n m k,rowB m k]
private def leftPlan (seed depth : Nat) : Syntax Nat Bool :=
  .node [.mk 8 false [.union [
    .binder false (.node (leftRows 0 (seed+1) (depth+1))),
    .node (leftRows seed depth seed)]]]
private def rightPlan (seed depth : Nat) : Syntax Nat Bool :=
  .node [.mk 8 false [.union [
    .binder false (.node (rightRows 0 (seed+1) (depth+1))),
    .node (rightRows seed depth seed)]]]
private def firstInputs (value : Value Nat Bool) := [value,.reference .depth,value]
private def secondInputs (value : Value Nat Bool) := [.reference .depth,value]

private theorem singleton_rows (first second : EdgeSyntax Nat Bool)
    (firstInputs secondInputs : List (Value Nat Bool))
    (related : RowRelated first firstInputs second secondInputs) :
    RowsRelated [first] firstInputs [second] secondInputs := by
  rw [RowsRelated]
  constructor
  · intro row member
    have same := List.mem_singleton.mp member
    subst row
    exact ⟨second,List.mem_singleton_self _,related⟩
  · intro row member
    have same := List.mem_singleton.mp member
    subst row
    exact ⟨first,List.mem_singleton_self _,related⟩

private theorem reorder_rows (a b d a' b' d' : EdgeSyntax Nat Bool)
    (firstInputs secondInputs : List (Value Nat Bool))
    (aa : RowRelated a firstInputs a' secondInputs)
    (bb : RowRelated b firstInputs b' secondInputs)
    (dd : RowRelated d firstInputs d' secondInputs) :
    RowsRelated [a,b,a,d] firstInputs [d',b',a',b'] secondInputs := by
  rw [RowsRelated]
  constructor
  · intro row member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨a',by simp,aa⟩
    · exact ⟨b',by simp,bb⟩
    · exact ⟨a',by simp,aa⟩
    · exact ⟨d',by simp,dd⟩
  · intro row member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨d,by simp,dd⟩
    · exact ⟨b,by simp,bb⟩
    · exact ⟨a,by simp,aa⟩
    · exact ⟨b,by simp,bb⟩

private theorem rows_related (n m k p q r : Nat) (first second : List (Value Nat Bool))
    (nn : first[n]?.getD .empty = second[p]?.getD .empty)
    (mm : first[m]?.getD .empty = second[q]?.getD .empty)
    (kk : first[k]?.getD .empty = second[r]?.getD .empty) :
    RowsRelated (leftRows n m k) first (rightRows p q r) second := by
  apply reorder_rows
  · simp only [rowA,RowRelated,ManyRelated,Related]
    exact ⟨True.intro,True.intro,nn,mm,kk,True.intro⟩
  · simp only [rowB,RowRelated,ManyRelated,Related]
    exact ⟨True.intro,True.intro,kk,mm,True.intro⟩
  · simp only [dead,RowRelated,ManyRelated,Related]
    exact ⟨True.intro,True.intro,True.intro,nn,True.intro⟩

/-- Recursive row sets relate below a binder and an ordered union, with aliased captured Depth. -/
theorem captured_recursive_relation (capture : Value Nat Bool) :
    Related (leftPlan 0 1) (firstInputs capture) (rightPlan 1 0) (secondInputs capture) := by
  have inside (name : InternedBinderProtocol.Reference) :
      Related (.node (leftRows 0 1 2)) (.reference name :: firstInputs capture)
        (.node (rightRows 0 2 1)) (.reference name :: secondInputs capture) := by
    rw [Related]
    exact rows_related 0 1 2 0 2 1 _ _ (by rfl) (by rfl) (by rfl)
  have outside : Related (.node (leftRows 0 1 0)) (firstInputs capture)
      (.node (rightRows 1 0 1)) (secondInputs capture) := by
    rw [Related]
    exact rows_related 0 1 0 1 0 1 _ _ (by rfl) (by rfl) (by rfl)
  have binderSame : Related (.binder false (.node (leftRows 0 1 2))) (firstInputs capture)
      (.binder false (.node (rightRows 0 2 1))) (secondInputs capture) := by
    rw [Related]
    exact ⟨rfl,inside⟩
  have unionSame : Related (.union [.binder false (.node (leftRows 0 1 2)),.node (leftRows 0 1 0)])
      (firstInputs capture) (.union [.binder false (.node (rightRows 0 2 1)),.node (rightRows 1 0 1)])
      (secondInputs capture) := by
    rw [Related,ManyRelated]
    refine ⟨binderSame,?_⟩
    rw [ManyRelated]
    refine ⟨outside,?_⟩
    rw [ManyRelated]
    trivial
  rw [leftPlan,rightPlan,Related]
  apply singleton_rows
  rw [RowRelated,ManyRelated]
  refine ⟨rfl,rfl,unionSame,?_⟩
  rw [ManyRelated]
  trivial

private def seedSyntax : Syntax Nat Bool := .node [.mk 9 false []]
private def seedRun := build seedSyntax [] empty
private def seed : Value Nat Bool := match seedRun with | .done value _ => value | .pending .. => .empty
private def initial := seedRun.state
private theorem seed_done : seedRun = .done seed initial := by cbv
private theorem initial_ready : Ready initial := SourceEqualityRequiredCache.constructed seedSyntax seed initial seed_done
private theorem seed_available : Available initial seed :=
  (InternedFreshOrdinaryFacts.closed_verified seedSyntax).result seed initial seed_done
private theorem first_available : Values initial (firstInputs seed) := by
  intro value member
  simp only [firstInputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact seed_available
  · exact InternedNestedProvenance.depth_available initial
  · exact seed_available
private theorem second_available : Values initial (secondInputs seed) := by
  intro value member
  simp only [secondInputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact InternedNestedProvenance.depth_available initial
  · exact seed_available

/-- The comparison starts from its own source-built Ready heap and available open captures. -/
theorem own_initial_relation :
    build seedSyntax [] empty = .done seed initial ∧ Ready initial ∧
    Values initial (firstInputs seed) ∧ Values initial (secondInputs seed) ∧
    Related (leftPlan 0 1) (firstInputs seed) (rightPlan 1 0) (secondInputs seed) :=
  ⟨seed_done,initial_ready,first_available,second_available,captured_recursive_relation seed⟩

private def firstRun := build (leftPlan 0 1) (firstInputs seed) initial
private def original : Value Nat Bool := match firstRun with | .done value _ => value | .pending .. => .empty
private def firstHeap := firstRun.state
private def underUnion (value : Value Nat Bool) : Value Nat Bool :=
  ((unionMembers (((children value)[0]?).getD .empty)).find? fun child =>
    match child with | .mu .. => true | _ => false).getD .empty
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private theorem first_done : firstRun = .done original firstHeap := by cbv
private theorem original_used : ∃ entry body depth ordinary,
    underUnion original = .mu entry body depth ordinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true := by
  exact ⟨(fields (underUnion original)).1,(fields (underUnion original)).2.1,
    (fields (underUnion original)).2.2.1,(fields (underUnion original)).2.2.2,by cbv,by cbv⟩
private theorem original_open : original.free ≠ [] := by
  intro impossible
  cbv at impossible
  cases impossible

/-- Own initial captures produce equal recursive permutations below a used Mu, with exact final warm replay. -/
theorem recursive_initial :
    ∃ value middle after,
      build (leftPlan 0 1) (firstInputs seed) initial = .done value middle ∧
      build (rightPlan 1 0) (secondInputs seed) middle = .done value after ∧
      Keeps initial middle ∧ Keeps middle after ∧ Available after value ∧
      (∃ entry body depth ordinary,
        underUnion value = .mu entry body depth ordinary ∧
        InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
      value.free ≠ [] ∧
      build (leftPlan 0 1) (firstInputs seed) after = .done value after ∧
      build (rightPlan 1 0) (secondInputs seed) after = .done value after := by
  obtain ⟨value,middle,after,leftDone,rightDone,first,second,available⟩ :=
    SourceCurrentNormalizedPlanCongruence.initial (leftPlan 0 1) (rightPlan 1 0)
      (firstInputs seed) (secondInputs seed) initial initial_ready first_available second_available
      (captured_recursive_relation seed)
  have originalDone : .done original firstHeap = (.done value middle : Outcome Nat Bool (Value Nat Bool)) :=
    first_done.symm.trans leftDone
  rcases Outcome.done.inj originalDone with ⟨valueEq,middleEq⟩
  subst value middle
  have leftWarm := InternedFreshOrdinaryReplay.build_replay (leftPlan 0 1) (firstInputs seed)
    initial after original firstHeap initial_ready.semantic.1.normal.facts.coherent.valid leftDone second.growth
  have rightWarm := InternedFreshOrdinaryReplay.build_replay (rightPlan 1 0) (secondInputs seed)
    firstHeap after original after first.ready.semantic.1.normal.facts.coherent.valid rightDone (grows_refl after)
  exact ⟨original,firstHeap,after,leftDone,rightDone,first,second,available,
    original_used,original_open,leftWarm,rightWarm⟩

end MicroCFTA.RecursivePlanKernels
#check @MicroCFTA.RecursivePlanKernels.recursive_initial
#print axioms MicroCFTA.RecursivePlanKernels.recursive_initial
