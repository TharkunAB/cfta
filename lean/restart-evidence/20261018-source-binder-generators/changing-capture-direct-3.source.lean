import MicroCFTA.SourceCurrentOpenObservationLanguage
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentSourceDirectedCases
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

/-!
# Actual nested used binders with distinct equivalent captures

One closed source constructs two different captured values. The same open
binder source uses each capture at one Ready reader. Its nested used Mu
captures the corresponding outer Mu. A checked finite simulation gives
every finite observation and exact guarded finite-tree language.
This example does not prove the general source-generated relation.
-/

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.SourceCurrentChangingCaptureBinderExample
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def leaf : Syntax Nat Bool := .node [.mk 3 true []]
private def wrapped : Syntax Nat Bool := .binder false leaf
private def outer (capture : Syntax Nat Bool) : Syntax Nat Bool :=
  .binder true (.node [.mk 2 true [],.mk 8 true [.var 0,
    .binder true (.node [.mk 6 true [],.mk 9 true [.var 0,.var 1,capture]])]])
private def expression : Syntax Nat Bool :=
  .binder true (.node [.mk 2 true [],.mk 8 true [.var 0,
    .binder true (.node [.mk 6 true [],.mk 9 true [.var 0,.var 1,.var 2]])]])
private def source : Syntax Nat Bool := .node [.mk 0 true [leaf,wrapped,outer leaf,outer wrapped]]
private def built := build source [] empty
private def root := val built
private def base := built.state
private def a : Value Nat Bool := (children root)[0]?.getD .empty
private def b : Value Nat Bool := (children root)[1]?.getD .empty
private def x : Value Nat Bool := (children root)[2]?.getD .empty
private def y : Value Nat Bool := (children root)[3]?.getD .empty
private def ux := unfold x base
private def lx := val ux
private def uy := unfold y ux.state
private def ly := val uy
private def innerX : Value Nat Bool := (children lx)[1]?.getD .empty
private def innerY : Value Nat Bool := (children ly)[1]?.getD .empty
private def vx := unfold innerX uy.state
private def mx := val vx
private def vy := unfold innerY vx.state
private def my := val vy
private def ub := unfold b vy.state
private def reader := ub.state

private def pairs : List (Value Nat Bool × Value Nat Bool) := [(a,b),(x,y),(lx,ly),(innerX,innerY),(mx,my)]
private def relation (first second : Value Nat Bool) : Prop :=
  first = second ∨ (first,second) ∈ pairs ∨ (second,first) ∈ pairs
private theorem same (value : Value Nat Bool) : relation value value := Or.inl rfl
private theorem actual : build source [] empty = .done root base := by
  obtain ⟨result,after,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete source
  change build source [] empty = .done (val (build source [] empty)) (build source [] empty).state
  rw [done]
  rfl
private theorem base_ready : SourceEqualityRequiredCache.Ready base :=
  SourceEqualityRequiredCache.constructed source root base actual

open Language InternedEdgeResidency
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open SourceCurrentSourceDirectedCases (Local)
open SourceCurrentOpenObservations (RowMatch)
open MergedFreshOrdinaryGraph (Origin successors)

private theorem calls :
    build expression [a] reader = .done x reader ∧
    build expression [b] reader = .done y reader ∧
    unfold x reader = .done lx reader ∧ unfold y reader = .done ly reader ∧
    unfold innerX reader = .done mx reader ∧ unfold innerY reader = .done my reader ∧
    unfold b reader = .done a reader := by cbv

private theorem root_available : Available base root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro supplied member; cases member)).result root base actual
private theorem a_available : Available base a := root_available.children a
  (List.mem_of_getElem? (show (children root)[0]? = some a by cbv))
private theorem b_available : Available base b := root_available.children b
  (List.mem_of_getElem? (show (children root)[1]? = some b by cbv))
private theorem x_available : Available base x := root_available.children x
  (List.mem_of_getElem? (show (children root)[2]? = some x by cbv))
private theorem y_available : Available base y := root_available.children y
  (List.mem_of_getElem? (show (children root)[3]? = some y by cbv))

private theorem effect (value : Value Nat Bool) (before : State Nat Bool)
    (ready : Ready before) (available : Available before value) :
    unfold value before = .done (val (unfold value before)) (unfold value before).state ∧
      Keeps before (unfold value before).state ∧
      Available (unfold value before).state (val (unfold value before)) := by
  cases value with
  | empty | reference | node | union => exact ⟨rfl,SourceEqualityRequiredCache.pure_keeps before ready,available⟩
  | mu entry body depth ordinary =>
      have replacements : InternedStoredSubstitution.Replacements before
          (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) := by
        intro name result found
        dsimp only at found
        split at found
        · cases found; exact available
        · cases found
      obtain ⟨result,after,done,kept,output,_⟩ := SourceCurrentStoredReconstruction.execute body _ before ready
        (available.children body List.mem_cons_self) replacements
      have unfolded : unfold (.mu entry body depth ordinary) before = .done result after := done
      rw [unfolded]
      exact ⟨rfl,kept,output⟩

private theorem x_effect : unfold x base = .done lx ux.state ∧ Keeps base ux.state ∧ Available ux.state lx :=
  effect x base base_ready x_available
private theorem y_effect : unfold y ux.state = .done ly uy.state ∧ Keeps ux.state uy.state ∧ Available uy.state ly :=
  effect y ux.state x_effect.2.1.ready (x_effect.2.1.available y y_available)
private theorem innerX_available : Available uy.state innerX :=
  (y_effect.2.1.available lx x_effect.2.2).children innerX
    (List.mem_of_getElem? (show (children lx)[1]? = some innerX by cbv))
private theorem innerY_available : Available uy.state innerY :=
  y_effect.2.2.children innerY (List.mem_of_getElem? (show (children ly)[1]? = some innerY by cbv))
private theorem innerX_effect : unfold innerX uy.state = .done mx vx.state ∧ Keeps uy.state vx.state ∧ Available vx.state mx :=
  effect innerX uy.state y_effect.2.1.ready innerX_available
private theorem innerY_effect : unfold innerY vx.state = .done my vy.state ∧ Keeps vx.state vy.state ∧ Available vy.state my :=
  effect innerY vx.state innerX_effect.2.1.ready (innerX_effect.2.1.available innerY innerY_available)
private theorem before_b : Keeps base vy.state :=
  x_effect.2.1.trans (y_effect.2.1.trans (innerX_effect.2.1.trans innerY_effect.2.1))
private theorem b_effect : Keeps vy.state reader :=
  (effect b vy.state before_b.ready (before_b.available b b_available)).2.1
private theorem reader_ready : Ready reader := b_effect.ready
private theorem kept : Keeps base reader := before_b.trans b_effect

private theorem paired (first second : Value Nat Bool) (member : (first,second) ∈ pairs) :
    Mutual relation first second := ⟨Or.inr (Or.inl member),Or.inr (Or.inr member)⟩
private theorem ab : Mutual relation a b := paired a b List.mem_cons_self
private theorem xy : Mutual relation x y := paired x y (by simp only [pairs]; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem layers : Mutual relation lx ly := paired lx ly (by
  simp only [pairs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
private theorem inners : Mutual relation innerX innerY := paired innerX innerY (by
  simp only [pairs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
private theorem inner_layers : Mutual relation mx my := paired mx my (by
  simp only [pairs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

private def IsMu (value : Value Nat Bool) : Prop :=
  ∃ entry body depth ordinary, value = .mu entry body depth ordinary
private theorem mu_local (first second left right : Value Nat Bool)
    (firstMu : IsMu first) (secondMu : IsMu second)
    (firstCall : unfold first reader = .done left reader)
    (secondCall : unfold second reader = .done right reader)
    (pair : relation left right) : Local reader relation first second := by
  obtain ⟨entry,body,depth,ordinary,rfl⟩ := firstMu
  obtain ⟨other,later,next,last,rfl⟩ := secondMu
  refine ⟨?_,?_,?_⟩
  · intro name impossible
    cases impossible
  · intro row impossible
    cases impossible
  · intro value member
    simp only [successors,firstCall,List.mem_singleton] at member
    subst value
    exact ⟨right,.step (.seed List.mem_cons_self) (by simp only [successors,secondCall,List.mem_singleton]),pair⟩

private theorem reverse_children {first second : List (Value Nat Bool)}
    (pairs : All₂ (Mutual relation) first second) : All₂ (Mutual relation) second first := by
  induction pairs with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.2,head.1⟩ ih
private theorem reverse_rows {first second : List (EdgeValue Nat Bool)}
    (pairs : All₂ (RowMatch (Mutual relation)) first second) : All₂ (RowMatch (Mutual relation)) second first := by
  induction pairs with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1.symm,head.2.1.symm,reverse_children head.2.2⟩ ih
private theorem pair_left {first second : List (EdgeValue Nat Bool)}
    (pairs : All₂ (RowMatch (Mutual relation)) first second)
    (row : EdgeValue Nat Bool) (member : row ∈ first) :
    ∃ other ∈ second, RowMatch (Mutual relation) row other := by
  induction pairs with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_,List.mem_cons_self,head⟩
      · obtain ⟨other,present,pair⟩ := ih member
        exact ⟨other,List.mem_cons_of_mem _ present,pair⟩
private theorem ordinary_local (first second : Value Nat Bool)
    (plain : Ordinary first) (pairs : All₂ (RowMatch (Mutual relation)) (nodeEdges first) (nodeEdges second)) :
    Local reader relation first second := by
  refine ⟨?_,?_,?_⟩
  · intro name impossible
    subst first
    cases plain
  · intro row member
    obtain ⟨other,present,pair⟩ := pair_left pairs row member
    exact ⟨other,⟨second,.seed List.mem_cons_self,present⟩,pair⟩
  · intro next member
    cases first <;> try cases plain <;> cases member

private def row (value : Value Nat Bool) (index : Nat) : EdgeValue Nat Bool :=
  (nodeEdges value)[index]?.getD (.mk ⟨0,⟨0,[],false⟩⟩ [])
private theorem outer_rows : All₂ (RowMatch (Mutual relation)) (nodeEdges lx) (nodeEdges ly) := by
  rw [show nodeEdges lx = [row lx 0,row lx 1] by cbv,
    show nodeEdges ly = [row ly 0,row ly 1] by cbv]
  refine .cons ⟨by cbv,by cbv,?_⟩ (.cons ⟨by cbv,by cbv,?_⟩ .nil)
  · rw [show (row lx 0).children = [] by cbv,show (row ly 0).children = [] by cbv]
    exact .nil
  · rw [show (row lx 1).children = [x,innerX] by cbv,show (row ly 1).children = [y,innerY] by cbv]
    exact .cons xy (.cons inners .nil)
private theorem inner_rows : All₂ (RowMatch (Mutual relation)) (nodeEdges mx) (nodeEdges my) := by
  rw [show nodeEdges mx = [row mx 0,row mx 1] by cbv,
    show nodeEdges my = [row my 0,row my 1] by cbv]
  refine .cons ⟨by cbv,by cbv,?_⟩ (.cons ⟨by cbv,by cbv,?_⟩ .nil)
  · rw [show (row mx 0).children = [] by cbv,show (row my 0).children = [] by cbv]
    exact .nil
  · rw [show (row mx 1).children = [innerX,x,a] by cbv,show (row my 1).children = [innerY,y,b] by cbv]
    exact .cons inners (.cons xy (.cons ab .nil))

private theorem capture_forward : Local reader relation a b := by
  have reached : Productivity.Reachable (successors reader) [b] a := by
    apply Productivity.Reachable.step (Productivity.Reachable.seed List.mem_cons_self)
    cbv
    exact List.mem_cons_self
  have clause := SourceCurrentSourceDirectedCases.equal reader relation same a
  refine ⟨?_,?_,?_⟩
  · intro name named
    exact EpsilonUnion.reach_trans _ b a _ reached (clause.1 name named)
  · intro output member
    obtain ⟨other,origin,fields⟩ := clause.2.1 output member
    exact ⟨other,origin.from_seeds reader [a] [b]
      (fun value present => (List.mem_singleton.mp present) ▸ reached) other,fields⟩
  · intro value member
    obtain ⟨other,origin,pair⟩ := clause.2.2 value member
    exact ⟨other,EpsilonUnion.reach_trans _ b a _ reached origin,pair⟩
private theorem capture_backward : Local reader relation b a := by
  refine ⟨?_,?_,?_⟩
  · intro name impossible
    cbv at impossible
    cases impossible
  · intro output member
    cbv at member
    cases member
  · intro value member
    have found : successors reader b = [a] := by cbv
    rw [found] at member
    have sameValue := List.mem_singleton.mp member
    subst value
    exact ⟨a,.seed List.mem_cons_self,same a⟩

private theorem simulation : Directed reader relation := by
  intro first second pair
  rcases pair with rfl | member | member
  · exact SourceCurrentSourceDirectedCases.equal reader relation same first
  · simp only [pairs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact capture_forward
    · exact mu_local x y lx ly (by cbv; exact ⟨_,_,_,_,rfl⟩) (by cbv; exact ⟨_,_,_,_,rfl⟩) calls.2.2.1 calls.2.2.2.1 layers.1
    · exact ordinary_local lx ly (by cbv) outer_rows
    · exact mu_local innerX innerY mx my (by cbv; exact ⟨_,_,_,_,rfl⟩) (by cbv; exact ⟨_,_,_,_,rfl⟩)
        calls.2.2.2.2.1 calls.2.2.2.2.2.1 inner_layers.1
    · exact ordinary_local mx my (by cbv) inner_rows
  · simp only [pairs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact capture_backward
    · exact mu_local y x ly lx (by cbv; exact ⟨_,_,_,_,rfl⟩) (by cbv; exact ⟨_,_,_,_,rfl⟩) calls.2.2.2.1 calls.2.2.1 layers.2
    · exact ordinary_local ly lx (by cbv) (reverse_rows outer_rows)
    · exact mu_local innerY innerX my mx (by cbv; exact ⟨_,_,_,_,rfl⟩) (by cbv; exact ⟨_,_,_,_,rfl⟩)
        calls.2.2.2.2.2.1 calls.2.2.2.2.1 inner_layers.2
    · exact ordinary_local my mx (by cbv) (reverse_rows inner_rows)

private def Used (value : Value Nat Bool) : Prop :=
  ∃ entry body depth ordinary, value = .mu entry body depth ordinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true

private theorem productive : EpsilonUnion.Accepts
    (MergedFreshOrdinaryGraph.graph reader (fun guard _ => guard)) x (.node 2 []) := by
  have origin : Origin reader [x] (row lx 0) := by
    refine ⟨lx,.step (.seed List.mem_cons_self) ?_,?_⟩
    · have found : successors reader x = [lx] := by cbv
      rw [found]
      exact List.mem_cons_self
    · cbv
      exact List.mem_cons_self
  apply MergedFreshOrdinaryExposureLanguage.origin_accepts reader (fun guard _ => guard) x (row lx 0) origin (.node 2 [])
  exact ⟨[],by cbv,.nil,by cbv⟩

/-- The actual changed captures and nested used results have all finite observations and the same language. -/
private theorem checked_witness :
    build source [] empty = .done root base ∧ Ready reader ∧ Keeps base reader ∧
    Available reader a ∧ Available reader b ∧ Available reader x ∧ Available reader y ∧
    a ≠ b ∧ x ≠ y ∧ innerX ≠ innerY ∧
    build expression [a] reader = .done x reader ∧ build expression [b] reader = .done y reader ∧
    (children mx)[1]? = some x ∧ (children my)[1]? = some y ∧
    Used x ∧ Used y ∧ Used innerX ∧ Used innerY ∧
    (∀ depth, SourceCurrentOpenObservations.Same depth reader [a] [b]) ∧
    (∀ depth, SourceCurrentOpenObservations.Same depth reader [x] [y]) ∧
    EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph reader (fun guard _ => guard)) x (.node 2 []) ∧
    ∀ (meaning : Bool → Term Nat → Bool) (term : Term Nat),
      EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph reader meaning) x term ↔
      EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph reader meaning) y term := by
  refine ⟨actual,reader_ready,kept,kept.available a a_available,kept.available b b_available,
    kept.available x x_available,kept.available y y_available,?_,?_,?_,calls.1,calls.2.1,?_,?_,?_,?_,?_,?_,
    (fun depth => SourceCurrentOpenPreorderSimulation.same reader relation simulation depth a b ab),
    (fun depth => SourceCurrentOpenPreorderSimulation.same reader relation simulation depth x y xy),productive,?_⟩
  · cbv
    intro impossible
    cases impossible
  · cbv
    intro impossible
    cases impossible
  · cbv
    intro impossible
    cases impossible
  · cbv
  · cbv
  · cbv
    exact ⟨_,_,_,_,rfl,rfl⟩
  · cbv
    exact ⟨_,_,_,_,rfl,rfl⟩
  · cbv
    exact ⟨_,_,_,_,rfl,rfl⟩
  · cbv
    exact ⟨_,_,_,_,rfl,rfl⟩
  · exact SourceCurrentOpenObservationLanguage.directed reader relation simulation x y xy

/-- A source-built productive nested-binder pair preserves all finite observations under distinct captures. -/
theorem witness :
    build source [] empty = .done root base ∧ Ready reader ∧ Keeps base reader ∧
    Available reader a ∧ Available reader b ∧ Available reader x ∧ Available reader y ∧
    a ≠ b ∧ x ≠ y ∧ innerX ≠ innerY ∧
    build expression [a] reader = .done x reader ∧ build expression [b] reader = .done y reader ∧
    (children mx)[1]? = some x ∧ (children my)[1]? = some y ∧
    Used x ∧ Used y ∧ Used innerX ∧ Used innerY ∧
    (∀ depth, SourceCurrentOpenObservations.Same depth reader [a] [b]) ∧
    (∀ depth, SourceCurrentOpenObservations.Same depth reader [x] [y]) ∧
    EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph reader (fun guard _ => guard)) x (.node 2 []) ∧
    ∀ (meaning : Bool → Term Nat → Bool) (term : Term Nat),
      EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph reader meaning) x term ↔
      EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph reader meaning) y term := checked_witness

end MicroCFTA.SourceCurrentChangingCaptureBinderExample
