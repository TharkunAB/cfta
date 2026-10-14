import MicroCFTA.SourceRecursiveIntersectionKernel

/-!
# Stable finite observations of recursive source execution

A larger proof bound retains every outcome other than exhaustion. The
equality includes complete results, pending keys, other failures, and all
returned caches. Exhaustion remains distinct from an empty language.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain

/-- A source observation reached its result before the recursive proof bound was exhausted. -/
def NonExhausted : Result Symbol Guard A → Prop
  | .failed .exhausted _ => False
  | _ => True

/-- Agreement at each reached request preserves ordered effect composition. -/
theorem bind_congr (first second : Result Symbol Guard A)
    (firstNext secondNext : A → Machine Symbol Guard → Result Symbol Guard B)
    (priorAgreement : NonExhausted first → second = first)
    (nextAgreement : ∀ value after, NonExhausted (firstNext value after) → secondNext value after = firstNext value after)
    (complete : NonExhausted (first.bind firstNext)) :
    second.bind secondNext = first.bind firstNext := by
  cases first with
  | done value after =>
      rw [priorAgreement True.intro]
      exact nextAgreement value after complete
  | failed failure after =>
      have reached : NonExhausted (Result.failed failure after : Result Symbol Guard A) := by
        cases failure <;> simp_all [Result.bind, NonExhausted]
      rw [priorAgreement reached]
      rfl

/-- Ordered source request lists preserve their complete actual cache when reached calls agree. -/
theorem walk_congr (first second : A → Machine Symbol Guard → Result Symbol Guard B)
    (requests : List A) (state : Machine Symbol Guard)
    (agree : ∀ request state, NonExhausted (first request state) → second request state = first request state)
    (complete : NonExhausted (walk first requests state)) : walk second requests state = walk first requests state := by
  induction requests generalizing state with
  | nil => simp only [walk]
  | cons head tail ih =>
      simp only [walk] at complete ⊢
      apply bind_congr _ _ _ _ (agree head state) _ complete
      intro value after completed
      apply bind_congr _ _ _ _ (fun reached => ih after reached) _ completed
      intro values final reached
      rfl

/-- All reached recursive requests agree on their exact complete source outcome. -/
def Agreement
    (first second : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ domain left right state, NonExhausted (first domain left right state) →
    second domain left right state = first domain left right state

/-- Mu allocation and optional-binder effects retain identical results after reached body requests agree. -/
theorem mu_congr [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (agree : Agreement first second) (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (complete : NonExhausted (mu first domain left right state)) : mu second domain left right state = mu first domain left right state := by
  cases leftId : SourceRecursiveIntersectionControl.identity left <;>
    cases rightId : SourceRecursiveIntersectionControl.identity right <;> simp only [mu, leftId, rightId] at complete ⊢
  all_goals try rfl
  apply bind_congr _ _ _ _ (agree _ _ _ _) _ complete
  intro value after reached
  rfl

/-- Actual original-binding lookup preserves the next exact recursive request. -/
theorem reference_congr
    (first second : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (agree : Agreement first second) (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard)
    (left : Bool) (state : Machine Symbol Guard) (complete : NonExhausted (reference first domain name other left state)) :
    reference second domain name other left state = reference first domain name other left state := by
  by_cases bound : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · simp only [reference, bound, ite_true] at complete ⊢
    cases read : SourcePreparedSharedRows.read state.heap name with
    | none => rfl
    | some value =>
        simp only [read] at complete ⊢
        cases left
        · exact agree domain other value state complete
        · exact agree domain value other state complete
  · simp only [reference, bound, ite_false]

/-- Guarded edge construction retains exact child order and cache effects after reached child calls agree. -/
theorem edge_congr [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (first second : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (agree : ∀ left right state, NonExhausted (first left right state) → second left right state = first left right state)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (complete : NonExhausted (edge emptyGuard conjoin first left right state)) :
    edge emptyGuard conjoin second left right state = edge emptyGuard conjoin first left right state := by
  by_cases arity : left.children.length = right.children.length
  · simp only [edge, arity, ite_true] at complete ⊢
    apply bind_congr _ _ _ _ _ _ complete
    · intro reached
      exact walk_congr _ _ _ state (fun pair current => agree pair.1 pair.2 current) reached
    · intro values after reached
      rfl
  · simp only [edge, arity, ite_false]

/-- Equal-symbol row occurrence order and node cache effects remain exact after reached edge calls agree. -/
theorem node_congr [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (first second : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (agree : ∀ left right state, NonExhausted (first left right state) → second left right state = first left right state)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (complete : NonExhausted (node emptyGuard conjoin first left right state)) :
    node emptyGuard conjoin second left right state = node emptyGuard conjoin first left right state := by
  simp only [node] at complete ⊢
  apply bind_congr _ _ _ _ _ _ complete
  · intro reached
    exact walk_congr _ _ _ state (fun pair current => edge_congr emptyGuard conjoin first second agree pair.1 pair.2 current) reached
  · intro values after reached
    rfl

/-- Full physical source control preserves its exact result after all reached recursive requests agree. -/
theorem onNode_congr [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (first second : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (agree : Agreement first second) (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (complete : NonExhausted (onNode emptyGuard conjoin first domain left right state)) :
    onNode emptyGuard conjoin second domain left right state = onNode emptyGuard conjoin first domain left right state := by
  cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
  | empty | self | repeated | unsupported => simp only [onNode, selected]
  | reset =>
      simp only [onNode, selected] at complete ⊢
      exact agree _ _ _ state complete
  | swap =>
      simp only [onNode, selected] at complete ⊢
      exact agree domain right left state complete
  | bothMu | leftMu | rightMu =>
      simp only [onNode, selected] at complete ⊢
      exact mu_congr first second agree domain left right state complete
  | leftUnion =>
      simp only [onNode, selected] at complete ⊢
      cases left <;> try rfl
      apply bind_congr _ _ _ _ _ _ complete
      · intro reached
        exact walk_congr _ _ _ state (fun member current => agree domain member right current) reached
      · intro values after reached
        rfl
  | rightUnion =>
      simp only [onNode, selected] at complete ⊢
      cases right <;> try rfl
      apply bind_congr _ _ _ _ _ _ complete
      · intro reached
        exact walk_congr _ _ _ state (fun member current => agree domain left member current) reached
      · intro values after reached
        rfl
  | leftReference =>
      simp only [onNode, selected] at complete ⊢
      cases left <;> try rfl
      rename_i name
      cases name <;> try rfl
      exact reference_congr first second agree domain _ right true state complete
  | rightReference =>
      simp only [onNode, selected] at complete ⊢
      cases right <;> try rfl
      rename_i name
      cases name <;> try rfl
      exact reference_congr first second agree domain _ left false state complete
  | ordinary =>
      simp only [onNode, selected] at complete ⊢
      cases left <;> cases right <;> try rfl
      exact node_congr emptyGuard conjoin (first domain) (second domain) (agree domain) _ _ state complete

/-- Every reached source observation retains the identical result and caches at all larger bounds. -/
theorem execute_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel extra : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (complete : NonExhausted (execute emptyGuard conjoin fuel domain left right state)) :
    execute emptyGuard conjoin (fuel + extra) domain left right state = execute emptyGuard conjoin fuel domain left right state := by
  induction fuel generalizing domain left right state with
  | zero => simp only [execute, NonExhausted] at complete
  | succ fuel ih =>
      rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
      simp only [execute] at complete ⊢
      exact onNode_congr emptyGuard conjoin _ _ (fun domain left right state reached => ih domain left right state reached)
        domain left right state complete

end MicroCFTA.SourceRecursiveIntersectionKernel
