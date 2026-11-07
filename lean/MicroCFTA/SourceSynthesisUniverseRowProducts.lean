import MicroCFTA.SourceSynthesisUniverseReferenceControl
import MicroCFTA.SourceSynthesisUniverseBody

/-!
# Actual universe row products in an entered source domain

The source kernel cuts off repeated open references before lookup. The
ordered child walk uses that cutoff for every catalog position. The arrow
self product first reads its closed marker, then cuts off both recursive
children. The final makeEdge request keeps its actual cache effects.
Products between a marker and the recursive universe remain separate.
-/
namespace MicroCFTA.SourceSynthesisUniverseRowProducts
open Cache InternedConstructorTemplates InternedBinderProtocol
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionKernel

private theorem walk_repeated {A B Symbol Guard : Type}
    (call : A → Machine Symbol Guard → Result Symbol Guard B) (request : A) (value : B)
    (returns : ∀ state, call request state = .done value state) (count : Nat) (state : Machine Symbol Guard) :
    walk call (List.replicate count request) state = .done (List.replicate count value) state := by
  induction count with
  | zero => simp only [List.replicate_zero, walk]
  | succ count ih => simp only [List.replicate_succ, walk, returns, Result.bind, ih]

section Kernel
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual repeated reference branch returns its placeholder without lookup or cache effects. -/
theorem execute_ref_self (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (name : Nat) (state : Machine Symbol Guard)
    (seen : pair name name ∈ domain.key.seen) :
    execute emptyGuard conjoin (fuel + 1) domain (.reference (.interned name)) (.reference (.interned name)) state =
      .done (repeatedValue (pair name name)) state := by
  have same : closedSelf (Value.reference (.interned name) : Value Symbol Guard)
      (.reference (.interned name)) = false := by simp [closedSelf, Value.free]
  have order : greater (Value.reference (.interned name) : Value Symbol Guard)
      (.reference (.interned name)) = false := by
    simp [greater, compareValue, tag, SourceRecursiveIntersectionSchedule.reference_interned]
  have selected := repeated_first domain.key (Value.reference (.interned name) : Value Symbol Guard)
    (.reference (.interned name)) rfl rfl same order name name rfl rfl seen
  simp only [execute, onNode, selected]

/-- An arbitrary catalog arity repeats the actual cutoff request in source order. -/
theorem walk_catalog (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (name arity : Nat) (state : Machine Symbol Guard)
    (seen : pair name name ∈ domain.key.seen) :
    walk (fun children : Value Symbol Guard × Value Symbol Guard =>
      execute emptyGuard conjoin (fuel + 1) domain children.1 children.2)
      (List.replicate arity (.reference (.interned name), .reference (.interned name))) state =
      .done (List.replicate arity (repeatedValue (pair name name))) state :=
  walk_repeated
    (fun children : Value Symbol Guard × Value Symbol Guard =>
      execute emptyGuard conjoin (fuel + 1) domain children.1 children.2)
    (.reference (.interned name), .reference (.interned name)) (repeatedValue (pair name name))
    (fun current => execute_ref_self emptyGuard conjoin fuel domain name current seen) arity state

/-- Equal catalog arities keep the literal ordered child results and final edge allocation. -/
theorem edge_catalog (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (name arity : Nat) (left right : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard)
    (leftChildren : left.children = List.replicate arity (.reference (.interned name)))
    (rightChildren : right.children = List.replicate arity (.reference (.interned name)))
    (seen : pair name name ∈ domain.key.seen) :
    edge emptyGuard conjoin (execute emptyGuard conjoin (fuel + 1) domain) left right state =
      work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint)
        (List.replicate arity (repeatedValue (pair name name)))) state := by
  simp only [edge, ite_true, leftChildren, rightChildren, List.zip_replicate',
    walk_catalog emptyGuard conjoin fuel domain name arity state seen, Result.bind]

/-- An arity mismatch runs the source empty-edge allocation without evaluating children. -/
theorem edge_catalog_mismatch (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (name leftArity rightArity : Nat) (left right : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard)
    (leftChildren : left.children = List.replicate leftArity (.reference (.interned name)))
    (rightChildren : right.children = List.replicate rightArity (.reference (.interned name)))
    (different : leftArity ≠ rightArity) :
    edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) left right state =
      work (makeEdge left.entry.key.symbol emptyGuard [.empty]) state := by
  simp only [edge, leftChildren, rightChildren, List.length_replicate, different, ite_false]

/-- A closed ordinary marker needs at most one reset before source self reuse. -/
theorem execute_marker_self (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth : Nat) (state : Machine Symbol Guard) :
    execute emptyGuard conjoin (fuel + 2) domain (.node entry rows depth []) (.node entry rows depth []) state =
      .done (.node entry rows depth []) state := by
  let marker : Value Symbol Guard := .node entry rows depth []
  have nonempty : hasEmpty marker marker = false := by simp [marker, hasEmpty, Value.referenceOf]
  have same : closedSelf marker marker = true := by simp [marker, closedSelf, Value.free, Value.referenceOf]
  have noReset : reset IntersectionEmptyDomain.emptyKey marker marker = false := rfl
  have emptySelf : decision IntersectionEmptyDomain.emptyDomain.key marker marker = .self :=
    self_first IntersectionEmptyDomain.emptyKey marker marker nonempty noReset same
  change execute emptyGuard conjoin (fuel + 2) domain marker marker state = .done marker state
  cases restart : reset domain.key marker marker with
  | false =>
      have selected := self_first domain.key marker marker nonempty restart same
      rw [execute, onNode, selected]
  | true =>
      have selected := reset_first domain.key marker marker nonempty restart
      rw [execute, onNode, selected, execute, onNode, emptySelf]

/-- The actual three-child arrow walk keeps its marker before both cutoff results. -/
theorem walk_arrow (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (name : Nat) (entry : Interned NodeKey)
    (rows : List (EdgeValue Symbol Guard)) (depth : Nat) (state : Machine Symbol Guard)
    (seen : pair name name ∈ domain.key.seen) :
    walk (fun children : Value Symbol Guard × Value Symbol Guard =>
      execute emptyGuard conjoin (fuel + 2) domain children.1 children.2)
      [(.node entry rows depth [], .node entry rows depth []),
        (.reference (.interned name), .reference (.interned name)),
        (.reference (.interned name), .reference (.interned name))] state =
      .done [.node entry rows depth [], repeatedValue (pair name name), repeatedValue (pair name name)] state := by
  simp only [walk, execute_marker_self emptyGuard conjoin fuel domain entry rows depth state,
    execute_ref_self emptyGuard conjoin (fuel + 1) domain name state seen, Result.bind]

/-- The distinguished-arrow self row executes its actual children and final makeEdge request. -/
theorem edge_arrow (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (name : Nat) (entry : Interned NodeKey)
    (rows : List (EdgeValue Symbol Guard)) (depth : Nat) (left right : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard)
    (leftChildren : left.children = [.node entry rows depth [], .reference (.interned name), .reference (.interned name)])
    (rightChildren : right.children = [.node entry rows depth [], .reference (.interned name), .reference (.interned name)])
    (seen : pair name name ∈ domain.key.seen) :
    edge emptyGuard conjoin (execute emptyGuard conjoin (fuel + 2) domain) left right state =
      work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint)
        [.node entry rows depth [], repeatedValue (pair name name), repeatedValue (pair name name)]) state := by
  have same : left.children.length = right.children.length := by rw [leftChildren, rightChildren]
  have zipped : left.children.zip right.children =
      [(.node entry rows depth [], .node entry rows depth []),
        (.reference (.interned name), .reference (.interned name)),
        (.reference (.interned name), .reference (.interned name))] := by
    rw [leftChildren, rightChildren]
    rfl
  simp only [edge, same, ite_true, zipped,
    walk_arrow emptyGuard conjoin fuel domain name entry rows depth state seen, Result.bind]

end Kernel

section SourceRows
variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- R121 actual catalog readback supplies the equal-child hypotheses and literal top guards. -/
theorem edge_catalog_readback (emptyGuard top : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (name : Nat) (descriptor : String × Nat) (left right : EdgeValue String Guard)
    (state : Machine String Guard)
    (leftRead : SourceSynthesisUniverseBody.RowKeys top (.interned name) descriptor left)
    (rightRead : SourceSynthesisUniverseBody.RowKeys top (.interned name) descriptor right)
    (seen : pair name name ∈ domain.key.seen) :
    edge emptyGuard conjoin (execute emptyGuard conjoin (fuel + 1) domain) left right state =
      work (makeEdge descriptor.1 (conjoin top top)
        (List.replicate descriptor.2 (repeatedValue (pair name name)))) state := by
  simpa only [leftRead.2, rightRead.2] using
    edge_catalog emptyGuard conjoin fuel domain name descriptor.2 left right state leftRead.1 rightRead.1 seen

/-- The actual diagonal entry derives every catalog cutoff before any reference lookup. -/
theorem edge_catalog_diagonal (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (entry : Interned NodeKey) (stored depth ordinary : Value String Guard) (arity : Nat)
    (left right : EdgeValue String Guard) (state : Machine String Guard) (valid : Cache.Valid state.domains)
    (leftChildren : left.children = List.replicate arity (.reference (.interned entry.identity)))
    (rightChildren : right.children = List.replicate arity (.reference (.interned entry.identity))) :
    let entered := SourceSynthesisUniverseReferenceControl.diagonal entry stored depth ordinary state
    edge emptyGuard conjoin (execute emptyGuard conjoin (fuel + 1) entered.1) left right
      {state with domains := entered.2} =
      work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint)
        (List.replicate arity (repeatedValue (pair entry.identity entry.identity))))
        {state with domains := entered.2} := by
  exact edge_catalog emptyGuard conjoin fuel _ _ arity left right _ leftChildren rightChildren
    (SourceSynthesisUniverseReferenceControl.diagonal_seen entry stored depth ordinary state valid)

/-- R121 actual marker readback supplies the closed marker used by the arrow product. -/
theorem edge_arrow_readback (emptyGuard top : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (name : Nat) (marker : Value String Guard) (left right : EdgeValue String Guard)
    (state : Machine String Guard) (markerRead : SourceSynthesisUniverseBody.RowReadback "(->)" top [] marker)
    (leftChildren : left.children = [marker, .reference (.interned name), .reference (.interned name)])
    (rightChildren : right.children = [marker, .reference (.interned name), .reference (.interned name)])
    (seen : pair name name ∈ domain.key.seen) :
    edge emptyGuard conjoin (execute emptyGuard conjoin (fuel + 2) domain) left right state =
      work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint)
        [marker, repeatedValue (pair name name), repeatedValue (pair name name)]) state := by
  obtain ⟨entry, markerEdge, markerEq, _, _⟩ := markerRead
  have markerNode : marker = .node entry [markerEdge] 0 [] := by
    simpa [maximumDepth, childFree, canonicalFree] using markerEq
  rw [markerNode] at leftChildren rightChildren ⊢
  exact edge_arrow emptyGuard conjoin fuel domain name entry [markerEdge] 0 left right state
    leftChildren rightChildren seen

end SourceRows
end MicroCFTA.SourceSynthesisUniverseRowProducts
