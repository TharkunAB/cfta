import MicroCFTA.SourceRecursiveIntersectionLeafNode
import MicroCFTA.InternedNodeSetCongruence

/-!
# Exact identity of literal leaf-row products

A matched nullary top row reuses the original resident marker edge.
An arity mismatch executes the actual empty-child edge constructor.
The ordered walk retains those effects. Final node normalization either
removes every row or reuses the original resident singleton marker node.
Either input can contain the singleton marker row. Other symbols and
arities can repeat. No recursive child-call completion is assumed.
-/
namespace MicroCFTA.SourceRecursiveIntersectionLeafIdentity
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedNodeSetCongruence
open InternedBinderProtocol (NodeKey NodeRef)
open SourceRecursiveIntersectionKernel
open EqualityLeafProjectionPhysical (dead)

variable {Symbol Guard : Type}

/-- Reconstructing a resident nullary edge reuses its complete payload and cache state. -/
theorem resident_leaf_edge_replay [DecidableEq (EdgeKey Symbol Guard)]
    (marker : EdgeValue Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (resident : EdgeResident state marker) (leaf : marker.children = []) :
    run (makeEdge marker.entry.key.symbol marker.entry.key.constraint []) state = (marker, state) := by
  have stored : state.edgeRecords marker.entry.key = some marker := resident
  have installed := (facts.coherent.edges marker.entry.key marker resident).1
  have references := (facts.coherent.edges marker.entry.key marker resident).2.2
  have keyChildren : marker.entry.key.children = [] := by
    rw [leaf, List.map_nil] at references
    exact references.symm
  have key : (⟨marker.entry.key.symbol, [], marker.entry.key.constraint⟩ : EdgeKey Symbol Guard) =
      marker.entry.key :=
    congrArg (fun children : List NodeRef =>
      (⟨marker.entry.key.symbol, children, marker.entry.key.constraint⟩ : EdgeKey Symbol Guard)) keyChildren.symm
  simp only [makeEdge, List.map_nil, run, edgeStep, key, Cache.intern,
    installed, keepFirst, stored, Option.getD_some]

/-- The original singleton marker node is the exact canonical node-cache hit. -/
theorem resident_marker_replay [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (marker : EdgeValue Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state)
    (resident : Resident state (.node entry [marker] 0 [])) (leaf : marker.children = []) :
    run (makeNode [marker]) state = (.node entry [marker] 0 [], state) := by
  have stored := resident entry rfl
  obtain ⟨actual, _, fields⟩ := facts.coherent.nodes entry.key _ stored
  have key : entry.key = .node [marker.entry.identity] := fields.2.1
  have installed := resident_entry state facts.coherent _ resident entry rfl
  rw [key] at installed stored
  have canonical : canonicalEdges (surviving [marker]) = [marker] := by
    simp [surviving, leaf, canonicalEdges, EnumerationBuilderCaches.canonicalIds, List.eraseDups_cons]
  simp only [makeNode, canonical, List.map_singleton, run, nodeStep,
    Cache.intern, installed, keepFirst, stored, Option.getD_some]

private theorem edge_marker_complete [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard top : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (marker left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (resident : EdgeResident state.heap marker) (leaf : marker.children = [])
    (which : left = marker ∨ right = marker)
    (symbol : left.entry.key.symbol = right.entry.key.symbol)
    (leftTop : left.entry.key.constraint = top) (rightTop : right.entry.key.constraint = top) :
    ∃ row after, edge emptyGuard conjoin call left right state = .done row after ∧
      Facts after.heap ∧ Grows state.heap after.heap ∧ EdgeResident after.heap row ∧
      (dead row = true ∨ row = marker) := by
  by_cases arity : left.children.length = right.children.length
  · have leftLeaf : left.children = [] := by
      rcases which with first | second
      · simpa only [first] using leaf
      · apply List.eq_nil_of_length_eq_zero
        rw [arity, second, leaf]
        rfl
    have markerTop : marker.entry.key.constraint = top := by
      rcases which with first | second
      · simpa only [first] using leftTop
      · simpa only [second] using rightTop
    have leftSymbol : left.entry.key.symbol = marker.entry.key.symbol := by
      rcases which with first | second
      · exact congrArg (fun row : EdgeValue Symbol Guard => row.entry.key.symbol) first
      · exact symbol.trans (congrArg (fun row : EdgeValue Symbol Guard => row.entry.key.symbol) second)
    have replayed := resident_leaf_edge_replay marker state.heap facts resident leaf
    have actual : edge emptyGuard conjoin call left right state =
        work (makeEdge marker.entry.key.symbol marker.entry.key.constraint []) state := by
      unfold edge
      simp only [arity, ↓reduceIte]
      rw [leftLeaf]
      change work (makeEdge left.entry.key.symbol
        (conjoin left.entry.key.constraint right.entry.key.constraint) []) state = _
      rw [leftSymbol, leftTop, rightTop, conjoinTop, markerTop]
    refine ⟨marker, state, ?_, facts, grows_refl _, resident, Or.inr rfl⟩
    rw [actual]
    simp only [work, replayed]
  · let made := run (makeEdge left.entry.key.symbol emptyGuard [.empty]) state.heap
    have checked := edge_verified left.entry.key.symbol emptyGuard [.empty] state.heap facts (by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact empty_available state.heap)
    have children := InternedShallowValues.makeEdge_children left.entry.key.symbol emptyGuard [.empty]
      state.heap facts.coherent facts.cached (by
        intro value member
        have same := List.mem_singleton.mp member
        subst value
        exact empty_available state.heap)
    refine ⟨made.1, {state with heap := made.2}, ?_, checked.facts, checked.growth,
      checked.result _ _ rfl, Or.inl ?_⟩
    · simp only [edge, arity, ↓reduceIte, work]
      rfl
    · change (run (makeEdge left.entry.key.symbol emptyGuard [.empty]) state.heap).1.children.any
        (fun child => child.referenceOf == .empty) = true
      rw [children]
      rfl

private theorem walk_marker_complete [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard top : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (marker : EdgeValue Symbol Guard) (jobs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (facts : Facts state.heap)
    (resident : EdgeResident state.heap marker) (leaf : marker.children = [])
    (good : ∀ job ∈ jobs, (job.1 = marker ∨ job.2 = marker) ∧
      job.1.entry.key.symbol = job.2.entry.key.symbol ∧
      job.1.entry.key.constraint = top ∧ job.2.entry.key.constraint = top) :
    ∃ rows after, walk (fun job => edge emptyGuard conjoin call job.1 job.2) jobs state = .done rows after ∧
      Facts after.heap ∧ Grows state.heap after.heap ∧
      (∀ row ∈ rows, EdgeResident after.heap row) ∧
      (∀ row ∈ rows, dead row = true ∨ row = marker) := by
  induction jobs generalizing state with
  | nil =>
      refine ⟨[], state, rfl, facts, grows_refl _, ?_, ?_⟩ <;> intro row member <;> cases member
  | cons first rest ih =>
      have firstGood := good first List.mem_cons_self
      obtain ⟨row, middle, firstDone, middleFacts, firstGrowth, rowResident, rowShape⟩ :=
        edge_marker_complete emptyGuard top conjoin conjoinTop call marker first.1 first.2 state facts
          resident leaf firstGood.1 firstGood.2.1 firstGood.2.2.1 firstGood.2.2.2
      obtain ⟨rows, after, restDone, afterFacts, restGrowth, residents, shapes⟩ :=
        ih middle middleFacts (edge_grows state.heap middle.heap firstGrowth marker resident)
          (fun job member => good job (List.mem_cons_of_mem _ member))
      refine ⟨row :: rows, after, ?_, afterFacts, grows_trans firstGrowth restGrowth, ?_, ?_⟩
      · simp only [walk, firstDone, Result.bind, restDone]
      · intro actual member
        rcases List.mem_cons.mp member with rfl | tail
        · exact edge_grows middle.heap after.heap restGrowth actual rowResident
        · exact residents actual tail
      · intro actual member
        rcases List.mem_cons.mp member with rfl | tail
        · exact rowShape
        · exact shapes actual tail

/-- Either literal marker-row operand yields Empty or the original resident marker node. -/
theorem node_marker_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (top : Guard) (conjoinTop : conjoin top top = top)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (markerEntry : Interned NodeKey) (markerRow : EdgeValue Symbol Guard)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (markerAvailable : Available state.heap (.node markerEntry [markerRow] 0 []))
    (leaf : markerRow.children = []) (side : left = [markerRow] ∨ right = [markerRow])
    (leftTop : ∀ row ∈ left, row.entry.key.constraint = top)
    (rightTop : ∀ row ∈ right, row.entry.key.constraint = top) :
    ∃ value final, node emptyGuard conjoin call left right state = .done value final ∧
      Facts final.heap ∧ Available final.heap value ∧ Grows state.heap final.heap ∧
      (value = .empty ∨ value = .node markerEntry [markerRow] 0 []) := by
  have markerResident : EdgeResident state.heap markerRow :=
    resident_edges state.heap facts.linked _ markerAvailable.resident markerRow
      (by simp [nodeEdges])
  have good : ∀ job ∈ pairs left right, (job.1 = markerRow ∨ job.2 = markerRow) ∧
      job.1.entry.key.symbol = job.2.entry.key.symbol ∧
      job.1.entry.key.constraint = top ∧ job.2.entry.key.constraint = top := by
    intro job member
    obtain ⟨first, firstIn, second, secondIn, sameSymbol, same⟩ :=
      (SymbolicHashJoin.hashJoin_member (fun row : EdgeValue Symbol Guard => row.entry.key.symbol)
        Prod.mk left right job).mp member
    rw [← same]
    refine ⟨?_, sameSymbol, leftTop first firstIn, rightTop second secondIn⟩
    rcases side with leftOnly | rightOnly
    · exact Or.inl (List.mem_singleton.mp (leftOnly ▸ firstIn))
    · exact Or.inr (List.mem_singleton.mp (rightOnly ▸ secondIn))
  obtain ⟨rows, after, walked, afterFacts, growth, residents, shapes⟩ :=
    walk_marker_complete emptyGuard top conjoin conjoinTop call markerRow (pairs left right)
      state facts markerResident leaf good
  let made := run (makeNode rows) after.heap
  have checked := node_verified rows after.heap afterFacts residents
  have markerAfter := edge_grows state.heap after.heap growth markerRow markerResident
  have nodeAfter := resident_grows state.heap after.heap growth
    (.node markerEntry [markerRow] 0 []) markerAvailable.resident
  refine ⟨made.1, {after with heap := made.2}, ?_, checked.facts, checked.result _ _ rfl,
    grows_trans growth checked.growth, ?_⟩
  · simp only [node, walked, Result.bind, work]
    rfl
  · change (run (makeNode rows) after.heap).1 = .empty ∨
      (run (makeNode rows) after.heap).1 = .node markerEntry [markerRow] 0 []
    have onlyLive : ∀ row ∈ surviving rows, row = markerRow := by
      intro row member
      have selected := List.mem_filter.mp member
      rcases shapes row selected.1 with killed | same
      · have live : dead row = false := by
          simpa only [dead, Bool.not_eq_true'] using selected.2
        rw [killed] at live
        cases live
      · exact same
    cases kept : surviving rows with
    | nil =>
        left
        simp [makeNode, kept, canonicalEdges, EnumerationBuilderCaches.canonicalIds, run]
    | cons first rest =>
        right
        have headSame := onlyLive first (by rw [kept]; exact List.mem_cons_self)
        have markerPresent : markerRow ∈ surviving rows := by
          rw [kept, headSame]
          exact List.mem_cons_self
        have request : makeNode rows = makeNode [markerRow] := by
          apply makeNode_same_members after.heap afterFacts.coherent rows [markerRow] residents
            (by intro row member; have same := List.mem_singleton.mp member; subst row; exact markerAfter)
          intro row
          constructor
          · intro member
            have same := onlyLive row member
            subst row
            simp [surviving, leaf]
          · intro member
            have same : row = markerRow := by simpa [surviving, leaf] using member
            subst row
            exact markerPresent
        rw [request]
        exact congrArg Prod.fst (resident_marker_replay markerEntry markerRow after.heap afterFacts nodeAfter leaf)

end MicroCFTA.SourceRecursiveIntersectionLeafIdentity
