import MicroCFTA.SourceRecursiveIntersectionOrdinaryProductRows

/-!
# Complete physical fields of replayed product edges

An equal-arity actual edge retains its symbol, conjoined guard, and ordered
child requests. Each child replays in the same final cache. An arity mismatch
has the actual empty-child result and cannot survive node normalization.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open EqualityLeafProjectionPhysical (dead)

/-- A replayed equal-arity edge retains exact fields and actual final-cache child calls in order. -/
theorem edge_children_replay [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (sameArity : left.children.length = right.children.length) (row : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (call domain) left right state = .done row state) :
    row.entry.key.symbol = left.entry.key.symbol ∧ row.entry.key.constraint = conjoin left.entry.key.constraint right.entry.key.constraint ∧
      All₂ (fun pair child => call domain pair.1 pair.2 state = .done child state) (left.children.zip right.children) row.children := by
  obtain ⟨children, after, trace, built, symbol, guard, exactChildren⟩ :=
    edge_readback emptyGuard conjoin call calls domain left right state valid known leftResident rightResident sameArity row state done
  have walked := (walk_done_iff _ _ _ _ _).mpr trace
  have inputs : ∀ pair ∈ left.children.zip right.children, Available state.heap pair.1 ∧ Available state.heap pair.2 := by
    intro pair member
    have selected := List.of_mem_zip member
    exact ⟨valid.1.cached.edges left.entry.key left leftResident pair.1 selected.1,
      valid.1.cached.edges right.entry.key right rightResident pair.2 selected.2⟩
  have checked := children_checked call calls domain (left.children.zip right.children) state valid known inputs
  have afterValid : Valid after := by simpa only [walked, Result.state] using checked.valid
  have available := checked.result children after walked
  have builtChecked := work_checked after afterValid
    (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint) children) EdgeResident
    (InternedNestedFacts.edge_verified _ _ children after.heap afterValid.1 available)
  have growth : Extension after state := by simpa only [built, Result.state] using builtChecked.extension
  refine ⟨symbol, guard, ?_⟩
  rw [exactChildren]
  exact children_pointwise_replay call calls replay domain (left.children.zip right.children) state state children after valid known inputs walked growth

/-- A physical arity mismatch has an actual empty child and is removed by node normalization. -/
theorem edge_mismatch_dead [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state)
    (different : left.children.length ≠ right.children.length) (row : EdgeValue Symbol Guard) (after : Machine Symbol Guard)
    (done : edge emptyGuard conjoin call left right state = .done row after) : dead row = true := by
  have fields := edge_mismatch_readback emptyGuard conjoin call left right state valid different row after done
  simp only [dead, fields.2.2.1, List.any_cons, List.any_nil, Value.referenceOf, beq_self_eq_true, Bool.or_false]

/-- Every live replayed edge has equal source arity and the complete actual child product trace. -/
theorem edge_live_product [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (row : EdgeValue Symbol Guard) (done : edge emptyGuard conjoin (call domain) left right state = .done row state)
    (live : dead row = false) :
    left.children.length = right.children.length ∧ row.entry.key.symbol = left.entry.key.symbol ∧
      row.entry.key.constraint = conjoin left.entry.key.constraint right.entry.key.constraint ∧
      All₂ (fun pair child => call domain pair.1 pair.2 state = .done child state) (left.children.zip right.children) row.children := by
  by_cases same : left.children.length = right.children.length
  · exact ⟨same, edge_children_replay emptyGuard conjoin call calls replay domain left right state valid known leftResident rightResident same row done⟩
  · have impossible := edge_mismatch_dead emptyGuard conjoin (call domain) left right state valid same row state done
    rw [live] at impossible
    cases impossible

/-- A dead equal-arity product edge has an actual child call that returns EmptyNode in the same cache. -/
theorem edge_dead_child [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (sameArity : left.children.length = right.children.length) (row : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (call domain) left right state = .done row state) (isDead : dead row = true) :
    ∃ pair ∈ left.children.zip right.children, call domain pair.1 pair.2 state = .done .empty state := by
  have fields := edge_children_replay emptyGuard conjoin call calls replay domain left right state valid known
    leftResident rightResident sameArity row done
  obtain ⟨child, member, empty⟩ := List.any_eq_true.mp isDead
  have same : child = .empty := (EqualityLeafProjectionPhysical.reference_empty child).mp (by simpa only [beq_iff_eq] using empty)
  subst child
  exact (pointwise_result_member (fun pair => call domain pair.1 pair.2 state) (left.children.zip right.children) row.children state fields.2.2 .empty).mp member

end MicroCFTA.SourceRecursiveIntersectionKernel
