import MicroCFTA.SourceRecursiveIntersectionProductEdgeShape

/-!
# Normalized synchronous rows of actual ordinary parents

The source rows retain full guards and ordered child pairs. Actual child
replay determines their copied identities and the empty-child filter.
The resulting membership and rejection laws follow from completed execution.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SymbolicGraphView
open SourcePreparedSharedRows (interpretedEdge)
open EqualityLeafProjectionPhysical (dead)

/-- Source synchronous product membership reads the original physical edges and their complete guards. -/
theorem physical_product_member [DecidableEq Symbol] (holds : Guard → Term Symbol → Bool)
    (left right : List (EdgeValue Symbol Guard)) (original : Language.Edge (Value Symbol Guard × Value Symbol Guard) Symbol) :
    original ∈ Language.intersect (fun (_ : Value Symbol Guard) => left.map (interpretedEdge holds))
      (fun (_ : Value Symbol Guard) => right.map (interpretedEdge holds)) (.empty, .empty) ↔
    ∃ first ∈ left, ∃ second ∈ right, first.entry.key.symbol = second.entry.key.symbol ∧
      first.children.length = second.children.length ∧ original =
        ⟨first.entry.key.symbol, first.children.zip second.children,
          fun term => holds first.entry.key.constraint term && holds second.entry.key.constraint term⟩ := by
  rw [mem_intersect_iff]
  constructor
  · rintro ⟨first, firstIn, second, secondIn, symbol, arity, same⟩
    obtain ⟨first, firstMember, rfl⟩ := List.mem_map.mp firstIn
    obtain ⟨second, secondMember, rfl⟩ := List.mem_map.mp secondIn
    exact ⟨first, firstMember, second, secondMember, symbol, arity, same⟩
  · rintro ⟨first, firstIn, second, secondIn, symbol, arity, same⟩
    exact ⟨interpretedEdge holds first, List.mem_map.mpr ⟨first, firstIn, rfl⟩,
      interpretedEdge holds second, List.mem_map.mpr ⟨second, secondIn, rfl⟩, symbol, arity, same⟩

/-- Keep exactly the source product rows whose actual copied children have no empty identity. -/
def keepProduct
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (domain : Interned DomainKey) (state : Machine Symbol Guard)
    (original : Language.Edge (Value Symbol Guard × Value Symbol Guard) Symbol) : Bool :=
  !original.children.any (fun pair => (childValue call domain state pair).referenceOf == .empty)

/-- The source product filter is exactly the actual replayed row's dead-child decision. -/
theorem edge_keep_product [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (sameArity : left.children.length = right.children.length) (row : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (call domain) left right state = .done row state) (holds : Guard → Term Symbol → Bool) :
    keepProduct call domain state ⟨left.entry.key.symbol, left.children.zip right.children,
      fun term => holds left.entry.key.constraint term && holds right.entry.key.constraint term⟩ = !dead row := by
  have fields := edge_children_replay emptyGuard conjoin call calls replay domain left right state valid known leftResident rightResident sameArity row done
  have children := replayed_children_map call domain state _ _ fields.2.2
  simp only [keepProduct, dead, children, List.any_map, Function.comp_def]

/-- A completed ordinary parent has exactly the renamed live synchronous product rows. -/
theorem node_product_members [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : node emptyGuard conjoin (call domain) left right state = .done value final)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (row : Language.Edge (Value Symbol Guard) Symbol) :
    row ∈ (nodeEdges value).map (interpretedEdge holds) ↔
      ∃ original ∈ Language.intersect (fun (_ : Value Symbol Guard) => left.map (interpretedEdge holds))
        (fun (_ : Value Symbol Guard) => right.map (interpretedEdge holds)) (.empty, .empty),
        keepProduct call domain final original = true ∧ row = renameEdge (childValue call domain final) original := by
  have checked := node_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  have finalValid : Valid final := by simpa only [done, Result.state] using checked.valid
  have growth : Extension state final := by simpa only [done, Result.state] using checked.extension
  have finalKnown := known.grows domain growth
  have leftFinal := fun edge member => edge_grows _ _ growth.heap edge (leftResident edge member)
  have rightFinal := fun edge member => edge_grows _ _ growth.heap edge (rightResident edge member)
  constructor
  · intro member
    obtain ⟨physical, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨first, firstIn, second, secondIn, symbol, returned, live⟩ :=
      (node_members_replay emptyGuard conjoin call calls replay domain left right state valid known leftResident rightResident value final done physical).mp selected
    have arity := (edge_live_product emptyGuard conjoin call calls replay domain first second final finalValid finalKnown
      (leftFinal first firstIn) (rightFinal second secondIn) physical returned live).1
    refine ⟨_, (physical_product_member holds left right _).mpr ⟨first, firstIn, second, secondIn, symbol, arity, rfl⟩, ?_, ?_⟩
    · rw [edge_keep_product emptyGuard conjoin call calls replay domain first second final finalValid finalKnown
        (leftFinal first firstIn) (rightFinal second secondIn) arity physical returned holds, live]
      rfl
    · exact edge_renamed_product emptyGuard conjoin call calls replay domain first second final finalValid finalKnown
        (leftFinal first firstIn) (rightFinal second secondIn) physical returned live holds conjoined
  · rintro ⟨original, member, kept, same⟩
    obtain ⟨first, firstIn, second, secondIn, symbol, arity, rfl⟩ := (physical_product_member holds left right original).mp member
    obtain ⟨rows, _, related, _⟩ := node_rows_replay emptyGuard conjoin call calls replay domain left right state valid known
      leftResident rightResident value final done
    obtain ⟨physical, _, returned⟩ := SymbolicSmartRows.all₂_child _ _ _ related (first, second)
      ((pairs_member left right (first, second)).mpr ⟨firstIn, secondIn, symbol⟩)
    have keepEq := edge_keep_product emptyGuard conjoin call calls replay domain first second final finalValid finalKnown
      (leftFinal first firstIn) (rightFinal second secondIn) arity physical returned holds
    have live : dead physical = false := by simpa only [keepEq, Bool.not_eq_true'] using kept
    refine List.mem_map.mpr ⟨physical, ?_, ?_⟩
    · exact (node_members_replay emptyGuard conjoin call calls replay domain left right state valid known leftResident rightResident
        value final done physical).mpr ⟨first, firstIn, second, secondIn, symbol, returned, live⟩
    · exact (edge_renamed_product emptyGuard conjoin call calls replay domain first second final finalValid finalKnown
        (leftFinal first firstIn) (rightFinal second secondIn) physical returned live holds conjoined).trans same.symm

/-- Each rejected synchronous row has the exact actual empty-child rejection reason. -/
theorem node_product_rejected [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : node emptyGuard conjoin (call domain) left right state = .done value final)
    (holds : Guard → Term Symbol → Bool) (target : Automaton (Value Symbol Guard) Symbol) (empty : target .empty = [])
    (original : Language.Edge (Value Symbol Guard × Value Symbol Guard) Symbol)
    (member : original ∈ Language.intersect (fun (_ : Value Symbol Guard) => left.map (interpretedEdge holds))
      (fun (_ : Value Symbol Guard) => right.map (interpretedEdge holds)) (.empty, .empty)) (rejected : keepProduct call domain final original = false) :
    DropReason target (childValue call domain final) original := by
  obtain ⟨first, firstIn, second, secondIn, symbol, arity, rfl⟩ := (physical_product_member holds left right original).mp member
  have checked := node_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  have finalValid : Valid final := by simpa only [done, Result.state] using checked.valid
  have growth : Extension state final := by simpa only [done, Result.state] using checked.extension
  obtain ⟨rows, _, related, _⟩ := node_rows_replay emptyGuard conjoin call calls replay domain left right state valid known
    leftResident rightResident value final done
  obtain ⟨physical, _, returned⟩ := SymbolicSmartRows.all₂_child _ _ _ related (first, second)
    ((pairs_member left right (first, second)).mpr ⟨firstIn, secondIn, symbol⟩)
  have keepEq := edge_keep_product emptyGuard conjoin call calls replay domain first second final finalValid (known.grows domain growth)
    (edge_grows _ _ growth.heap _ (leftResident first firstIn)) (edge_grows _ _ growth.heap _ (rightResident second secondIn)) arity physical returned holds
  have isDead : dead physical = true := by simpa only [keepEq, Bool.not_eq_false'] using rejected
  exact edge_product_rejected emptyGuard conjoin call calls replay domain first second final finalValid (known.grows domain growth)
    (edge_grows _ _ growth.heap _ (leftResident first firstIn)) (edge_grows _ _ growth.heap _ (rightResident second secondIn))
    arity physical returned isDead holds target empty

end MicroCFTA.SourceRecursiveIntersectionKernel
