import MicroCFTA.SourceRecursiveIntersectionProductEdgeReadback
import MicroCFTA.SourcePreparedSharedRowsLanguage

/-!
# Renamed synchronous rows from actual product-edge execution

Successful pointwise replay determines one child map in the final cache.
Complete source guard conjunction then identifies the literal product row.
Dead equal-arity rows have the existing empty-child rejection reason.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SymbolicGraphView
open SourcePreparedSharedRows (interpretedEdge)

/-- Project a returned child record. The empty default is unused on proved successful replayed requests. -/
def childValue
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (domain : Interned DomainKey) (state : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) : Value Symbol Guard :=
  match call domain pair.1 pair.2 state with
  | .done value _ => value
  | .failed .. => .empty

/-- Every successful ordered child result is the corresponding value of the same actual final-cache map. -/
theorem replayed_children_map
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (domain : Interned DomainKey) (state : Machine Symbol Guard) (requests : List (Value Symbol Guard × Value Symbol Guard))
    (values : List (Value Symbol Guard))
    (related : All₂ (fun pair child => call domain pair.1 pair.2 state = .done child state) requests values) :
    values = requests.map (childValue call domain state) := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, childValue, head, ih]

/-- A live actual replayed edge is the literal renamed synchronous product edge, including its complete guard. -/
theorem edge_renamed_product [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (row : EdgeValue Symbol Guard) (done : edge emptyGuard conjoin (call domain) left right state = .done row state)
    (live : EqualityLeafProjectionPhysical.dead row = false) (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    interpretedEdge holds row = renameEdge (childValue call domain state)
      ⟨left.entry.key.symbol, left.children.zip right.children,
        fun term => holds left.entry.key.constraint term && holds right.entry.key.constraint term⟩ := by
  have fields := edge_live_product emptyGuard conjoin call calls replay domain left right state valid known leftResident rightResident row done live
  have children := replayed_children_map call domain state _ _ fields.2.2.2
  change (⟨row.entry.key.symbol, row.children, holds row.entry.key.constraint⟩ : Language.Edge (Value Symbol Guard) Symbol) =
    ⟨left.entry.key.symbol, (left.children.zip right.children).map (childValue call domain state),
      fun term => holds left.entry.key.constraint term && holds right.entry.key.constraint term⟩
  rw [Language.Edge.mk.injEq]
  refine ⟨fields.2.1, children, ?_⟩
  funext term
  rw [fields.2.2.1, conjoined]

/-- A dead actual equal-arity edge supplies the exact empty-child reason used by normalized product rows. -/
theorem edge_product_rejected [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (sameArity : left.children.length = right.children.length) (row : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (call domain) left right state = .done row state)
    (isDead : EqualityLeafProjectionPhysical.dead row = true) (holds : Guard → Term Symbol → Bool)
    (target : Automaton (Value Symbol Guard) Symbol) (empty : target .empty = []) :
    DropReason target (childValue call domain state)
      ⟨left.entry.key.symbol, left.children.zip right.children,
        fun term => holds left.entry.key.constraint term && holds right.entry.key.constraint term⟩ := by
  obtain ⟨pair, member, returned⟩ := edge_dead_child emptyGuard conjoin call calls replay domain left right state valid known
    leftResident rightResident sameArity row done isDead
  refine Or.inr ⟨pair, member, ?_⟩
  simpa only [childValue, returned] using empty

end MicroCFTA.SourceRecursiveIntersectionKernel
