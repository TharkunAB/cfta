import MicroCFTA.SourceRecursiveIntersectionProductRowView
import MicroCFTA.RelatedRows

/-!
# Related rows from actual ordinary intersection execution

The child relation is the actual completed call in the parent's current
domain and final cache. Ordered child traces derive this relation. They
do not use a default result or assume any child-language equivalence.
Deleted rows retain actual related children and an empty-child witness.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourcePreparedSharedRows (interpretedEdge)
open EqualityLeafProjectionPhysical (dead)

/-- An actual equal-arity edge has related children from its exact final-cache calls. -/
theorem edge_related_product [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (sameArity : left.children.length = right.children.length) (row : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (call domain) left right state = .done row state)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    RelatedRows.Match (fun pair child => call domain pair.1 pair.2 state = .done child state)
      ⟨left.entry.key.symbol, left.children.zip right.children,
        fun term => holds left.entry.key.constraint term && holds right.entry.key.constraint term⟩ (interpretedEdge holds row) := by
  have fields := edge_children_replay emptyGuard conjoin call calls replay domain left right state valid known
    leftResident rightResident sameArity row done
  refine ⟨fields.1.symm, ?_, fields.2.2⟩
  funext term
  change (holds left.entry.key.constraint term && holds right.entry.key.constraint term) = holds row.entry.key.constraint term
  rw [fields.2.1, conjoined]

/-- Actual ordinary parent rows supply local related-row soundness and complete retained/deleted source rows. -/
theorem node_related_product_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : node emptyGuard conjoin (call domain) left right state = .done value final)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (target : Automaton (Value Symbol Guard) Symbol) (empty : target .empty = []) :
    let related := fun pair child => call domain pair.1 pair.2 final = .done child final
    let originals := Language.intersect (fun (_ : Value Symbol Guard) => left.map (interpretedEdge holds))
      (fun (_ : Value Symbol Guard) => right.map (interpretedEdge holds)) (.empty, .empty)
    (∀ edge ∈ (nodeEdges value).map (interpretedEdge holds), ∃ original ∈ originals, RelatedRows.Match related original edge) ∧
      (∀ original ∈ originals,
        (∃ children, All₂ related original.children children ∧ ∃ child ∈ children, target child = []) ∨
        ∃ edge ∈ (nodeEdges value).map (interpretedEdge holds), RelatedRows.Match related original edge) := by
  dsimp only
  have checked := node_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  have finalValid : Valid final := by simpa only [done, Result.state] using checked.valid
  have growth : Extension state final := by simpa only [done, Result.state] using checked.extension
  have finalKnown := known.grows domain growth
  have leftFinal := fun edge member => edge_grows _ _ growth.heap edge (leftResident edge member)
  have rightFinal := fun edge member => edge_grows _ _ growth.heap edge (rightResident edge member)
  constructor
  · intro edge member
    obtain ⟨physical, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨first, firstIn, second, secondIn, symbol, returned, live⟩ :=
      (node_members_replay emptyGuard conjoin call calls replay domain left right state valid known leftResident rightResident value final done physical).mp selected
    have arity := (edge_live_product emptyGuard conjoin call calls replay domain first second final finalValid finalKnown
      (leftFinal first firstIn) (rightFinal second secondIn) physical returned live).1
    exact ⟨_, (physical_product_member holds left right _).mpr ⟨first, firstIn, second, secondIn, symbol, arity, rfl⟩,
      edge_related_product emptyGuard conjoin call calls replay domain first second final finalValid finalKnown
        (leftFinal first firstIn) (rightFinal second secondIn) arity physical returned holds conjoined⟩
  · intro original member
    obtain ⟨first, firstIn, second, secondIn, symbol, arity, rfl⟩ := (physical_product_member holds left right original).mp member
    obtain ⟨rows, _, paired, _⟩ := node_rows_replay emptyGuard conjoin call calls replay domain left right state valid known
      leftResident rightResident value final done
    obtain ⟨physical, _, returned⟩ := SymbolicSmartRows.all₂_child _ _ _ paired (first, second)
      ((pairs_member left right (first, second)).mpr ⟨firstIn, secondIn, symbol⟩)
    have matched := edge_related_product emptyGuard conjoin call calls replay domain first second final finalValid finalKnown
      (leftFinal first firstIn) (rightFinal second secondIn) arity physical returned holds conjoined
    cases deadRow : dead physical with
    | false =>
        exact Or.inr ⟨interpretedEdge holds physical,
          List.mem_map.mpr ⟨physical,
            (node_members_replay emptyGuard conjoin call calls replay domain left right state valid known leftResident rightResident value final done physical).mpr
              ⟨first, firstIn, second, secondIn, symbol, returned, deadRow⟩, rfl⟩, matched⟩
    | true =>
        obtain ⟨child, present, emptyRef⟩ := List.any_eq_true.mp deadRow
        have same : child = .empty := (EqualityLeafProjectionPhysical.reference_empty child).mp (by simpa only [beq_iff_eq] using emptyRef)
        exact Or.inl ⟨physical.children, matched.2.2, child, present, same ▸ empty⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
