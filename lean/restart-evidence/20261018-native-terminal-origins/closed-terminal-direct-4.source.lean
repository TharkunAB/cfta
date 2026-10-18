import MicroCFTA.SourceCurrentNativeQueryRowOrigins

/-!
# Closed operands at the actual root terminal writer

Actual root forwarding uses only swaps and domain resets. These steps
retain both operand closures. A selected terminal row therefore requires
no bare-reference branch. Internal recursive requests remain separate.
-/
namespace MicroCFTA.SourceCurrentNativeQueryClosedTerminal
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentNativeQueryRowOrigins (Route RowOrigin Joined)
open SourceRecursiveIntersectionControl (decision payload)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

private theorem payload_not_reference (left right : Value Symbol Guard)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    payload left right ≠ .leftReference ∧ payload left right ≠ .rightReference := by
  cases left <;> cases right <;> simp_all [Value.free,payload]

private theorem decision_not_reference (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value Symbol Guard) (leftClosed : left.free = []) (rightClosed : right.free = []) :
    decision domain left right ≠ .leftReference ∧ decision domain left right ≠ .rightReference := by
  have safe := payload_not_reference left right leftClosed rightClosed
  unfold decision
  split
  · constructor <;> intro impossible <;> cases impossible
  · split
    · constructor <;> intro impossible <;> cases impossible
    · split
      · constructor <;> intro impossible <;> cases impossible
      · split
        · constructor <;> intro impossible <;> cases impossible
        · cases SourceRecursiveIntersectionControl.identity left with
          | none => constructor <;> intro impossible <;> cases impossible
          | some first =>
              cases SourceRecursiveIntersectionControl.identity right with
              | none => constructor <;> intro impossible <;> cases impossible
              | some second =>
                  by_cases seen : SourceRecursiveIntersectionControl.pair first second ∈ domain.seen
                  · simp only [seen,ite_true]
                    constructor <;> intro impossible <;> cases impossible
                  · simpa only [seen,ite_false] using safe

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The exact swap and reset route retains closure of both ordered terminal operands. -/
theorem route_closed {reader : Checked width} {result : Value Symbol Guard}
    {first last : NodeRequest Symbol Guard} (actual : Route reader result first last) :
    first.left.free = [] → first.right.free = [] → last.left.free = [] ∧ last.right.free = [] := by
  induction actual with
  | refl => intro left right; exact ⟨left,right⟩
  | step one rest ih =>
      intro left right
      obtain ⟨before,after,fuel,_good,_trace,_retained,changed,_forwarded⟩ := one
      rcases changed with ⟨_swap,same⟩ | ⟨_reset,same⟩
      · subst same
        exact ih right left
      · subst same
        exact ih left right

/-- A closed root row origin retains its exact writer and only Mu or union residual branches. -/
theorem closed_residual {reader : Checked width} {request : NodeRequest Symbol Guard}
    {result : Value Symbol Guard} {rowIndex : Nat} {row : EdgeValue Symbol Guard}
    (origin : RowOrigin reader request result rowIndex row)
    (left : request.left.free = []) (right : request.right.free = []) :
    ∃ terminal handle, Route reader result request terminal ∧
      terminal.left.free = [] ∧ terminal.right.free = [] ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle terminal result reader.native ∧
      ((decision terminal.domain.key terminal.left terminal.right = .self ∧
          (nodeEdges terminal.left)[rowIndex]? = some row) ∨
       (decision terminal.domain.key terminal.left terminal.right = .ordinary ∧ Joined reader terminal row) ∨
        (decision terminal.domain.key terminal.left terminal.right = .bothMu ∨
         decision terminal.domain.key terminal.left terminal.right = .leftMu ∨
         decision terminal.domain.key terminal.left terminal.right = .rightMu ∨
         decision terminal.domain.key terminal.left terminal.right = .leftUnion ∨
         decision terminal.domain.key terminal.left terminal.right = .rightUnion)) := by
  obtain ⟨terminal,handle,route,cell,writer,classified⟩ := origin
  have closed := route_closed route left right
  have safe := decision_not_reference terminal.domain.key terminal.left terminal.right closed.1 closed.2
  refine ⟨terminal,handle,route,closed.1,closed.2,cell,writer,?_⟩
  rcases classified with self | ordinary | residual
  · exact .inl self
  · exact .inr (.inl ordinary)
  · rcases residual with both | first | second | firstUnion | secondUnion | firstReference | secondReference
    · exact .inr (.inr (.inl both))
    · exact .inr (.inr (.inr (.inl first)))
    · exact .inr (.inr (.inr (.inr (.inl second))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl firstUnion)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr secondUnion)))))
    · exact False.elim (safe.1 firstReference)
    · exact False.elim (safe.2 secondReference)

end MicroCFTA.SourceCurrentNativeQueryClosedTerminal
