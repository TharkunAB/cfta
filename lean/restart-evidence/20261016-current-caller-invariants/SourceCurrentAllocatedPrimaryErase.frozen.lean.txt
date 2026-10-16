import MicroCFTA.SourceCurrentAllocatedPrimaryReads

/-!
# Erase exact source primary reads to historical operational receipts

Erasure retains each actual call equation and both memo endpoints. It
forgets only the exact source operand annotation at a closed endpoint.
-/
namespace MicroCFTA.SourceCurrentAllocatedPrimaryReads
open Cache InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open EndpointMemoGateTrace (Memos)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Exact node reads retain their historical operational equations. -/
theorem node_erase
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    {actual : EndpointStatefulGateTrace.NodeTrace source reaches path value before answer after} {memos final : Memos}
    (reads : NodeReads actual memos final) : EndpointMemoGateTrace.NodeReads actual memos final := by
  induction reads using NodeReads.rec
      (motive_2 := fun {_values _index _path _before _answer _after} trace memos saved _ =>
        EndpointMemoGateTrace.ChildReads trace memos saved)
      (motive_3 := fun {_index _path _edges _before _answer _after} trace memos saved _ =>
        EndpointMemoGateTrace.EdgesReads trace memos saved) with
  | empty => exact .empty
  | reference => exact .reference
  | union members => exact .union members
  | finite fast => exact .finite fast
  | endpoint_open slow opened => exact .endpoint_open slow opened
  | endpoint_closed slow closed actual => exact .endpoint_closed slow closed actual
  | branches slow trace ih => exact .branches slow ih
  | constrained blocked actual => exact .constrained blocked actual
  | closed plain closed actual => exact .closed plain closed actual
  | unfold plain opened actual predicate unfolding trace ih => exact .unfold plain opened actual predicate unfolding ih
  | missing absent => exact .missing absent
  | present found trace ih => exact .present found ih
  | nil => exact .nil
  | stop head ih => exact .stop ih
  | next head tail headIH tailIH => exact .next headIH tailIH

/-- Exact selected-child reads retain the same physical choice. -/
theorem child_erase
    {values : List (Value Symbol Guard)} {index : Nat} {path : Path}
    {before after : State Symbol Guard} {answer : Bool}
    {actual : EndpointStatefulGateTrace.ChildTrace source reaches values index path before answer after}
    {memos final : Memos} (reads : ChildReads actual memos final) : EndpointMemoGateTrace.ChildReads actual memos final := by
  cases reads with
  | missing absent => exact .missing absent
  | present found called => exact .present found (node_erase called)

/-- Exact row reads retain the actual visited prefix and returned tables. -/
theorem edges_erase
    {index : Nat} {path : Path} {edges : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {answer : Bool}
    {actual : EndpointStatefulGateTrace.EdgesTrace source reaches index path edges before answer after}
    {memos final : Memos} (reads : EdgesReads actual memos final) : EndpointMemoGateTrace.EdgesReads actual memos final := by
  induction reads using EdgesReads.rec
      (motive_1 := fun {_path _value _before _answer _after} _ _ _ _ => True)
      (motive_2 := fun {_values _index _path _before _answer _after} _ _ _ _ => True) with
  | empty | reference | union | finite | endpoint_open | endpoint_closed | branches | constrained | closed | unfold | missing | present => trivial
  | nil => exact .nil
  | stop head _ => exact .stop (child_erase head)
  | next head tail _ ih => exact .next (child_erase head) ih

/-- Exact path reads retain the literal selected path. -/
theorem path_erase
    {values : List (Value Symbol Guard)} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    {actual : EndpointStatefulGateTrace.PathTrace source reaches values path before answer after}
    {memos final : Memos} (reads : PathReads actual memos final) : EndpointMemoGateTrace.PathReads actual memos final := by
  cases reads with
  | empty => exact .empty
  | child called => exact .child (child_erase called)

/-- Exact class reads retain source path order and short-circuiting. -/
theorem class_erase
    {values : List (Value Symbol Guard)} {paths : Class} {before after : State Symbol Guard} {answer : Bool}
    {actual : EndpointStatefulGateTrace.ClassTrace source reaches values paths before answer after}
    {memos final : Memos} (reads : ClassReads actual memos final) : EndpointMemoGateTrace.ClassReads actual memos final := by
  induction reads with
  | nil => exact .nil
  | stop first => exact .stop (path_erase first)
  | next first rest ih => exact .next (path_erase first) ih

end MicroCFTA.SourceCurrentAllocatedPrimaryReads
