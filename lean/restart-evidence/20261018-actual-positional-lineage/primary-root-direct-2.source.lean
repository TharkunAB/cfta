import MicroCFTA.SourceCurrentActualRequiredRowOrigins
import MicroCFTA.SourceCurrentRequiredExposureSafe
import MicroCFTA.SourceCurrentAllocatedGateWorker

/-!
# Root support from actual false primary selection

A false primary observation certifies each selected original forest value.
The proof uses the literal selected path and existing slot. It needs no
whole-forest annotation. This is a completed-observation theorem. It does
not construct a primary execution or certify later edited values.
-/
namespace MicroCFTA.SourceCurrentPrimaryRootSupport
open InternedConstructorTemplates EqualityNormalize EndpointStatefulGateTrace
open SourceCurrentActualRequiredRowOrigins (Root)
open SourceCurrentRequiredRowOrigins (ExposureSafe)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- A nonempty requirement excludes the unrestricted identity case. -/
theorem exposure {entries : List (Int × SourceEqualityNeeded.Needed)} {value : Node}
    (safe : ExposureSafe (.node entries) value) (nonempty : entries ≠ []) : Root value := by
  cases safe with
  | identity => exact False.elim (nonempty rfl)
  | empty | ordinary => trivial
  | accepted needed value accepted => cases value <;> trivial

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual false primary node observation retains its recursive gate acceptance. -/
theorem node_false {path : Path} {value : Node} {before after : Heap}
    (actual : NodeTrace source reaches path value before false after) : Root value := by
  cases value with
  | empty | node => trivial
  | reference | union => cases actual
  | mu =>
    cases actual with
    | closed accepted closed => exact accepted
    | unfold accepted opened called rest => exact accepted

private theorem false_member {values : List Node} {paths : Class} {before after : Heap}
    (actual : ClassTrace source reaches values paths before false after)
    {path : Path} (member : path ∈ paths) :
    ∃ start finish, PathTrace source reaches values path start false finish := by
  induction paths generalizing before with
  | nil => cases member
  | cons first rest ih =>
    cases actual with
    | next head tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_,_,head⟩
      · exact ih tail member

/-- Every present original slot selected by a false class has supported root shape. -/
theorem class_trace {values : List Node} {paths : Class} {before after : Heap}
    (actual : ClassTrace source reaches values paths before false after)
    {index : Nat} {suffix : Path} (member : index :: suffix ∈ paths)
    {value : Node} (found : values[index]? = some value) : Root value := by
  obtain ⟨start,finish,path⟩ := false_member actual member
  cases path with
  | child child =>
    cases child with
    | missing absent => rw [absent] at found; cases found
    | present selected node =>
      have same := Option.some.inj (selected.symm.trans found)
      cases same
      exact node_false node

/-- A literal false primary worker return supplies support for its selected original value. -/
theorem primary {width fuel : Nat} {values : List Node} {paths : Class}
    {before after : SourceEqualityNativeDemand.State width}
    (actual : SourceCurrentAllocatedGateWorker.primary fuel values paths before = .done false after)
    {index : Nat} {suffix : Path} (member : index :: suffix ∈ paths)
    {value : Node} (found : values[index]? = some value) : Root value :=
  class_trace (SourceCurrentAllocatedGateWorker.primary_graph actual) member found

end MicroCFTA.SourceCurrentPrimaryRootSupport
