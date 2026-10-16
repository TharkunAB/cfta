import MicroCFTA.SourceCurrentAllocatedSeededQuery
import MicroCFTA.SourceEqualityProjectionWorker

/-!
# Literal first-seeded checked queries

An operand projects its captured forest. The fold projects the head,
executes the tail, then requests intersection at that tail's checked state.
The first source path is the final seed. Three independent bounds control
projection, stored reads, and native execution. Failed prefixes retain the
complete observation and reached checked state. These workers specify a
completed serial schedule, not the host demand or publication protocol.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededWorker
open InternedConstructorTemplates
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

abbrev Checked := SourceEqualityNativeDemand.State

/-- Incomplete stages retain their entire projection or native observation. -/
inductive Fault (width : Nat) : Type 1 where
  | projection (observation : SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard))
  | native (observation : SourceEqualityNativeDemand.Outcome width (Value Symbol Guard))

/-- Each completed or failed observation retains the complete checked state. -/
inductive Outcome (width : Nat) : Type 1 where
  | done (value : Value Symbol Guard) (state : Checked width)
  | failed (fault : Fault width) (state : Checked width)

def Outcome.state : Outcome width → Checked width
  | .done _ state | .failed _ state => state

/-- Only success enters its continuation, at the exact returned state. -/
def Outcome.bind (first : Outcome width)
    (next : Value Symbol Guard → Checked width → Outcome width) : Outcome width :=
  match first with
  | .done value state => next value state
  | .failed fault state => .failed fault state

/-- A projection retains the native tables and equality operations. -/
def operand [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width) : Outcome width :=
  match SourceEqualityProjectionWorker.forest p h path values before.native.machine.heap with
  | .done value heap => .done value (advancePhysical before ⟨heap, before.operations⟩)
  | .pending key heap => .failed (.projection (.pending key heap))
      (advancePhysical before ⟨heap, before.operations⟩)
  | .unresolved name heap => .failed (.projection (.unresolved name heap))
      (advancePhysical before ⟨heap, before.operations⟩)
  | .exhausted limit heap => .failed (.projection (.exhausted limit heap))
      (advancePhysical before ⟨heap, before.operations⟩)

/-- The checked native request starts at the exact tail return. -/
noncomputable def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width) : Outcome width :=
  match SourceEqualityNativeDemand.execute fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | .done result after => .done result after
  | other => .failed (.native other) other.state

/-- The first seed is projected after every preceding head operand. -/
noncomputable def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h n : Nat) (values : List (Value Symbol Guard)) (seed : List Int) :
    List (List Int) → Checked width → Outcome width
  | [], before => operand p h seed values before
  | path :: paths, before =>
      (operand p h path values before).bind fun head middle =>
        (fold p h n values seed paths middle).bind fun tail later => leaf n head tail later

/-- Empty input does no work. Nonempty input rotates its first path to the seed. -/
noncomputable def seeded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h n : Nat) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked width) : Outcome width :=
  match paths with
  | [] => .done .empty before
  | seed :: rest => fold p h n values seed rest before

end MicroCFTA.SourceCurrentAllocatedSeededWorker
