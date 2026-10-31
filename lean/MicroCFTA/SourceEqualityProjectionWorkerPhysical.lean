import MicroCFTA.SourceEqualityProjectionWorker
import MicroCFTA.MergedFreshOrdinaryColdEffects
import MicroCFTA.SourcePruningEnumerationNodes

/-! Physical lookup retention for actual projection reader operations. -/
set_option autoImplicit false

namespace MicroCFTA.SourceEqualityProjectionWorkerPhysical
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceEqualityRequiredWorker (Result work)
open SourcePruningEnumerationNodes (lookupNode)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Cold" => MergedFreshOrdinaryColdEffects.Verified
variable {Guard A : Type}

/-- Return the physical heap of each actual worker outcome. -/
def reached : Result Symbol Guard A → State Symbol Guard
  | .done _ after | .pending _ after | .unresolved _ after | .exhausted _ after => after

/-- Keep the reader payload and physical heap. The exposure type has no limit tag. -/
def exposure : Result Symbol Guard (List (EdgeValue Symbol Guard)) → MergedSourceExposure.Result Symbol Guard
  | .done edges after => .done edges after
  | .pending key after => .pending key after
  | .unresolved name after => .unresolved name after
  | .exhausted _ after => .exhausted after

private theorem exposure_append (earlier : List (EdgeValue Symbol Guard))
    (actual : Result Symbol Guard (List (EdgeValue Symbol Guard))) :
    exposure (actual.bind fun more after => .done (earlier ++ more) after) =
      (exposure actual).prepend earlier := by
  cases actual <;> rfl

private theorem exposure_state (actual : Result Symbol Guard (List (EdgeValue Symbol Guard))) :
    (exposure actual).state = reached actual := by
  cases actual <;> rfl

/-- The literal reader retains cold effects at every outcome and every read fuel. -/
theorem readAll_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Values before values) (closed : ClosedValues values) :
    Cold before (exposure (SourceEqualityProjectionWorker.readAll fuel values before)) := by
  induction values generalizing before with
  | nil =>
      exact MergedFreshOrdinaryColdEffects.done_verified before semantic covered []
        (by simp [Edges]) (by simp [ClosedEdges])
  | cons value values ih =>
      have first := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value before semantic covered
        (available value List.mem_cons_self) (closed value List.mem_cons_self)
      cases observed : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
      | done edges middle =>
          have current : Cold before (.done edges middle) := by
            simpa only [observed] using MergedFreshOrdinaryColdEffects.nodeEdges_verified
              fuel value before semantic covered (available value List.mem_cons_self) (closed value List.mem_cons_self)
          have rest := ih middle current.semantic current.covered
            (fun child member => (available child (List.mem_cons_of_mem _ member)).grows
              before middle current.growth current.history)
            (fun child member => closed child (List.mem_cons_of_mem _ member))
          have combined := (rest.prepend edges (current.edges _ _ rfl) (current.closed _ _ rfl)).extend
            current.growth current.history
          simpa only [SourceEqualityProjectionWorker.readAll, observed, exposure_append] using combined
      | pending key after =>
          simpa only [SourceEqualityProjectionWorker.readAll, observed, exposure] using first
      | unresolved name after =>
          simpa only [SourceEqualityProjectionWorker.readAll, observed, exposure] using first
      | exhausted after =>
          simpa only [SourceEqualityProjectionWorker.readAll, observed, exposure] using first

private theorem lookup_growth (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (handle : Nat) (value : Value Symbol Guard) (present : lookupNode before handle = some value) :
    lookupNode after handle = some value := by
  cases handle with
  | zero => exact present
  | succ identity =>
      cases issued : before.nodes.issued identity with
      | none => simp only [lookupNode, issued] at present; cases present
      | some key =>
          cases canonical : before.nodes.table key with
          | none => simp only [lookupNode, issued, canonical] at present; cases present
          | some entry =>
              by_cases winner : entry.identity = identity
              · simp only [lookupNode, issued, canonical, ite_eq_left winner] at present
                simpa only [lookupNode, history identity key issued,
                  growth.nodes key entry canonical, ite_eq_left winner] using
                  growth.nodeRecords key value present
              · simp only [lookupNode, issued, canonical, ite_eq_right winner] at present
                cases present

/-- Each old physical handle keeps its exact payload after the actual reader. -/
theorem readAll_lookup [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Values before values) (closed : ClosedValues values)
    (handle : Nat) (value : Value Symbol Guard) (present : lookupNode before handle = some value) :
    lookupNode (reached (SourceEqualityProjectionWorker.readAll fuel values before)) handle = some value := by
  have verified := readAll_verified fuel values before semantic covered available closed
  exact lookup_growth before _
    (by simpa only [exposure_state] using verified.growth)
    (by simpa only [exposure_state] using verified.history) handle value present

private theorem rebuild_lookup [DecidableEq (EdgeKey Symbol Guard)]
    (before : State Symbol Guard) (actual : MergedSourceExposure.Result Symbol Guard)
    (verified : Cold before actual) (handle : Nat) (value : Value Symbol Guard)
    (present : lookupNode before handle = some value) :
    lookupNode (reached (match actual with
      | .done edges after => work (makeNode edges) after
      | .pending key after => .pending key after
      | .unresolved name after => .unresolved name after
      | .exhausted after => .exhausted .head after)) handle = some value := by
  cases actual with
  | done edges after =>
      have made := InternedNestedFacts.node_verified edges after verified.semantic.1.normal.facts
        (verified.edges _ _ rfl)
      simpa only [work, reached, InternedNestedConstruction.work, InternedNestedConstruction.Outcome.state] using lookup_growth before _
        (grows_trans verified.growth made.growth) (extends_trans verified.history made.history)
        handle value present
  | pending key after | unresolved name after | exhausted after =>
      exact lookup_growth before _ verified.growth verified.history handle value present

/-- Node reconstruction retains old handles after every actual projection-union outcome. -/
theorem union_lookup [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Values before values) (closed : ClosedValues values)
    (handle : Nat) (value : Value Symbol Guard) (present : lookupNode before handle = some value) :
    lookupNode (reached (SourceEqualityProjectionWorker.union fuel values before)) handle = some value := by
  have kept := rebuild_lookup before (exposure (SourceEqualityProjectionWorker.readAll fuel values before))
    (readAll_verified fuel values before semantic covered available closed) handle value present
  cases observed : SourceEqualityProjectionWorker.readAll fuel values before <;>
    simpa only [SourceEqualityProjectionWorker.union, observed, Result.bind, exposure, reached] using kept

/-- The actual head reader retains old handles even when the read fuel is exhausted. -/
theorem head_lookup [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (query : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before query) (closed : query.free = [])
    (handle : Nat) (value : Value Symbol Guard) (present : lookupNode before handle = some value) :
    lookupNode (reached (SourceEqualityRequiredWorker.head fuel query before)) handle = some value := by
  have kept := rebuild_lookup before (MergedFreshOrdinaryExposure.nodeEdges fuel query before)
    (MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel query before semantic covered available closed)
    handle value present
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel query before <;>
    simpa only [SourceEqualityRequiredWorker.head, actual, reached, work] using kept

end MicroCFTA.SourceEqualityProjectionWorkerPhysical
