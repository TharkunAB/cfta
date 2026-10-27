import MicroCFTA.SourcePruningEnumerationArityOrigins
import MicroCFTA.SourceRecursiveIntersectionMaybeMu
import MicroCFTA.SourceEqualityNativeDemand

/-!
# Arity through actual native constructor primitives

The work condition follows only the actual constructor results.
It imposes no law on an arbitrary native continuation.
Optional binding retains arity at both completed and pending outcomes.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeArityPrimitives
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts
open SourcePruningEnumerationArityOrigins (Fits Heap)
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

section Construction
variable {Symbol : Type}

/-- Each edge request executed by this work has arity at its actual current cache. -/
def WorkFits [DecidableEq (EdgeKey Symbol Constraint)] :
    Work Symbol Constraint A → State Symbol Constraint → Prop
  | .pure _, _ => True
  | .edge key identify next, state =>
      Fits key.constraint key.children.length ∧
        WorkFits (next (edgeStep key identify state).1) (edgeStep key identify state).2
  | .node key identify next, state =>
      WorkFits (next (nodeStep key identify state).1) (nodeStep key identify state).2

/-- An actual edge instruction retains old keys and checks the key it can install. -/
theorem edgeStep_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (key : EdgeKey Symbol Constraint)
    (identify : Interned (EdgeKey Symbol Constraint) → EdgeValue Symbol Constraint)
    (state : State Symbol Constraint) (heap : Heap state)
    (checked : Fits key.constraint key.children.length) :
    Heap (edgeStep key identify state).2 := by
  intro other edge present
  rcases record_cases state.edgeRecords key other
    (identify (Cache.intern state.edges key).1) edge present with old | ⟨same, _⟩
  · exact heap other edge old
  · simpa only [same] using checked

/-- Executed constructor work preserves arity along its actual returned values and caches. -/
theorem work_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (job : Work Symbol Constraint A) (state : State Symbol Constraint)
    (heap : Heap state) (checked : WorkFits job state) :
    Heap (run job state).2 := by
  induction job generalizing state with
  | pure value => exact heap
  | edge key identify next ih =>
      change Fits key.constraint key.children.length ∧
        WorkFits (next (edgeStep key identify state).1) (edgeStep key identify state).2 at checked
      exact ih (edgeStep key identify state).1 (edgeStep key identify state).2
        (edgeStep_heap key identify state heap checked.1) checked.2
  | node key identify next ih =>
      change WorkFits (next (nodeStep key identify state).1) (nodeStep key identify state).2 at checked
      exact ih (nodeStep key identify state).1 (nodeStep key identify state).2 heap checked

/-- A raw edge constructor checks only its supplied guard and actual number of children. -/
theorem makeEdge_fits [DecidableEq (EdgeKey Symbol Constraint)]
    (symbol : Symbol) (constraint : Constraint) (children : List (Value Symbol Constraint))
    (state : State Symbol Constraint) (checked : Fits constraint children.length) :
    WorkFits (makeEdge symbol constraint children) state := by
  simpa only [makeEdge, WorkFits, List.length_map, and_true] using checked

/-- Ordinary node construction emits no edge-key request. -/
theorem makeNode_fits [DecidableEq (EdgeKey Symbol Constraint)]
    (edges : List (EdgeValue Symbol Constraint)) (state : State Symbol Constraint) :
    WorkFits (makeNode edges) state := by
  simp only [makeNode]
  split <;> trivial

/-- Union normalization emits no new edge-key request. -/
theorem makeUnion_fits [DecidableEq (EdgeKey Symbol Constraint)]
    (values : List (Value Symbol Constraint)) (state : State Symbol Constraint) :
    WorkFits (makeUnion values) state := by
  unfold makeUnion
  split <;> first | trivial | (split <;> first | trivial | exact makeNode_fits _ state)

/-- Removing a bare self reference emits no new edge-key request. -/
theorem filter_fits [DecidableEq (EdgeKey Symbol Constraint)]
    (name : InternedBinderProtocol.Reference) (value : Value Symbol Constraint)
    (state : State Symbol Constraint) :
    WorkFits (withoutSelfReference name value) state := by
  cases value <;> simp only [withoutSelfReference] <;> try trivial
  split
  · exact makeUnion_fits _ state
  · trivial

/-- Actual optional binding retains arity at its complete or pending stopping cache. -/
theorem optionalBinder_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (key : Nat × Nat) (body : Value Symbol Constraint) (state : State Symbol Constraint)
    (facts : Facts state) (heap : Heap state) (available : Available state body) :
    Heap (SourceRecursiveIntersectionMaybeMu.maybeMu key body state).state := by
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq key body state state facts available]
  split
  · apply SourcePruningEnumerationArityOrigins.build_heap _ _ state heap
    exact SourcePruningEnumerationArityOrigins.encode_checked body state facts heap available _ _
  · exact heap

end Construction

section Native
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]

/-- One actual native work instruction retains arity before its continuation runs. -/
theorem step_work_heap (job : Work Symbol Constraint A)
    (next : A → SourceRecursiveIntersectionCode.Code Symbol Constraint Output)
    (state : Checked width) (heap : Heap state.native.machine.heap)
    (checked : WorkFits job state.native.machine.heap) :
    Heap (SourceEqualityNativeDemand.step (.code (.work job next)) state).state.native.machine.heap := by
  have retained := work_heap job state.native.machine.heap heap checked
  simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
    SourceEqualityNativeDemand.lift, SourceEqualityNativeDemand.Outcome.state,
    SourceRecursiveIntersectionThunks.advance] using retained

/-- One actual optional-binder instruction retains the exact completed or blocked native heap. -/
theorem step_optionalBinder_heap (key : Nat × Nat) (body : Value Symbol Constraint)
    (next : Value Symbol Constraint → SourceRecursiveIntersectionCode.Code Symbol Constraint Output)
    (state : Checked width) (facts : Facts state.native.machine.heap)
    (heap : Heap state.native.machine.heap) (available : Available state.native.machine.heap body) :
    Heap (SourceEqualityNativeDemand.step (.code (.optionalBinder key body next)) state).state.native.machine.heap := by
  have retained := optionalBinder_heap key body state.native.machine.heap facts heap available
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.native.machine.heap with
  | done value after =>
      simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
        actual, SourceEqualityNativeDemand.lift, SourceEqualityNativeDemand.Outcome.state,
        SourceRecursiveIntersectionThunks.advance, InternedNestedConstruction.Outcome.state] using retained
  | pending pending after =>
      simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
        actual, SourceEqualityNativeDemand.lift, SourceEqualityNativeDemand.Outcome.state,
        SourceRecursiveIntersectionThunks.advance, InternedNestedConstruction.Outcome.state] using retained

end Native
end MicroCFTA.SourcePruningEnumerationNativeArityPrimitives
