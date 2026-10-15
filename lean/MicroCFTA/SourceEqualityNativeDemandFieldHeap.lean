import MicroCFTA.SourceEqualityNativeDemandValidity
import MicroCFTA.SourceEqualityNativeDemandAcceptedLanguage
import MicroCFTA.InternedFreshOrdinaryStoredConstraintHeap

/-!
# Normalized fields in actual checked construction

Resident edge keys supply normalized original fields. Source work retains
this invariant when its new edge annotations are normalized. Actual
optional-binder construction copies annotations from the original available
body, including through nested substitution and both probes.
-/
namespace MicroCFTA.SourceEqualityNativeDemandFieldHeap
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local notation "Cached" => SourceEqualityGuardReadback.Cached

/-- The physical source edge cache contains normalized stored equality fields. -/
def Heap (state : InternedConstructorTemplates.State Symbol Guard) : Prop :=
  InternedFreshOrdinaryConstraintHeap.Heap (fun guard : Guard => Cached guard.equalities) state

/-- Actual edge residency recovers the normalized original field from its physical key. -/
theorem resident_cached (state : InternedConstructorTemplates.State Symbol Guard) (heap : Heap state)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident state edge) : Cached edge.entry.key.constraint.equalities :=
  heap edge.entry.key edge resident

/-- No field premise is needed at the empty original source heap. -/
theorem empty_heap : Heap (@InternedConstructorTemplates.empty Symbol Guard) :=
  InternedFreshOrdinaryConstraintHeap.empty_heap _

/-- New raw work annotations satisfy the same stored equality-field invariant. -/
def WorkFields : Work Symbol Guard X → Prop
  | .pure _ => True
  | .edge key _ next => Cached key.constraint.equalities ∧ ∀ value, WorkFields (next value)
  | .node _ _ next => ∀ value, WorkFields (next value)

/-- Every finite raw work computation retains normalized stored fields. -/
theorem work_heap [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard X)
    (state : InternedConstructorTemplates.State Symbol Guard) (heap : Heap state) (fields : WorkFields job) :
    Heap (run job state).2 := by
  induction job generalizing state with
  | pure value => exact heap
  | edge key identify next ih =>
      apply ih _ _ ?_ (fields.2 _)
      intro other edge present
      rcases InternedRecordCoherence.record_cases state.edgeRecords key other
        (identify (Cache.intern state.edges key).1) edge present with old | ⟨same, _⟩
      · exact heap other edge old
      · exact same ▸ fields.1
  | node key identify next ih => exact ih _ _ heap (fields _)

/-- Normalized input annotations suffice for direct source edge construction. -/
theorem makeEdge_fields (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (cached : Cached guard.equalities) : WorkFields (makeEdge symbol guard values) := ⟨cached, fun _ => trivial⟩

/-- Ordinary node construction adds no edge annotation. -/
theorem makeNode_fields (edges : List (EdgeValue Symbol Guard)) : WorkFields (makeNode edges) := by
  unfold makeNode
  dsimp only
  split <;> first | trivial | (intro value; trivial)

/-- Union flattening, deduplication, and ordinary reconstruction add no edge annotation. -/
theorem makeUnion_fields (values : List (Value Symbol Guard)) : WorkFields (makeUnion values) := by
  unfold makeUnion
  split <;> first | trivial | (split <;> first | exact makeNode_fields _ | (intro value; trivial))

/-- Actual source optional-binder execution retains normalized fields on every outcome. -/
theorem optionalBinder_heap [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (value : Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (heap : Heap state) (available : Available state value) :
    Heap (SourceRecursiveIntersectionMaybeMu.maybeMu pair value state).state := by
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair value state state facts available]
  split
  · apply InternedFreshOrdinaryConstraintHeap.build_heap _ _ _ state heap
    exact InternedFreshOrdinaryStoredConstraintHeap.encode_valid _ value state facts heap available _ _
  · exact heap

/-- Current original edge residency derives the fields required by the actual checked body. -/
theorem body_fields (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : CheckedState width) (heap : Heap state.native.machine.heap) (ready : EdgeReady state.native.machine request) :
    SourceEqualityNativeDemandOperations.Fields (.edgeBody request next) :=
  ⟨resident_cached _ heap request.left ready.2.1, resident_cached _ heap request.right ready.2.2⟩

/-- Actual successful prefix execution derives the normalized new annotation. -/
theorem ready_cached (request : EdgeRequest Symbol Guard) (state : CheckedState width)
    (heap : Heap state.native.machine.heap) (ready : EdgeReady state.native.machine request)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (first second combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (arity : request.left.children.length = request.right.children.length)
    (firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (checked : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined)) :
    Cached (SourceEqualityConjoinAllocation.readback combined).equalities := by
  have fields := SourceEqualityNativeDemandAcceptedLanguage.ready_readback request state first second combined valid
    (resident_cached _ heap request.left ready.2.1) (resident_cached _ heap request.right ready.2.2)
    arity firstLoaded secondLoaded checked
  rw [fields]
  exact SourceEqualityConstraintConstructors.conjoin_cached _ _ _

end MicroCFTA.SourceEqualityNativeDemandFieldHeap
