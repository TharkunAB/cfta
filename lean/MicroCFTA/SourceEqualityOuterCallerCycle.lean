import MicroCFTA.SourceEqualityPartialHeightBoundary
import MicroCFTA.SourceEqualityInheritedPayload
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# A repeated empty-inherited outer caller key

Actual source construction and two local prefixes return the original
ordinary root below a wrapper. Both physical inherited payloads are empty.
The observed key dependency relation has a two-edge cycle. The outer
Haskell memo table and GHC demand behavior remain separate source boundaries.
-/
namespace MicroCFTA.SourceEqualityOuterCallerCycle
open InternedConstructorTemplates InternedNestedConstruction
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "sourceTop" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "equality" => SourceEqualityPartialHeightBoundary.equality
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes

attribute [local cbv_eval] array_small

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- One ordinary unary wrapper has no own equality constraint. -/
def wrap (value : Syntax Symbol Guard) : Syntax Symbol Guard := .node [.mk ("w", .top) sourceTop [value]]

/-- The closed unconstrained binder accepts wrapped binary trees. -/
def plain : Syntax Symbol Guard := .binder true (.node [.mk ("a", .top) sourceTop [],
  .mk ("p", .top) sourceTop [wrap (.var 0),wrap (.var 0)]])

/-- One ordinary binary layer contains the fixed unconstrained binder. -/
def next : Syntax Symbol Guard := .node [.mk ("p", .top) sourceTop [wrap plain,wrap plain]]

/-- A productive binder repeats the root equality below its own wrapper. -/
def constrained : Syntax Symbol Guard := .binder true (.node [.mk ("a", .top) sourceTop [],
  .mk ("p", .top) equality [wrap (.var 0),wrap next]])

/-- Both selected endpoints are closed ordinary wrappers. -/
def expression : Syntax Symbol Guard := .node [.mk ("p", .top) equality [wrap constrained,wrap next]]

/-- Original syntax is closed and every physical annotation is normalized. -/
theorem source_valid : Scoped 0 expression ∧
    SourceEqualityAnnotationConstruction.Allowed SourceEqualityNormalizedEntry.ValidGuard expression := by
  constructor
  · simp [expression, constrained, next, plain, wrap, Scoped, ManyScoped, EdgesScoped]
  · simp only [expression, constrained, next, plain, wrap, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.ManyAllowed, SourceEqualityAnnotationConstruction.EdgesAllowed]
    simp only [SourceEqualityNormalizedEntry.ValidGuard, SourceEqualityConstraintConstructors.top_cached,
      SourceEqualityPartialHeightBoundary.equality_cached, and_self]

/-- The actual outer memo arguments retain the complete inherited physical payload. -/
abbrev Key := SourceEqualityPrecheck.Constraint × InternedBinderProtocol.NodeRef

/-- Two actual local prefixes retain their selected physical child calls. -/
structure Observation where
  original : InternedBinderProtocol.NodeRef
  wrapper : InternedBinderProtocol.NodeRef
  returned : InternedBinderProtocol.NodeRef
  firstInherited : SourceEqualityPrecheck.Constraint
  secondInherited : SourceEqualityPrecheck.Constraint

/-- Follow the first source child through its returned wrapper at the actual warm state. -/
noncomputable def observation : Option Observation :=
  match InternedFreshOrdinaryConstruction.build expression [] empty with
  | .pending .. => none
  | .done root heap => match root with
    | .node _ (edge :: _) _ _ =>
        match SourceEqualityGuardedEdgeWorker.run SourceMemoGate.unconstrained sourceTop SourceEqualityPCSNativeEdge.conjoin
            SourceMemoGate.plain sourceTop 4 4 2 2 2 1024 edge (some []) (SourceEqualityNativeInitial.cold 32 heap) with
        | .done (.ok result) middle =>
            match SourceEqualityPhysicalPayload.own result.entry.key.constraint with
            | .error _ => none
            | .ok own => match SourceEqualityInheritedPayload.combine (some []) own with
              | .error _ => none
              | .ok payload => match result.children with
                | (wrapper@(.node _ [wrapperEdge] _ _)) :: _ =>
                    let firstInherited := SourceEqualityDescend.descend payload 0
                    match SourceEqualityGuardedEdgeWorker.run SourceMemoGate.unconstrained sourceTop SourceEqualityPCSNativeEdge.conjoin
                        SourceMemoGate.plain sourceTop 4 4 2 2 2 1024 wrapperEdge firstInherited middle with
                    | .done (.ok wrapperResult) _ =>
                        match SourceEqualityPhysicalPayload.own wrapperResult.entry.key.constraint with
                        | .error _ => none
                        | .ok wrapperOwn => match SourceEqualityInheritedPayload.combine firstInherited wrapperOwn with
                          | .error _ => none
                          | .ok wrapperPayload => match wrapperResult.children with
                            | [returned] => some ⟨root.referenceOf, wrapper.referenceOf, returned.referenceOf,
                                firstInherited, SourceEqualityDescend.descend wrapperPayload 0⟩
                            | _ => none
                    | _ => none
                | _ => none
        | _ => none
    | _ => none

/-- Test the literal empty physical constructor without a comparison axiom. -/
def emptyPayload : SourceEqualityPrecheck.Constraint → Bool
  | some [] => true
  | _ => false

/-- The physical test identifies exactly EmptyConstraints. -/
theorem emptyPayload_iff (payload : SourceEqualityPrecheck.Constraint) :
    emptyPayload payload = true ↔ payload = some [] := by
  cases payload with
  | none => simp [emptyPayload]
  | some records => cases records <;> simp [emptyPayload]

/-- Check physical root identity and both actual inherited payload constructors. -/
def closes (observed : Observation) : Bool :=
  decide (observed.returned = observed.original) &&
    emptyPayload observed.firstInherited && emptyPayload observed.secondInherited &&
    decide (observed.wrapper ≠ observed.original)

/-- Kernel evaluation follows original construction, the native prefix, and the warm wrapper prefix. -/
theorem actual_cycle : observation.map closes = some true := by cbv

/-- Both source child calls return to the identical empty-inherited physical root key. -/
theorem cycle : ∃ observed, observation = some observed ∧ observed.returned = observed.original ∧
    observed.firstInherited = some [] ∧ observed.secondInherited = some [] ∧ observed.wrapper ≠ observed.original := by
  cases found : observation with
  | none => have impossible := actual_cycle; simp [found] at impossible
  | some observed =>
      have checked : closes observed = true := by simpa only [found, Option.map_some, Option.some.injEq] using actual_cycle
      simp only [closes, Bool.and_eq_true, decide_eq_true_eq, emptyPayload_iff] at checked
      exact ⟨observed, rfl, checked.1.1.1, checked.1.1.2, checked.1.2, checked.2⟩

/-- The observed source prefixes supply both child-to-parent memo-key dependencies. -/
def Dependency (child parent : Key) : Prop :=
  ∃ observed, observation = some observed ∧
    ((child = (observed.firstInherited, observed.wrapper) ∧ parent = (some [], observed.original)) ∨
      (child = (observed.secondInherited, observed.returned) ∧ parent = (observed.firstInherited, observed.wrapper)))

/-- This actual physical caller-key relation is not well founded. -/
theorem not_wellFounded : ¬ WellFounded Dependency := by
  intro wellFounded
  have noCycles : ∀ key, Acc Dependency key → ∀ other, Dependency other key → Dependency key other → False := by
    intro key accessible
    induction accessible with
    | intro key _ ih =>
        intro other forward backward
        exact ih other forward key backward forward
  obtain ⟨observed, found, same, first, second, _⟩ := cycle
  have forward : Dependency (some [], observed.wrapper) (some [], observed.original) :=
    ⟨observed, found, Or.inl ⟨by rw [first], rfl⟩⟩
  have backward : Dependency (some [], observed.original) (some [], observed.wrapper) :=
    ⟨observed, found, Or.inr ⟨by rw [second, same], by rw [first]⟩⟩
  exact noCycles _ (wellFounded.apply _) _ forward backward

end MicroCFTA.SourceEqualityOuterCallerCycle
