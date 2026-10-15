import MicroCFTA.SourceEqualityConstraintGuardInventory
import MicroCFTA.SourceEqualityConstraintPathInventory
import MicroCFTA.SourceEqualityPartialConstraintOrigins

/-!
# A finite original inventory of complete recursive source constraints

An explicit finite product contains every derived physical equality field
and guard field. Original normalized syntax supplies the literal checks.
Actual checked recursive success therefore retains only constraints in this
fixed inventory. This bounds annotations, not constructed node identities
or the length of a recursive caller execution.
-/
namespace MicroCFTA.SourceEqualityConstraintInventory
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityNativeInitial
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialGraphRuns SourceEqualityPartialMemoGraph
open SourceEqualityAnnotationConstruction SourceEqualityConstraintOrigins
open SourceEqualityAnnotationHeap (Heap)
open SourceEqualityAnnotationLanguage (Annotated)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "sourceTop" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

mutual
/-- Original syntax checks every literal in its complete stored guard inventory. -/
theorem literal_checks {S G : Type} (annotation : G → Prop) (expression : Syntax S G)
    (allowed : Allowed annotation expression) : ∀ guard ∈ guards expression, annotation guard := by
  cases expression with
  | empty | var => simp [guards]
  | node edges =>
      simp only [Allowed] at allowed
      exact edge_checks annotation edges allowed
  | union members =>
      simp only [Allowed] at allowed
      exact child_checks annotation members allowed
  | binder smart body =>
      simp only [Allowed] at allowed
      exact literal_checks annotation body allowed
termination_by sizeOf expression

/-- Each original child inventory retains its own annotation checks. -/
theorem child_checks {S G : Type} (annotation : G → Prop) (expressions : List (Syntax S G))
    (allowed : ManyAllowed annotation expressions) : ∀ guard ∈ childGuards expressions, annotation guard := by
  cases expressions with
  | nil => simp [childGuards]
  | cons first rest =>
      simp only [ManyAllowed] at allowed
      intro guard member
      rcases List.mem_append.mp member with member | member
      · exact literal_checks annotation first allowed.1 guard member
      · exact child_checks annotation rest allowed.2 guard member
termination_by sizeOf expressions

/-- Each original row checks its complete literal guard and all child and tail literals. -/
theorem edge_checks {S G : Type} (annotation : G → Prop) (expressions : List (EdgeSyntax S G))
    (allowed : EdgesAllowed annotation expressions) : ∀ guard ∈ edgeGuards expressions, annotation guard := by
  cases expressions with
  | nil => simp [edgeGuards]
  | cons first rest =>
      cases first with
      | mk symbol own children =>
          simp only [EdgesAllowed] at allowed
          intro guard member
          rcases List.mem_cons.mp member with same | member
          · exact same ▸ allowed.1
          · rcases List.mem_append.mp member with member | member
            · exact child_checks annotation children allowed.2.1 guard member
            · exact edge_checks annotation rest allowed.2.2 guard member
termination_by sizeOf expressions
end

/-- Enumerate the finite product of complete physical equality fields and original guard fields. -/
def inventory (literals : List Constraint) : List Constraint :=
  (SourceEqualityConstraintPathInventory.inventory literals).flatMap (fun equalities =>
    (SourceEqualityConstraintGuardInventory.inventory literals).map (fun guard => ⟨equalities, guard⟩))

/-- Every derived complete source constraint is in the fixed original finite product. -/
theorem derived_mem_inventory (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (constraint : Constraint) (derived : Derived literals sourceTop conjoin constraint) : constraint ∈ inventory literals := by
  apply List.mem_flatMap.mpr
  refine ⟨constraint.equalities, SourceEqualityConstraintPathInventory.derived_mem_inventory literals normalized constraint derived, ?_⟩
  apply List.mem_map.mpr
  refine ⟨constraint.guard, SourceEqualityConstraintGuardInventory.derived_mem_inventory literals constraint derived, ?_⟩
  cases constraint
  rfl

/-- The actual own-payload accessor also has a fixed finite image of the original complete inventory. -/
theorem own_mem_inventory (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (constraint : Constraint) (derived : Derived literals sourceTop conjoin constraint) :
    SourceEqualityPhysicalPayload.own constraint ∈ (inventory literals).map SourceEqualityPhysicalPayload.own :=
  List.mem_map.mpr ⟨constraint, derived_mem_inventory literals normalized constraint derived, rfl⟩

/-- Literal origins in an actual physical heap imply membership in the explicit finite constraint inventory. -/
theorem heap (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (state : State Symbol Constraint) (origins : Heap (Derived literals sourceTop conjoin) state) :
    Heap (fun constraint => constraint ∈ inventory literals) state :=
  fun key edge present => derived_mem_inventory literals normalized key.constraint (origins key edge present)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]

/-- Original normalized syntax supplies a fixed finite constraint inventory for every checked successful public execution. -/
theorem closed (width : Nat) (expression : Syntax Symbol Constraint)
    (normalized : Allowed SourceEqualityNormalizedEntry.ValidGuard expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value state, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      Scope (cold width state) ∧ Heap (fun constraint => constraint ∈ inventory (guards expression)) state ∧
      Available state value ∧ value.free = [] ∧
      ∀ g e p h c n fuel result after,
        SourceEqualityPartialChecks.Checked g e p h c n fuel (some []) value (cold width state) →
        SourceEqualityPartialWorker.run g e p h c n fuel (some []) value (cold width state) = .done (.ok result) after →
        ∃ trace : ReduceNode (some []) value (cold width state) result after,
          Heap (fun constraint => constraint ∈ inventory (guards expression)) after.machine.heap ∧
          Annotated (fun constraint => constraint ∈ inventory (guards expression)) result ∧ NodeReads trace ∧ Scope after ∧
          SourceEqualityRequiredCache.Keeps state after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
          NodeRun (some []) value (cold width state) result after ∧
          ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  have literals := literal_checks SourceEqualityNormalizedEntry.ValidGuard expression normalized
  obtain ⟨value, state, built, scope, origins, available, valueClosed, every⟩ :=
    SourceEqualityPartialConstraintOrigins.closed width expression normalized formulas solver ambient
  refine ⟨value, state, built, scope, heap _ literals state origins, available, valueClosed, ?_⟩
  intro g e p h c n fuel result after plan done
  obtain ⟨trace, finalOrigins, _, reads, finalScope, keeps, finalAvailable, resultClosed, replay, exactLanguage⟩ :=
    every g e p h c n fuel result after plan done
  have finalHeap := heap _ literals after.machine.heap finalOrigins
  exact ⟨trace, finalHeap, SourceEqualityAnnotationHeap.available _ _ finalHeap
    finalScope.native.semantic.ready.semantic.1.normal.facts.linked result finalAvailable,
    reads, finalScope, keeps, finalAvailable, resultClosed, replay, exactLanguage⟩

end MicroCFTA.SourceEqualityConstraintInventory
