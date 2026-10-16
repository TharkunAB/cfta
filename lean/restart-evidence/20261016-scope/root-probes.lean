import MicroCFTA.SourceCurrentAllocatedNativeScopedMuCertificates
import MicroCFTA.SourceCurrentAllocatedNativeScopedNodeCertificates
import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact
open MicroCFTA
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
open SourceCurrentAllocatedNativeScopedMuCertificates
open SourceCurrentAllocatedNativeColdClosedExact
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

#print axioms optional_scope
#print axioms mu_certified
#print axioms left_reference
#print axioms right_reference
#print axioms SourceCurrentAllocatedNativeScopedNodeCertificates.node_certified
#print axioms completed_unique
#print axioms cold_complete
#check @optional_scope
#check @mu_certified
#check @left_reference
#check @right_reference
#check @SourceCurrentAllocatedNativeScopedNodeCertificates.node_certified
#check @completed_unique
#check @cold_complete

example [DecidableEq (EdgeKey Symbol Guard)] (state : Machine Symbol Guard)
    (semantic : SemanticReady state.heap) (pairs : List (Nat × Nat)) (pair : Nat × Nat) :
    SourceRecursiveIntersectionResultScope.Scope pairs (.empty : Value Symbol Guard) :=
  optional_scope pairs pair .empty .empty state state semantic (empty_available _)
    (SourceRecursiveIntersectionResultScope.closed _ _ rfl) rfl

example [DecidableEq (EdgeKey Symbol Guard)] (state : Machine Symbol Guard) :
    SourceCurrentAllocatedNativeScopedCode.Certified
      (compileReference IntersectionEmptyDomain.emptyDomain 0 (.empty : Value Symbol Guard) true)
      state (fun _ value => SourceRecursiveIntersectionResultScope.Scope [] value) :=
  left_reference IntersectionEmptyDomain.emptyDomain 0 .empty state

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (ready : NodeReady state request) :
    SourceCurrentAllocatedNativeScopedCode.Certified (compileNode request) state
      (fun _ value => SourceRecursiveIntersectionResultScope.Scope request.domain.key.seen value) :=
  SourceCurrentAllocatedNativeScopedNodeCertificates.node_certified request state valid semantic ready

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (firstFuel secondFuel : Nat) (control : Control A) (before firstAfter secondAfter : Checked width)
    (firstValue secondValue : A)
    (first : execute firstFuel control before = .done firstValue firstAfter)
    (second : execute secondFuel control before = .done secondValue secondAfter) :
    firstAfter.operations = secondAfter.operations :=
  congrArg SourceEqualityNativeDemand.State.operations
    (completed_unique firstFuel secondFuel control before firstAfter secondAfter firstValue secondValue first second).2

theorem cold_closed_exact_kernel [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : Good (⟨initial width machine, operations⟩ : Checked width)) (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (⟨initial width machine, operations⟩ : Checked width)) :
    ∃ fuel value after,
      execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        ⟨initial width machine, operations⟩ = .done value after ∧
      value.free = [] ∧ Good after ∧ SemanticReady after.native.machine.heap ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      Available after.native.machine.heap value ∧
      (∀ extra, execute (fuel + 1 + extra) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        ⟨initial width machine, operations⟩ = .done value after) ∧
      ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  obtain ⟨model, ranked, fuel, value, after, receipt, scopeCache, _, closed, meaning⟩ :=
    cold_complete formulas solver machine operations valid semantic left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨fuel, value, after, receipt.done, closed, receipt.good, receipt.semantic, scopeCache, receipt.result,
    (fun extra => done_stable (fuel + 1) extra _ _ _ _ receipt.done), meaning⟩

#print axioms cold_closed_exact_kernel
