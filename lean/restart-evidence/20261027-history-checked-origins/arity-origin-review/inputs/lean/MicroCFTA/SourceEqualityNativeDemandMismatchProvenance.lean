import MicroCFTA.SourceEqualityNativeDemandMismatch
import MicroCFTA.SourceEqualityNativeDemandMeaning
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.SourceRecursiveIntersectionNativeShape

/-!
# Actual completed mismatch provenance

The mismatch branch constructs a resident sentinel and completes the
original native edge cell. Primitive constructor proofs derive heap
readiness and growth. Independent record meaning proves the exact empty
intersection language. No eager-kernel completed provenance is assumed.
-/
namespace MicroCFTA.SourceEqualityNativeDemandMismatchProvenance
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionNative SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- An actual edge with the sentinel's literal empty child has no independent accepted term. -/
theorem empty_child_rejects (edge : EdgeValue Symbol Guard) (children : edge.children = [.empty])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    ¬ InternedGuardedLanguage.edgeMeaning holds ambient edge term := by
  cases edge with
  | mk entry values =>
      change values = [.empty] at children
      subst values
      rw [InternedGuardedLanguage.edgeMeaning]
      rintro ⟨terms, _, forest, _⟩
      cases terms <;> simp only [InternedGuardedLanguage.forest, InternedGuardedLanguage.meaning, false_and] at forest

/-- Actual sentinel interning retains a ready heap and reads back its complete resident fields. -/
theorem sentinel_provenance [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol)
    (heap : InternedConstructorTemplates.State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready heap) :
    let built := InternedConstructorTemplates.run (makeEdge symbol top [.empty]) heap
    SourceEqualityRequiredCache.Keeps heap built.2 ∧ EdgeResident built.2 built.1 ∧
      built.1.entry.key.symbol = symbol ∧ built.1.entry.key.constraint = top ∧ built.1.children = [.empty] ∧
      ∀ holds ambient term, ¬ InternedGuardedLanguage.edgeMeaning holds ambient built.1 term := by
  have available : InternedNestedProvenance.Values heap ([.empty] : List (Value Symbol Guard)) := by
    intro child member
    have same := List.mem_singleton.mp member
    subst child
    exact empty_available heap
  obtain ⟨keeps, resident, children⟩ := SourceEqualityRequiredCache.edge symbol top [.empty] heap ready available
  have fields := MergedPhysicalGroupEdges.makeEdge_fields heap ready.semantic.1.normal.facts symbol top [.empty] available
  exact ⟨keeps, resident, fields.1, fields.2.1, children,
    fun holds ambient term => empty_child_rejects _ children holds ambient term⟩

/-- Actual started mismatch execution preserves the heap and completes its original returned cell. -/
theorem mismatch_provenance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (started : (demandEdge (lookupEdge width request state.native).1 (lookupEdge width request state.native).2).1 = .evaluate request) :
    ∃ result after, execute 5 (.code (.edge request .pure)) state = .done result after ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap result ∧
      after.native.edges.cells (lookupEdge width request state.native).1 = some ⟨request, .returned result⟩ ∧
      result.entry.key.symbol = request.left.entry.key.symbol ∧ result.entry.key.constraint = top ∧ result.children = [.empty] := by
  let selected := lookupEdge width request state.native
  let current := (demandEdge selected.1 selected.2).2
  let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) current.machine.heap
  have certificate := sentinel_provenance request.left.entry.key.symbol current.machine.heap ready
  refine ⟨built.1, ⟨SourceRecursiveIntersectionThunks.finishEdge selected.1 built.1
    (advance current {current.machine with heap := built.2}), SourceEqualityMkEdgeAllocation.emptyField state.operations⟩,
    mismatch_complete request state mismatch started, certificate.1, certificate.2.1, ?_,
    certificate.2.2.1, certificate.2.2.2.1, certificate.2.2.2.2.1⟩
  have demanded : demandEdge selected.1 selected.2 = (.evaluate request, current) := Prod.ext started rfl
  have running := (demandEdge_evaluate selected.1 selected.2 current request demanded).2
  exact FlatMemoThunk.finish_evaluating selected.1 built.1 current.edges request running

/-- Fresh mismatch publication derives actual completed constructor provenance without a demand-answer premise. -/
theorem mismatch_miss_provenance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (missing : state.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    ∃ result after, execute 5 (.code (.edge request .pure)) state = .done result after ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap result ∧
      after.native.edges.cells (lookupEdge width request state.native).1 = some ⟨request, .returned result⟩ ∧
      result.entry.key.symbol = request.left.entry.key.symbol ∧ result.entry.key.constraint = top ∧ result.children = [.empty] :=
  mismatch_provenance request state ready mismatch (edge_miss_starts request state missing)

/-- The actual completed mismatch result has exactly the independent intersection language of its original operands. -/
theorem mismatch_language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (started : (demandEdge (lookupEdge width request state.native).1 (lookupEdge width request state.native).2).1 = .evaluate request) :
    ∃ result after, execute 5 (.code (.edge request .pure)) state = .done result after ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap result ∧
      after.native.edges.cells (lookupEdge width request state.native).1 = some ⟨request, .returned result⟩ ∧
      ∀ term, InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.left term ∧
          InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.right term := by
  obtain ⟨result, after, done, keeps, resident, returned, _, _, children⟩ := mismatch_provenance request state ready mismatch started
  refine ⟨result, after, done, keeps, resident, returned, ?_⟩
  intro term
  exact ⟨fun accepted => False.elim (empty_child_rejects result children _ ambient term accepted),
    fun common => False.elim (mismatch_disjoint formulas solver ambient request.left request.right leftCached rightCached mismatch term common)⟩

/-- A fresh mismatched source request derives exact completed language and heap provenance directly. -/
theorem mismatch_miss_language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (missing : state.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    ∃ result after, execute 5 (.code (.edge request .pure)) state = .done result after ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap result ∧
      after.native.edges.cells (lookupEdge width request state.native).1 = some ⟨request, .returned result⟩ ∧
      ∀ term, InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.left term ∧
          InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.right term :=
  mismatch_language formulas solver ambient request state ready leftCached rightCached mismatch (edge_miss_starts request state missing)

end MicroCFTA.SourceEqualityNativeDemandMismatchProvenance
