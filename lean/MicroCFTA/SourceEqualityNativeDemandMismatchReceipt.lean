import MicroCFTA.SourceEqualityNativeDemandMismatchProvenance
import MicroCFTA.SourceEqualityNativeDemandCellValidity

/-!
# Checked body receipts for mismatched edges

Standalone checked mismatch bodies complete with the actual sentinel heap.
Their independent empty intersection law holds for every guard evaluator.
Ready original inputs and primitive constructor proofs derive the new
checked receipt. No older eager-kernel result predicate is required.
-/
namespace MicroCFTA.SourceEqualityNativeDemandMismatchReceipt
open Language Cache InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- Unequal original arities have no common independent accepted term for any guard evaluator. -/
theorem mismatch_disjoint (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (left right : EdgeValue Symbol Guard) (mismatch : left.children.length ≠ right.children.length) (term : Term Symbol) :
    ¬ (InternedGuardedLanguage.edgeMeaning holds ambient left term ∧ InternedGuardedLanguage.edgeMeaning holds ambient right term) := by
  rintro ⟨first, second⟩
  obtain ⟨firstTerms, firstShape, firstForest, _⟩ := (InternedGuardedLanguage.edgeMeaning_all holds ambient left term).mp first
  obtain ⟨secondTerms, secondShape, secondForest, _⟩ := (InternedGuardedLanguage.edgeMeaning_all holds ambient right term).mp second
  have sameTerms := (Term.node.inj (firstShape.symm.trans secondShape)).2
  exact mismatch (firstForest.length_eq.trans ((congrArg List.length sameTerms).trans secondForest.length_eq.symm))

/-- A checked standalone mismatch body completes through the actual sentinel constructor in three instructions. -/
theorem mismatch_body_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap
    execute 3 (.edgeBody request .pure) state = .done built.1
      ⟨advance state.native {state.native.machine with heap := built.2}, SourceEqualityMkEdgeAllocation.emptyField state.operations⟩ := by
  simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, body_mismatch request _ _ mismatch]
  rfl

/-- The actual standalone mismatch execution derives checked provenance at its returned physical machine. -/
theorem mismatch_body_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (inputs : EdgeReady state.native.machine request)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap
    EdgeProduced (width := width) holds {state.native.machine with heap := built.2} request built.1 := by
  let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap
  have certificate := SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance request.left.entry.key.symbol state.native.machine.heap heapReady
  refine ⟨state, ⟨advance state.native {state.native.machine with heap := built.2},
    SourceEqualityMkEdgeAllocation.emptyField state.operations⟩, 3, inputs,
    mismatch_body_complete request state mismatch,
    ⟨certificate.1.growth, certificate.1.history, Cache.extends_refl _⟩,
    certificate.2.1, Extension.refl _, ?_⟩
  intro _ _ _ ambient term
  exact ⟨fun accepted => False.elim (certificate.2.2.2.2.2 holds ambient term accepted),
    fun common => False.elim (mismatch_disjoint holds ambient request.left request.right mismatch term common)⟩

/-- Later actual machine growth retains the same completed mismatch body receipt and language law. -/
theorem mismatch_body_produced_grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (inputs : EdgeReady state.native.machine request)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (machine : Machine Symbol Guard)
    (later : Extension {state.native.machine with heap :=
      (InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap).2} machine) :
    EdgeProduced (width := width) holds machine request
      (InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap).1 :=
  (mismatch_body_produced holds request state heapReady inputs mismatch).grows later

/-- Actual native mismatch completion installs its checked receipt and retains validity of both memo families. -/
theorem mismatch_native_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (inputs : EdgeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (started : (demandEdge (lookupEdge width request state.native).1 (lookupEdge width request state.native).2).1 = .evaluate request) :
    ∃ result after, execute 5 (.code (.edge request .pure)) state = .done result after ∧
      SourceEqualityNativeDemandProvenance.Valid holds after.native ∧
      EdgeProduced (width := width) holds after.native.machine request result ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap result ∧
      after.native.edges.cells (lookupEdge width request state.native).1 = some ⟨request, .returned result⟩ := by
  let selected := lookupEdge width request state.native
  let current := (demandEdge selected.1 selected.2).2
  let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) current.machine.heap
  have selectedValid := SourceEqualityNativeDemandProvenance.lookupEdge_valid state.native valid request inputs safe
  have currentValid := SourceEqualityNativeDemandProvenance.demandEdge_valid selected.2 selectedValid selected.1
  have demanded : demandEdge selected.1 selected.2 = (.evaluate request, current) := Prod.ext started rfl
  have running := (SourceRecursiveIntersectionNative.demandEdge_evaluate selected.1 selected.2 current request demanded).2
  have certificate := SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance request.left.entry.key.symbol current.machine.heap heapReady
  have growth : Extension current.machine {current.machine with heap := built.2} :=
    ⟨certificate.1.growth, certificate.1.history, Cache.extends_refl _⟩
  have machineValid : SourceRecursiveIntersectionKernel.Valid {current.machine with heap := built.2} :=
    ⟨certificate.1.ready.semantic.1.normal.facts, currentValid.machine.2⟩
  have advancedValid := SourceEqualityNativeDemandProvenance.advance_valid current currentValid _ machineValid growth
  have produced := mismatch_body_produced holds request (⟨current, state.operations⟩ : SourceEqualityNativeDemand.State width) heapReady inputs mismatch
  have completed := SourceEqualityNativeDemandProvenance.finishEdge_valid
    (advance current {current.machine with heap := built.2}) advancedValid selected.1 request built.1 running produced
  refine ⟨built.1, ⟨SourceRecursiveIntersectionThunks.finishEdge selected.1 built.1
    (advance current {current.machine with heap := built.2}), SourceEqualityMkEdgeAllocation.emptyField state.operations⟩,
    mismatch_complete request state mismatch started, completed, produced, certificate.1, certificate.2.1, ?_⟩
  exact FlatMemoThunk.finish_evaluating selected.1 built.1 current.edges request running

/-- A fresh mismatched native publication derives its own completion receipt and both checked memo invariants. -/
theorem mismatch_miss_native_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (inputs : EdgeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (missing : state.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    ∃ result after, execute 5 (.code (.edge request .pure)) state = .done result after ∧
      SourceEqualityNativeDemandProvenance.Valid holds after.native ∧
      EdgeProduced (width := width) holds after.native.machine request result ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap result ∧
      after.native.edges.cells (lookupEdge width request state.native).1 = some ⟨request, .returned result⟩ :=
  mismatch_native_valid holds request state valid heapReady inputs safe mismatch (edge_miss_starts request state missing)

end MicroCFTA.SourceEqualityNativeDemandMismatchReceipt
