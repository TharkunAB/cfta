import MicroCFTA.SourceEqualityNativeDemandMismatchReceipt

/-!
# Actual checked rejection receipts

Equal-arity rejection retains the actual raw conjunction and accessor
effects. The sentinel then demands the empty equality field and constructs
the actual edge. Independent source constraint meaning proves the empty
intersection language. Checked completion installs that derived receipt.
-/
namespace MicroCFTA.SourceEqualityNativeDemandRejectedReceipt
open Language Cache InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- The actual rejected body retains all reached accessor effects before sentinel completion. -/
theorem rejected_body_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width) (first second : Allocated)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected) :
    let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations
    let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap
    execute 3 (.edgeBody request .pure) state = .done built.1
      ⟨advance state.native {state.native.machine with heap := built.2}, SourceEqualityMkEdgeAllocation.emptyField checked.2⟩ := by
  simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
    body_rejected request _ state arity first second left right rejected]
  rfl

/-- Actual rejected-prefix allocation followed by the sentinel retains valid growing operation caches. -/
theorem rejected_operations (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (first second : Allocated) (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected) :
    let after := SourceEqualityMkEdgeAllocation.emptyField (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le
      first second request.left.children.length request.right.children.length state.operations).2
    SourceEqualityConstraintMemoAllocation.Valid after ∧ SourceEqualityConstraintMemoAllocation.Grows state.operations after := by
  have checked := SourceEqualityNativeDemandOperations.body_operations request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    state valid leftCached rightCached
  rw [body_rejected request _ state arity first second left right rejected] at checked
  exact checked

/-- The actual rejected sentinel has exact PCS intersection language for every domain and input closure. -/
theorem rejected_result_language [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width) (first second : Allocated)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected) :
    let result := (InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap).1
    ∀ ambient term, InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.left term ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.right term := by
  have certificate := SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance request.left.entry.key.symbol state.native.machine.heap heapReady
  dsimp only
  intro ambient term
  exact ⟨fun accepted => False.elim (certificate.2.2.2.2.2 _ ambient term accepted),
    fun common => False.elim (rejected_disjoint formulas solver ambient request state valid leftCached rightCached
      first second left right rejected term common)⟩

/-- Source rejection derives its own actual checked body receipt and independent PCS intersection law. -/
theorem rejected_body_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width) (first second : Allocated)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap) (inputs : EdgeReady state.native.machine request)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected) :
    let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap
    EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver)
      {state.native.machine with heap := built.2} request built.1 := by
  let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
    request.left.children.length request.right.children.length state.operations
  let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) state.native.machine.heap
  have certificate := SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance request.left.entry.key.symbol state.native.machine.heap heapReady
  refine ⟨state, ⟨advance state.native {state.native.machine with heap := built.2},
    SourceEqualityMkEdgeAllocation.emptyField checked.2⟩, 3, inputs,
    rejected_body_complete request state first second arity left right rejected,
    ⟨certificate.1.growth, certificate.1.history, Cache.extends_refl _⟩,
    certificate.2.1, Extension.refl _, ?_⟩
  intro _ _ _ ambient term
  exact rejected_result_language formulas solver request state first second valid heapReady leftCached rightCached left right rejected ambient term

/-- Native rejection completes at its actual selected handle with every reached equality effect retained. -/
theorem rejected_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width) (first second : Allocated)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected)
    (started : (demandEdge (lookupEdge width request state.native).1 (lookupEdge width request state.native).2).1 = .evaluate request) :
    let selected := lookupEdge width request state.native
    let current := (demandEdge selected.1 selected.2).2
    let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations
    let built := InternedConstructorTemplates.run (makeEdge request.left.entry.key.symbol top [.empty]) current.machine.heap
    execute 5 (.code (.edge request .pure)) state = .done built.1
      ⟨SourceRecursiveIntersectionThunks.finishEdge selected.1 built.1
        (advance current {current.machine with heap := built.2}), SourceEqualityMkEdgeAllocation.emptyField checked.2⟩ := by
  let selected := lookupEdge width request state.native
  let current := (demandEdge selected.1 selected.2).2
  have stopped := body_rejected request (fun value => .finishEdge selected.1 value (.pure value))
    ({state with native := current}) arity first second left right rejected
  simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, started]
  rw [stopped]
  rfl

/-- Actual rejection installs its derived receipt and retains all reached native and equality caches. -/
theorem rejected_native_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width) (first second : Allocated)
    (valid : SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap) (inputs : EdgeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected)
    (started : (demandEdge (lookupEdge width request state.native).1 (lookupEdge width request state.native).2).1 = .evaluate request) :
    ∃ result after, execute 5 (.code (.edge request .pure)) state = .done result after ∧
      SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) after.native ∧
      EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) after.native.machine request result ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap result ∧
      after.native.edges.cells (lookupEdge width request state.native).1 = some ⟨request, .returned result⟩ ∧
      after.operations = SourceEqualityMkEdgeAllocation.emptyField (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le
        first second request.left.children.length request.right.children.length state.operations).2 ∧
      SourceEqualityConstraintMemoAllocation.Valid after.operations ∧ SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations := by
  let selected := lookupEdge width request state.native
  let current := (demandEdge selected.1 selected.2).2
  let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
    request.left.children.length request.right.children.length state.operations
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
  have produced := rejected_body_produced formulas solver request (⟨current, state.operations⟩ : SourceEqualityNativeDemand.State width)
    first second operationsValid heapReady inputs leftCached rightCached arity left right rejected
  have completed := SourceEqualityNativeDemandProvenance.finishEdge_valid
    (advance current {current.machine with heap := built.2}) advancedValid selected.1 request built.1 running produced
  have operations := rejected_operations request state first second operationsValid leftCached rightCached arity left right rejected
  refine ⟨built.1, ⟨SourceRecursiveIntersectionThunks.finishEdge selected.1 built.1
    (advance current {current.machine with heap := built.2}), SourceEqualityMkEdgeAllocation.emptyField checked.2⟩,
    rejected_complete request state first second arity left right rejected started, completed, produced, certificate.1, certificate.2.1,
    ?_, rfl, operations.1, operations.2⟩
  exact FlatMemoThunk.finish_evaluating selected.1 built.1 current.edges request running

/-- A fresh rejected request derives full checked completion without a supplied native demand observation. -/
theorem rejected_miss_native_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width) (first second : Allocated)
    (valid : SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap) (inputs : EdgeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected)
    (missing : state.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    ∃ result after, execute 5 (.code (.edge request .pure)) state = .done result after ∧
      SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) after.native ∧
      EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) after.native.machine request result ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap result ∧
      after.native.edges.cells (lookupEdge width request state.native).1 = some ⟨request, .returned result⟩ ∧
      after.operations = SourceEqualityMkEdgeAllocation.emptyField (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le
        first second request.left.children.length request.right.children.length state.operations).2 ∧
      SourceEqualityConstraintMemoAllocation.Valid after.operations ∧ SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations :=
  rejected_native_valid formulas solver request state first second valid operationsValid heapReady inputs safe leftCached rightCached
    arity left right rejected (edge_miss_starts request state missing)

end MicroCFTA.SourceEqualityNativeDemandRejectedReceipt
