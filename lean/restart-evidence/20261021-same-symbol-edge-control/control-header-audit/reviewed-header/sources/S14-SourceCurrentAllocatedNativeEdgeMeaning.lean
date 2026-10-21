import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceEqualityNativeDemandAcceptedReadback
import MicroCFTA.SourceEqualityNativeDemandMismatchReceipt

/-!
# Contextual laws for actual checked edge bodies

Accepted bodies use only the actual ordered child calls and their local
node laws. The final source edge constructor derives its complete fields.
Mismatch and checked rejection emit only the literal sentinel. No parent
edge law, parent produced receipt, or eager execution equivalence is used.
Local child trace effects and contextual node laws remain recursive
induction hypotheses. Matching symbols come from the parent row join.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning
open Cache Language BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePairContexts SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Pair" => Value Symbol Guard × Value Symbol Guard
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- The actual parent join derives the matching symbols needed by an edge body. -/
theorem joined_symbols [DecidableEq Symbol] (left right : List (EdgeValue Symbol Guard)) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard)
    (member : pair ∈ SourceRecursiveIntersectionKernel.pairs left right) : pair.1.entry.key.symbol = pair.2.entry.key.symbol :=
  ((SourceRecursiveIntersectionKernel.pairs_member left right pair).mp member).2.2

private theorem forest_sound (left right results : List (Value Symbol Guard))
    (resultMeaning leftMeaning rightMeaning : Value Symbol Guard → Term Symbol → Prop)
    (arity : left.length = right.length)
    (laws : All₂ (fun pair result => ∀ term, resultMeaning result term →
      leftMeaning pair.1 term ∧ rightMeaning pair.2 term) (left.zip right) results)
    (terms : List (Term Symbol)) (accepted : All₂ resultMeaning results terms) :
    All₂ leftMeaning left terms ∧ All₂ rightMeaning right terms := by
  induction left generalizing right results terms with
  | nil =>
      have empty : right = [] := List.length_eq_zero_iff.mp arity.symm
      subst right; cases laws; cases accepted
      exact ⟨.nil, .nil⟩
  | cons first rest ih =>
      cases right with
      | nil => simp at arity
      | cons second tail =>
          cases laws with
          | cons head later =>
              cases accepted with
              | cons firstAccepted remaining =>
                  have common := head _ firstAccepted
                  have rest := ih tail _ (Nat.succ.inj arity) later _ remaining
                  exact ⟨.cons common.1 rest.1, .cons common.2 rest.2⟩

private theorem forest_complete (left right results : List (Value Symbol Guard))
    (resultMeaning leftMeaning rightMeaning : Value Symbol Guard → Term Symbol → Prop)
    (laws : All₂ (fun pair result => ∀ term, leftMeaning pair.1 term → rightMeaning pair.2 term →
      resultMeaning result term) (left.zip right) results)
    (terms : List (Term Symbol)) (first : All₂ leftMeaning left terms) (second : All₂ rightMeaning right terms) :
    All₂ resultMeaning results terms := by
  induction first generalizing right results with
  | nil => cases second; cases laws; exact .nil
  | cons accepted remaining ih =>
      cases second with
      | cons other rest =>
          cases laws with
          | cons head tail => exact .cons (head _ accepted other) (ih _ _ tail rest)

/-- Each accepted zip entry inherits exactly its original input scope. -/
theorem zip_inputs (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs view model request) (pair : Pair)
    (member : pair ∈ request.left.children.zip request.right.children) :
    NodeInputs view model ⟨request.domain, pair.1, pair.2⟩ := by
  have inside := List.of_mem_zip member
  exact ⟨(inputs.1 pair.1 inside.1).1, (inputs.2 pair.2 inside.2).1,
    (inputs.1 pair.1 inside.1).2, (inputs.2 pair.2 inside.2).2⟩

/-- Actual result fields and local child laws derive both contextual edge directions. -/
theorem edge_law (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (label : result.entry.key.symbol = request.left.entry.key.symbol)
    (guards : ∀ term, holds result.entry.key.constraint term =
      (holds request.left.entry.key.constraint term && holds request.right.entry.key.constraint term))
    (children : All₂ (fun pair child => NodeLaw view model ranked holds ⟨request.domain, pair.1, pair.2⟩ child)
      (request.left.children.zip request.right.children) result.children) : EdgeLaw view model ranked holds request result := by
  constructor
  · intro inputs output sound term accepted
    obtain ⟨terms, shape, forest, guard⟩ := (InternedGuardedLanguage.edgeMeaning_all holds output result term).mp accepted
    have localLaws := MergedPhysicalGroupCalls.all₂_left_imp _ _ _ _ children (fun pair member child law =>
      law.sound (zip_inputs view model request inputs pair member) output sound)
    have common := forest_sound request.left.children request.right.children result.children
      (InternedGuardedLanguage.meaning holds output)
      (fun child part => IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf child) part)
      (fun child part => IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf child) part)
      arity localLaws terms forest
    have gates := Bool.and_eq_true_iff.mp ((guards term).symm.trans guard)
    exact ⟨⟨terms, by rw [← label]; exact shape, common.1, gates.1⟩,
      ⟨terms, by rw [← symbols, ← label]; exact shape, common.2, gates.2⟩⟩
  · intro inputs bound output complete first second bounded term left right
    obtain ⟨terms, shape, leftForest, leftGuard⟩ := left
    obtain ⟨other, otherShape, rightForest, rightGuard⟩ := right
    have same : other = terms := by
      rw [shape, ← symbols] at otherShape
      exact (Term.node.inj otherShape).2.symm
    subst other
    apply (InternedGuardedLanguage.edgeMeaning_all holds output result term).mpr
    refine ⟨terms, by rw [label]; exact shape, ?_, ?_⟩
    · have localLaws := MergedPhysicalGroupCalls.all₂_left_imp _ _ _ _ children (fun pair member child law =>
        fun part left right => law.complete (zip_inputs view model request inputs pair member)
          bound output complete first second bounded part left right)
      exact forest_complete request.left.children request.right.children result.children
        (InternedGuardedLanguage.meaning holds output)
        (fun child part => IntersectSchedule.inputAt ranked.languages (SourceRecursiveIntersectionInputView.inputOf child) first part)
        (fun child part => IntersectSchedule.inputAt ranked.languages (SourceRecursiveIntersectionInputView.inputOf child) second part)
        localLaws terms leftForest rightForest
    · rw [guards term, leftGuard, rightGuard]; rfl

/-- Each actual reached child trace carries only that child's proved effects and contextual law. -/
inductive Walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    List Pair → SourceEqualityNativeDemand.State width → List (Value Symbol Guard) → SourceEqualityNativeDemand.State width → Nat → Prop where
  | nil (state) : Walk view model ranked holds domain [] state [] state 0
  | cons (pair : Pair) (rest) (before middle after : SourceEqualityNativeDemand.State width) (value values firstFuel restFuel)
      (called : Steps firstFuel (.code (requestNode domain pair.1 pair.2)) before (.code (.pure value)) middle)
      (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap)
      (available : Available middle.native.machine.heap value)
      (law : NodeLaw view model ranked holds ⟨domain, pair.1, pair.2⟩ value)
      (tail : Walk view model ranked holds domain rest middle values after restFuel) :
      Walk view model ranked holds domain (pair :: rest) before (value :: values) after (firstFuel + restFuel)

/-- The local certificates erase to exactly the actual ordered child executions. -/
theorem Walk.actual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {view : IntersectSchedule.View Symbol} {model : IntersectSchedule.InputMeaning view}
    {ranked : IntersectSchedule.RankedInput view model.valid} {holds : Guard → Term Symbol → Bool}
    {domain : Interned IntersectionFlatMemoKeyDomain.DomainKey} {pairs : List Pair} {before after : SourceEqualityNativeDemand.State width}
    {values : List (Value Symbol Guard)} {fuel : Nat} (walk : Walk view model ranked holds domain pairs before values after fuel) :
    SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode domain pair.1 pair.2) pairs before values after fuel := by
  induction walk with
  | nil state => exact .nil state
  | cons pair rest before middle after value values firstFuel restFuel called keeps available law tail ih =>
      exact .cons pair rest before middle after value values firstFuel restFuel called ih

/-- Actual child effects derive final readiness, available values, and all local laws. -/
theorem Walk.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {view : IntersectSchedule.View Symbol} {model : IntersectSchedule.InputMeaning view}
    {ranked : IntersectSchedule.RankedInput view model.valid} {holds : Guard → Term Symbol → Bool}
    {domain : Interned IntersectionFlatMemoKeyDomain.DomainKey} {pairs : List Pair} {before after : SourceEqualityNativeDemand.State width}
    {values : List (Value Symbol Guard)} {fuel : Nat} (walk : Walk view model ranked holds domain pairs before values after fuel)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap) :
    SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      InternedNestedProvenance.Values after.native.machine.heap values ∧
      All₂ (fun pair value => NodeLaw view model ranked holds ⟨domain, pair.1, pair.2⟩ value) pairs values := by
  induction walk with
  | nil state => exact ⟨SourceEqualityRequiredCache.pure_keeps _ ready, (by intro value member; cases member), .nil⟩
  | cons pair rest before middle after value values firstFuel restFuel called keeps available law tail ih =>
      have later := ih keeps.ready
      refine ⟨keeps.trans later.1, ?_, .cons law later.2.2⟩
      intro child member
      cases member with
      | head => exact later.1.available value available
      | tail _ member => exact later.2.1 child member

/-- Accepted actual child traces precede exactly one final edge constructor. -/
theorem children_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {view : IntersectSchedule.View Symbol} {model : IntersectSchedule.InputMeaning view}
    {ranked : IntersectSchedule.RankedInput view model.valid} {holds : Guard → Term Symbol → Bool}
    (request : EdgeRequest Symbol Guard) (combined : Allocated) (before after : SourceEqualityNativeDemand.State width)
    (values : List (Value Symbol Guard)) (fuel : Nat)
    (walk : Walk view model ranked holds request.domain (request.left.children.zip request.right.children) before values after fuel) :
    let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) after.native.machine.heap
    Steps (fuel + 1) (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)) before
      (.code (.pure built.1)) {after with native := advance after.native {after.native.machine with heap := built.2}} := by
  have first := walk.actual.trace.bind _ _ _ _ _ (fun values =>
    .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure)
  exact first.trans _ _ _ _ _ _ _ _ (.cons _ _ _ _ _ _ 0 rfl (.refl _ _))

/-- A checked ready prefix, actual child laws, and actual construction derive the parent law. -/
theorem accepted_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (before middle : SourceEqualityNativeDemand.State width) (first second combined : Allocated)
    (values : List (Value Symbol Guard)) (fuel : Nat) (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined))
    (walk : Walk view model ranked (SourceEqualityPCSGuard.holds formulas solver) request.domain
      (request.left.children.zip request.right.children)
      {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length before.operations).2} values middle fuel) :
    let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) middle.native.machine.heap
    let after : SourceEqualityNativeDemand.State width := {middle with native := advance middle.native {middle.native.machine with heap := built.2}}
    execute (fuel + 3) (.edgeBody request .pure) before = .done built.1 after ∧
      EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request built.1 ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      EdgeResident after.native.machine.heap built.1 := by
  have childEffects := walk.effects ready
  have constructor := SourceEqualityRequiredCache.edge request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values middle.native.machine.heap childEffects.1.ready childEffects.2.1
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.native.machine.heap childEffects.1.ready.semantic.1.normal.facts
    request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values childEffects.2.1
  have literal := SourceEqualityNativeDemandAcceptedLanguage.ready_readback request before first second combined valid
    leftCached rightCached arity left right accepted
  have law := edge_law view model ranked (SourceEqualityPCSGuard.holds formulas solver) request _ arity symbols fields.1
    (fun term => by rw [fields.2.1, literal]; exact SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver _ _ term)
    (by rw [constructor.2.2]; exact childEffects.2.2)
  have prefixStep := body_ready request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    before arity first second combined left right accepted
  simp only [code_bind_pure] at prefixStep
  exact ⟨trace_done (fuel + 2) _ before _ _ (.cons _ _ _ _ _ _ (fuel + 1) prefixStep
    (children_trace request combined _ middle values fuel walk)), law, childEffects.1.trans constructor.1, constructor.2.1⟩

/-- Different original row arities have no common bounded input forest. -/
theorem rowAt_mismatch (holds : Guard → Term Symbol → Bool) (ranks : Nat → Nat → Lang Symbol)
    (left right : EdgeValue Symbol Guard) (mismatch : left.children.length ≠ right.children.length)
    (first second : Nat) (term : Term Symbol) : ¬ (RowAt holds ranks first left term ∧ RowAt holds ranks second right term) := by
  rintro ⟨⟨terms, shape, firstForest, _⟩, ⟨other, otherShape, secondForest, _⟩⟩
  have same := (Term.node.inj (shape.symm.trans otherShape)).2
  exact mismatch (firstForest.length_eq.trans ((congrArg List.length same).trans secondForest.length_eq.symm))

/-- The actual checked allocation rejection derives rejection of the original source constraints. -/
theorem rejected_source (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (first second : Allocated)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected) :
    SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le request.left.entry.key.constraint
      request.right.entry.key.constraint request.left.children.length request.right.children.length = .rejected := by
  obtain ⟨firstReady, firstFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints leftCached first left
  obtain ⟨secondReady, secondFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints rightCached second right
  obtain ⟨branch, done, source, _, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le
    first second request.left.children.length request.right.children.length state.operations valid firstReady secondReady
  have same : branch = .rejected := Except.ok.inj (done.symm.trans rejected)
  rw [same] at source
  simpa only [SourceEqualityIntersectionEdgeAllocation.Branch.map, firstFields, secondFields] using source.symm

/-- Checked source rejection has no common bounded row term before child demand. -/
theorem rowAt_rejected (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ranks : Nat → Nat → Lang Symbol) (request : EdgeRequest Symbol Guard)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (rejected : SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le request.left.entry.key.constraint
      request.right.entry.key.constraint request.left.children.length request.right.children.length = .rejected)
    (first second : Nat) (term : Term Symbol) :
    ¬ (RowAt (SourceEqualityPCSGuard.holds formulas solver) ranks first request.left term ∧
      RowAt (SourceEqualityPCSGuard.holds formulas solver) ranks second request.right term) := by
  rintro ⟨⟨terms, shape, forest, firstGuard⟩, ⟨_, _, _, secondGuard⟩⟩
  have firstPublic := (SourceEqualityPCSGuard.public_eq formulas solver request.left.entry.key.constraint
    (SourceEqualityGuardReadback.active leftCached) term).symm.trans firstGuard
  have secondPublic := (SourceEqualityPCSGuard.public_eq formulas solver request.right.entry.key.constraint
    (SourceEqualityGuardReadback.active rightCached) term).symm.trans secondGuard
  rw [shape] at firstPublic secondPublic
  exact SourceEqualityNativeDemand.rejected_no_term formulas solver _ _ _ _ leftCached rightCached rejected
    _ terms forest.length_eq.symm ⟨firstPublic, secondPublic⟩

/-- A literal empty child and independent input disjointness derive the contextual sentinel law. -/
theorem sentinel_edge_law (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) (children : result.children = [.empty])
    (disjoint : ∀ first second term, ¬ (RowAt holds ranked.languages first request.left term ∧
      RowAt holds ranked.languages second request.right term)) : EdgeLaw view model ranked holds request result := by
  constructor
  · intro _ output _ term accepted
    exact False.elim (SourceEqualityNativeDemandMismatchProvenance.empty_child_rejects result children holds output term accepted)
  · intro _ _ _ _ first second _ term left right
    exact False.elim (disjoint first second term ⟨left, right⟩)

/-- Mismatch completes without children at the exact sentinel heap and empty-field state. -/
theorem mismatch_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : EdgeRequest Symbol Guard) (before : SourceEqualityNativeDemand.State width)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    let built := run (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap
    let after : SourceEqualityNativeDemand.State width :=
      ⟨advance before.native {before.native.machine with heap := built.2}, SourceEqualityMkEdgeAllocation.emptyField before.operations⟩
    execute 3 (.edgeBody request .pure) before = .done built.1 after ∧
      EdgeLaw view model ranked holds request built.1 ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧ EdgeResident after.native.machine.heap built.1 := by
  have constructor := SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance request.left.entry.key.symbol before.native.machine.heap ready
  exact ⟨SourceEqualityNativeDemandMismatchReceipt.mismatch_body_complete request before mismatch,
    sentinel_edge_law view model ranked holds request _ constructor.2.2.2.2.1
      (rowAt_mismatch holds ranked.languages request.left request.right mismatch), constructor.1, constructor.2.1⟩

/-- Rejection skips children and retains both allocation stages in the literal returned state. -/
theorem rejected_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (before : SourceEqualityNativeDemand.State width) (first second : Allocated)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations).1 = .ok .rejected) :
    let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length before.operations
    let built := run (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap
    let after : SourceEqualityNativeDemand.State width :=
      ⟨advance before.native {before.native.machine with heap := built.2}, SourceEqualityMkEdgeAllocation.emptyField checked.2⟩
    execute 3 (.edgeBody request .pure) before = .done built.1 after ∧
      EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request built.1 ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧ EdgeResident after.native.machine.heap built.1 := by
  have constructor := SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance request.left.entry.key.symbol before.native.machine.heap ready
  have sourceRejected := rejected_source request before valid leftCached rightCached first second left right rejected
  refine ⟨?_, sentinel_edge_law view model ranked (SourceEqualityPCSGuard.holds formulas solver) request _ constructor.2.2.2.2.1
    (rowAt_rejected formulas solver ranked.languages request leftCached rightCached sourceRejected), constructor.1, constructor.2.1⟩
  have prefixStep := body_rejected request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    before arity first second left right rejected
  simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, prefixStep]
  rfl

end MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning
