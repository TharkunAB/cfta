import MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning
open MicroCFTA Cache Language BinderLanguage InternedBinderProtocol
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePairContexts SourceCurrentAllocatedNativeContextCache
open SourceCurrentAllocatedNativeEdgeMeaning
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.joined_symbols
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.zip_inputs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.edge_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.Walk.actual
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.Walk.effects
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.children_trace
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.accepted_body
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.rowAt_mismatch
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.rejected_source
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.rowAt_rejected
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.sentinel_edge_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.mismatch_body
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.rejected_body
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.joined_symbols
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.zip_inputs
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.edge_law
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.Walk.actual
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.Walk.effects
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.children_trace
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.accepted_body
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.rowAt_mismatch
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.rejected_source
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.rowAt_rejected
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.sentinel_edge_law
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.mismatch_body
#check @MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning.rejected_body

namespace ContextEdgeChecks
noncomputable section
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local instance : DecidableEq Symbol := Classical.typeDecidableEq _
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

def raw (symbol : Symbol) (constraint : Guard) (children : List (Value Symbol Guard)) : EdgeValue Symbol Guard :=
  .mk ⟨0, ⟨symbol, children.map Value.referenceOf, constraint⟩⟩ children

def impossible : Guard := ⟨none, .top⟩
def stopped : Allocated := ⟨.contradiction, .top⟩

-- 1. The actual row join supplies matching symbols.
example (left right : List (EdgeValue Symbol Guard)) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard)
    (member : pair ∈ SourceRecursiveIntersectionKernel.pairs left right) : pair.1.entry.key.symbol = pair.2.entry.key.symbol :=
  joined_symbols left right pair member

-- 2. Unequal row arities reject without a child semantic premise.
example (holds : Guard → Term Symbol → Bool) (ranks : Nat → Nat → Lang Symbol) (symbol : Symbol) (term : Term Symbol) :
    ¬ (RowAt holds ranks 5 (raw symbol impossible []) term ∧ RowAt holds ranks 9 (raw symbol impossible [.empty]) term) :=
  rowAt_mismatch holds ranks _ _ (by change 0 ≠ 1; decide) 5 9 term

-- 3. The literal contradictory allocated field selects rejection before child construction.
example (operations : SourceEqualityConstraintMemoAllocation.State) :
    (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le stopped stopped 0 0 operations).1 = .ok .rejected := by
  rfl

-- 4. Contradictory original storage loads directly, without allocation.
example (operations : SourceEqualityConstraintMemoAllocation.State) :
    SourceEqualityConstraintFieldLookup.load impossible operations.constraints = .ok (some stopped) := rfl

-- 5. Mismatch executes the exact sentinel branch in three steps.
example (symbol : Symbol) (state : SourceEqualityNativeDemand.State 8) :
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, raw symbol impossible [], raw symbol impossible [.empty]⟩
    let built := run (makeEdge symbol SourceEqualityConstraintConstructors.top [.empty]) state.native.machine.heap
    execute 3 (.edgeBody request .pure) state = .done built.1
      ⟨advance state.native {state.native.machine with heap := built.2}, SourceEqualityMkEdgeAllocation.emptyField state.operations⟩ := by
  exact SourceEqualityNativeDemandMismatchReceipt.mismatch_body_complete _ state (by change 0 ≠ 1; decide)

-- 6. A rejected leaf body derives its contextual law with no child law.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (symbol : Symbol) (state : SourceEqualityNativeDemand.State 8)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap) :
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, raw symbol impossible [], raw symbol impossible []⟩
    let built := run (makeEdge symbol SourceEqualityConstraintConstructors.top [.empty]) state.native.machine.heap
    EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request built.1 := by
  have cached : SourceEqualityGuardReadback.Cached impossible.equalities := by intro classes equal; cases equal
  exact (rejected_body view model ranked formulas solver
    ⟨IntersectionEmptyDomain.emptyDomain, raw symbol impossible [], raw symbol impossible []⟩
    state stopped stopped valid ready cached cached rfl rfl rfl rfl).2.1

-- 7. An empty reached child walk derives its physical and semantic fold receipts.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (state : SourceEqualityNativeDemand.State 8) (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap) :
    SourceEqualityRequiredCache.Keeps state.native.machine.heap state.native.machine.heap ∧
      InternedNestedProvenance.Values state.native.machine.heap [] ∧
      All₂ (fun (pair : Value Symbol Guard × Value Symbol Guard) child =>
        NodeLaw view model ranked holds ⟨IntersectionEmptyDomain.emptyDomain, pair.1, pair.2⟩ child) [] [] :=
  (Walk.nil state : Walk view model ranked holds IntersectionEmptyDomain.emptyDomain [] state [] state 0).effects ready

-- 8. The accepted leaf case needs no recursive child semantic callback.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State 8) (first second combined : Allocated)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (leftChildren : request.left.children = []) (rightChildren : request.right.children = [])
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 state.operations).1 = .ok (.ready combined)) :
    let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 state.operations
    let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) []) state.native.machine.heap
    let after : SourceEqualityNativeDemand.State 8 := {state with
      native := advance state.native {state.native.machine with heap := built.2}, operations := checked.2}
    execute 3 (.edgeBody request .pure) state = .done built.1 after ∧
      EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request built.1 := by
  let childState : SourceEqualityNativeDemand.State 8 := {state with operations :=
    (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 state.operations).2}
  have walked : Walk view model ranked (SourceEqualityPCSGuard.holds formulas solver) request.domain
      (request.left.children.zip request.right.children) childState [] childState 0 := by
    simpa only [leftChildren, rightChildren, List.zip_nil_left] using
      (Walk.nil childState : Walk view model ranked (SourceEqualityPCSGuard.holds formulas solver) request.domain [] childState [] childState 0)
  have parent := accepted_body view model ranked formulas solver request state childState first second combined [] 0
    valid ready leftCached rightCached (by rw [leftChildren, rightChildren]) symbols left right
    (by simpa only [leftChildren, rightChildren, List.length_nil] using accepted)
    (by simpa only [leftChildren, rightChildren, List.length_nil] using walked)
  exact ⟨parent.1, parent.2.1⟩

-- 9. Distinct symbols refute a standalone edge law, even with empty child lists.
theorem distinct_symbols_boundary (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (first second : Symbol) (different : first ≠ second) :
    ¬ EdgeLaw view model ranked (fun _ _ => true)
      ⟨IntersectionEmptyDomain.emptyDomain, raw first impossible [], raw second impossible []⟩ (raw first impossible []) := by
  intro law
  let output : InternedGuardedLanguage.Env Symbol := fun _ _ => False
  have inputs : EdgeInputs view model ⟨IntersectionEmptyDomain.emptyDomain, raw first impossible [], raw second impossible []⟩ := by
    constructor <;> intro child member <;> cases member
  have accepted : InternedGuardedLanguage.edgeMeaning (fun _ _ => true) output (raw first impossible []) (.node first []) :=
    (InternedGuardedLanguage.edgeMeaning_all _ _ _ _).mpr ⟨[], rfl, .nil, rfl⟩
  have common := law.sound inputs output (sound_empty_domain _ output) _ accepted
  obtain ⟨terms, same, _, _⟩ := common.2
  exact different (Term.node.inj same).1

-- 10. A concrete singleton actual walk retains exactly its reached local child law.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pair : Value Symbol Guard × Value Symbol Guard) (before middle : SourceEqualityNativeDemand.State 8)
    (value : Value Symbol Guard) (fuel : Nat)
    (trace : Steps fuel (.code (requestNode domain pair.1 pair.2)) before (.code (.pure value)) middle)
    (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap)
    (available : Available middle.native.machine.heap value)
    (law : NodeLaw view model ranked holds ⟨domain, pair.1, pair.2⟩ value) :
    Walk view model ranked holds domain [pair] before [value] middle (fuel + 0) :=
  .cons pair [] before middle middle value [] fuel 0 trace keeps available law (.nil middle)
end
end ContextEdgeChecks
