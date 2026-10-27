import MicroCFTA.SourceEqualityNativeDemandChildWalk
import MicroCFTA.SourceEqualityNativeDemandAcceptedLanguage
import MicroCFTA.SourceEqualityNativeDemandControl

/-!
# Accepted checked edge bodies from actual child calls

The prefix retains its actual conjunction and accessor effects. Each child
call supplies its actual checked trace and proved recursive receipt. The
ordered fold derives constructor inputs and complete edge provenance. This
is a compositional proof. General child receipt derivation remains separate.
-/
namespace MicroCFTA.SourceEqualityNativeDemandAcceptedReceipt
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Actual child traces precede the final edge constructor in the exact accepted code. -/
theorem children_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (combined : Allocated)
    (before after : State width) (values : List (Value Symbol Guard)) (fuel : Nat)
    (walk : SourceEqualityNativeDemandChildWalk.Walk holds request.domain
      (request.left.children.zip request.right.children) before values after fuel) :
    let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) after.native.machine.heap
    Steps (fuel + 1) (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)) before
      (.code (.pure built.1)) {after with native := advance after.native {after.native.machine with heap := built.2}} := by
  let job := makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values
  let built := run job after.native.machine.heap
  have walked := walk.trace.bind _ _ _ _ _ (fun values =>
    .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure)
  have builtTrace : Steps 1 (.code (.work job .pure)) after (.code (.pure built.1))
      {after with native := advance after.native {after.native.machine with heap := built.2}} :=
    .cons _ _ _ _ _ _ 0 rfl (.refl _ _)
  exact walked.trans _ _ _ _ _ _ _ _ builtTrace

/-- Actual accepted prefix and child traces give the full standalone checked edge-body trace. -/
theorem body_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (state after : State width)
    (first second combined : Allocated) (values : List (Value Symbol Guard)) (fuel : Nat)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    (walk : SourceEqualityNativeDemandChildWalk.Walk holds request.domain
      (request.left.children.zip request.right.children)
      {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length state.operations).2} values after fuel) :
    let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) after.native.machine.heap
    Steps (fuel + 2) (.edgeBody request .pure) state (.code (.pure built.1))
      {after with native := advance after.native {after.native.machine with heap := built.2}} := by
  have firstStep := body_ready request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    state arity first second combined left right accepted
  simp only [code_bind_pure] at firstStep
  exact .cons _ _ _ _ _ _ (fuel + 1) firstStep (children_trace holds request combined _ after values fuel walk)

/-- Verified actual child calls derive accepted edge provenance and actual heap preservation. -/
theorem body_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state after : State width)
    (first second combined : Allocated) (values : List (Value Symbol Guard)) (fuel : Nat)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (inputs : EdgeReady state.native.machine request)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    (walk : SourceEqualityNativeDemandChildWalk.Walk (SourceEqualityPCSGuard.holds formulas solver) request.domain
      (request.left.children.zip request.right.children)
      {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length state.operations).2} values after fuel) :
    let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) after.native.machine.heap
    let final : State width := {after with native := advance after.native {after.native.machine with heap := built.2}}
    execute (fuel + 3) (.edgeBody request .pure) state = .done built.1 final ∧
      EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) final.native.machine request built.1 ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap final.native.machine.heap ∧
      EdgeResident final.native.machine.heap built.1 ∧ built.1.children = values ∧ built.1.children.length = request.left.children.length := by
  let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) after.native.machine.heap
  let final : State width := {after with native := advance after.native {after.native.machine with heap := built.2}}
  have children := walk.effects heapReady
  have constructor := SourceEqualityRequiredCache.edge request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values after.native.machine.heap children.1.ready children.2.2.1
  have fields := MergedPhysicalGroupEdges.makeEdge_fields after.native.machine.heap children.1.ready.semantic.1.normal.facts
    request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values children.2.2.1
  have literal := SourceEqualityNativeDemandAcceptedLanguage.ready_readback request state first second combined valid
    leftCached rightCached arity left right accepted
  have meaning := SourceEqualityNativeDemandAcceptedLanguage.edgeMeaning_of_nodes formulas solver request built.1 arity symbols
    fields.1 (fields.2.1.trans literal) (by rw [constructor.2.2]; exact children.2.2.2)
  have finished : execute (fuel + 3) (.edgeBody request .pure) state = .done built.1 final :=
    trace_done (fuel + 2) _ state final built.1 (body_trace _ request state after first second combined values fuel arity left right accepted walk)
  have extension : Extension state.native.machine final.native.machine :=
    children.2.1.trans ⟨constructor.1.growth, constructor.1.history, Cache.extends_refl _⟩
  have produced : EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) final.native.machine request built.1 :=
    ⟨state, final, fuel + 3, inputs, finished, extension, constructor.2.1, Extension.refl _, meaning⟩
  refine ⟨finished, produced, children.1.trans constructor.1, constructor.2.1, constructor.2.2, ?_⟩
  rw [constructor.2.2, walk.length, List.length_zip, arity, Nat.min_self]

end MicroCFTA.SourceEqualityNativeDemandAcceptedReceipt
