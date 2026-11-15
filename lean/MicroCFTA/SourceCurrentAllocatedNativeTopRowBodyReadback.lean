import MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback
import MicroCFTA.SourceCurrentAllocatedNativePrefixInputs
import MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit
import MicroCFTA.SourceCurrentNativeOpenRequestResults

/-!
# Raw self-Top row readback from actual smaller node queries

Completion forces the successful original field load.
Valid operations and Top exclude both rejected sentinel branches.
The original input plan supplies checks for the same raw trace.
Smaller child hypotheses use their actual raw step counts.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeTopRowBodyReadback
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel (Extension)
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedNestedProvenance (Values)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Pair" => Value Symbol Guard × Value Symbol Guard
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

set_option autoImplicit false

private theorem source_top_ready (arity : Nat) :
    SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le top top arity arity = .ready top := by
  unfold SourceEqualityIntersectionEdgeAllocation.source
  rw [ite_eq_right (by intro different; exact different rfl)]
  rw [SourceSynthesisUniverseTopConjunction.conjoin_top GuardStructuralOrder.le]
  have acceptedTop : SourceEqualityMkEdgeAllocation.accepted top arity = true := by
    simp [SourceEqualityMkEdgeAllocation.accepted, SourceEqualityMkEdgeAllocation.contradictory,
      SourceEqualityConstraintConstructors.top, SourceCompactGuards.sourceEqualities,
      SourceCompactGuards.positiveNormalized, SourceEqualityMkEdgeAllocation.fits,
      SourceEqualityMkEdgeAllocation.signed, SymbolicSignedPaths.fitsArity]
  exact ite_eq_left acceptedTop

private theorem ready_of_raw_trace
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before after : Checked width) (bodySteps : Nat)
    (row : EdgeValue Symbol Guard) (self : request.right = request.left)
    (sourceTop : request.left.entry.key.constraint = top)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (actual : Steps bodySteps (.edgeBody request .pure) before (.code (.pure row)) after) :
    ∃ loaded combined : Allocated,
      SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints =
        .ok (some loaded) ∧
      (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
        request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined) ∧
      SourceEqualityConjoinAllocation.readback combined = top ∧
      SourceEqualityNativeDemand.body request .pure before =
        .yielded (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined))
          {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
            request.left.children.length request.right.children.length before.operations).2} := by
  have yielded : ∃ control reached,
      SourceEqualityNativeDemand.body request .pure before = .yielded control reached := by
    cases bodySteps with
    | zero => cases (steps_zero _ _ _ _ actual).1
    | succ steps =>
        obtain ⟨control, reached, one, _tail⟩ := steps_succ steps _ _ _ _ actual
        exact ⟨control, reached, by simpa only [SourceEqualityNativeDemand.step] using one⟩
  obtain ⟨control, reached, yielded⟩ := yielded
  have arity : request.left.children.length = request.right.children.length := by rw [self]
  have loaded : ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints =
        .ok (some loaded) := by
    cases loadedCase : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint
        before.operations.constraints with
    | error message =>
        simp only [SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, loadedCase] at yielded
        cases yielded
    | ok possible =>
        cases possible with
        | none =>
            simp only [SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, loadedCase] at yielded
            cases yielded
        | some loaded => exact ⟨loaded, rfl⟩
  obtain ⟨loaded, actualLoad⟩ := loaded
  have cached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities := by
    simpa only [sourceTop] using SourceEqualityConstraintConstructors.top_cached (Formula := FullSyntax.Formula)
  have loadedFacts := SourceEqualityConstraintFieldLookup.load_ready request.left.entry.key.constraint
    before.operations.constraints valid.constraints cached loaded actualLoad
  have loadedTop : SourceEqualityConjoinAllocation.readback loaded = top := loadedFacts.2.trans sourceTop
  obtain ⟨branch, allocation, semantic, _afterValid, _growth, _ready⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le loaded loaded
      request.left.children.length request.right.children.length before.operations valid loadedFacts.1 loadedFacts.1
  have topBranch : branch.map SourceEqualityConjoinAllocation.readback = .ready top := by
    simpa only [loadedTop, self, source_top_ready] using semantic
  cases branch with
  | mismatch | rejected => cases topBranch
  | ready combined =>
      have combinedTop := SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj topBranch
      have rightLoad : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint
          before.operations.constraints = .ok (some loaded) := by rw [self]; exact actualLoad
      have one := body_ready request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        before arity loaded loaded combined actualLoad rightLoad allocation
      simp only [code_bind_pure] at one
      exact ⟨loaded, combined, actualLoad, allocation, combinedTop, one⟩

private theorem walk_child_laws
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (childLaw : Pair → Value Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (original state final : Checked width)
    (parentFuel bodySteps : Nat) (row : EdgeValue Symbol Guard)
    (finishNext : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    (entered : Steps 1 (.code (.edge request .pure)) original (.edgeBody request finishNext) state)
    (actual : Trace bodySteps (.edgeBody request .pure) state (.code (.pure row)) final)
    (children : ∀ used count, 0 < used → used + count ≤ parentFuel → count < parentFuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : Checked width) (value : Value Symbol Guard),
      Steps used (.code (.edge request .pure)) original
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      Physical first.native →
      Steps count (.code (requestNode request.domain pair.1 pair.2)) first (.code (.pure value)) last →
      childLaw pair value)
    (pairs : List Pair) (before : Checked width) (values : List (Value Symbol Guard))
    (after : Checked width) (count : Nat)
    (walked : SourceEqualityNativeDemandWalkExecution.Walk
      (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs before values after count)
    (bodyUsed : Nat) (next : List (Value Symbol Guard) → Code Symbol Guard (EdgeValue Symbol Guard))
    (origin : Steps bodyUsed (.edgeBody request .pure) state
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs).bind next)) before)
    (bounded : 1 + bodyUsed + count ≤ parentFuel) (physical : Physical before.native)
    (included : ∀ pair ∈ pairs, pair ∈ request.left.children.zip request.right.children) :
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap values ∧ All₂ childLaw pairs values := by
  induction walked generalizing bodyUsed next with
  | nil current =>
      exact ⟨physical, Extension.refl _, (by intro value member; cases member), .nil⟩
  | cons pair rest before middle after value values firstCount restCount called tail ih =>
      let childNext : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) := fun value =>
        (SourceRecursiveIntersectionCode.walk
          (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
          (fun values => next (value :: values))
      let lifted : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
        fun value => (childNext value).bind finishNext
      have atChild : Steps bodyUsed (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind childNext)) before := by
        simpa only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, childNext] using origin
      have appended := atChild.bind _ _ _ _ _ finishNext
      have outer := entered.trans _ _ _ _ _ _ _ _ appended
      have atOuter : Steps (1 + bodyUsed) (.code (.edge request .pure)) original
          (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) before := by
        simpa only [Control.bind, Code.bind_assoc, Code.bind, lifted] using outer
      have own := children (1 + bodyUsed) firstCount (by omega) (by omega) (by omega)
        pair (included pair List.mem_cons_self) lifted before middle value atOuter physical called
      have advanced := called.bind _ _ _ _ _ childNext
      obtain ⟨_extra, _length, _physicalPrefix, queryTail⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix atChild actual
      obtain ⟨_remaining, _count, queryBound, _physicalTail⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix advanced queryTail
      have queryPhysical := SourceCurrentHereditaryNativePhysicalSplit.unbind called childNext queryBound
      have queryChecked := SourceCurrentNativeEnterCommonOperand.checked_trace_extension queryPhysical physical
      have available := SourceCurrentNativeOpenRequestResults.node_result firstCount
        ⟨request.domain, pair.1, pair.2⟩ before middle value physical queryPhysical
      have tailOrigin : Steps (bodyUsed + firstCount) (.edgeBody request .pure) state
          (.code ((SourceRecursiveIntersectionCode.walk
            (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
            (fun values => next (value :: values)))) middle :=
        atChild.trans _ _ _ _ _ _ _ _ advanced
      have restIncluded : ∀ candidate ∈ rest, candidate ∈ request.left.children.zip request.right.children := by
        intro candidate member
        exact included candidate (List.mem_cons_of_mem _ member)
      have later := ih (bodyUsed + firstCount) (fun values => next (value :: values))
        tailOrigin (by omega) queryChecked.1 restIncluded
      refine ⟨later.1, queryChecked.2.trans later.2.1, ?_, .cons own later.2.2.2⟩
      intro selected member
      cases member with
      | head => exact later.2.1.available value available
      | tail _ member => exact later.2.2.1 selected member

/-- The actual self-Top body derives ordered child laws and its full Top row without an initial field origin. -/
theorem self_top_body_readback_of_smaller_nodes
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (childLaw : Pair → Value Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (original before after : Checked width)
    (parentFuel bodySteps : Nat) (row : EdgeValue Symbol Guard)
    (finishNext : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    (self : request.right = request.left) (sourceTop : request.left.entry.key.constraint = top)
    (physical : Physical before.native)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (entered : Steps 1 (.code (.edge request .pure)) original (.edgeBody request finishNext) before)
    (smaller : bodySteps < parentFuel)
    (plan : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough (parentFuel - 1)
      (.edgeBody request .pure) before)
    (actual : Steps bodySteps (.edgeBody request .pure) before (.code (.pure row)) after)
    (children : ∀ used count, 0 < used → used + count ≤ parentFuel → count < parentFuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : Checked width) (value : Value Symbol Guard),
      Steps used (.code (.edge request .pure)) original
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      Physical first.native →
      Steps count (.code (requestNode request.domain pair.1 pair.2)) first (.code (.pure value)) last →
      childLaw pair value) :
    All₂ childLaw (request.left.children.zip request.right.children) row.children ∧
      row.entry.key = ⟨request.left.entry.key.symbol, row.children.map Value.referenceOf, top⟩ ∧
      ∃ (loaded combined : Allocated) (values : List (Value Symbol Guard)) (middle : Checked width) (count : Nat),
        SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints =
          .ok (some loaded) ∧
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
          request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined) ∧
        SourceEqualityConjoinAllocation.readback combined = top ∧
        count + 1 ≤ bodySteps ∧ 2 + count ≤ parentFuel ∧
        SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode request.domain pair.1 pair.2)
          (request.left.children.zip request.right.children)
          {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
            request.left.children.length request.right.children.length before.operations).2} values middle count ∧
        values = row.children ∧ Physical middle.native ∧
        SourceRecursiveIntersectionKernel.Extension before.native.machine middle.native.machine ∧
        Values middle.native.machine.heap values ∧
        row = (run (makeEdge request.left.entry.key.symbol top values) middle.native.machine.heap).1 ∧
        after = {middle with native := advance middle.native {middle.native.machine with heap :=
          (run (makeEdge request.left.entry.key.symbol top values) middle.native.machine.heap).2}} := by
  have checked := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
    (parentFuel - 1) bodySteps (.edgeBody request .pure) (.code (.pure row))
    (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    before after physical plan actual (by omega)
  have physicalActual : Trace bodySteps (.edgeBody request .pure) before (.code (.pure row)) after := checked.1
  obtain ⟨loaded, combined, actualLoad, allocation, combinedTop, one⟩ :=
    ready_of_raw_trace request before after bodySteps row self sourceTop valid actual
  have arity : request.left.children.length = request.right.children.length := by rw [self]
  have rightLoad : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint
      before.operations.constraints = .ok (some loaded) := by rw [self]; exact actualLoad
  obtain ⟨values, middle, count, countBound, walked, resultEq, afterEq⟩ :=
    SourceEqualityNativeDemandAcceptedReadback.body_observation request before after loaded loaded combined
      (bodySteps + 1) row arity actualLoad rightLoad allocation (trace_done bodySteps _ before after row actual)
  let next : List (Value Symbol Guard) → Code Symbol Guard (EdgeValue Symbol Guard) := fun values =>
    .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure
  have origin : Steps 1 (.edgeBody request .pure) before
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)).bind next))
      {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
        request.left.children.length request.right.children.length before.operations).2} :=
    .cons _ _ _ _ _ _ _ one (.refl _ _)
  have observed := walk_child_laws childLaw request original before after parentFuel bodySteps row finishNext
    entered physicalActual children (request.left.children.zip request.right.children)
    {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
      request.left.children.length request.right.children.length before.operations).2} values middle count walked
    1 next origin (by omega) physical (by intro pair member; exact member)
  have fields := InternedGuardedExecutionLists.makeEdge_fields request.left.entry.key.symbol top values
    middle.native.machine.heap observed.1.machine.1.coherent observed.1.machine.1.cached observed.2.2.1
  have topResult : row = (run (makeEdge request.left.entry.key.symbol top values) middle.native.machine.heap).1 := by
    simpa only [combinedTop] using resultEq
  have topAfter : after = {middle with native := advance middle.native {middle.native.machine with heap :=
      (run (makeEdge request.left.entry.key.symbol top values) middle.native.machine.heap).2}} := by
    simpa only [combinedTop] using afterEq
  have childrenEq : row.children = values := by rw [topResult]; exact fields.2
  refine ⟨?_, ?_, loaded, combined, values, middle, count, actualLoad, allocation, combinedTop,
    by omega, by omega, walked, childrenEq.symm, observed.1, observed.2.1,
    observed.2.2.1, topResult, topAfter⟩
  · rw [childrenEq]
    exact observed.2.2.2
  · rw [childrenEq, topResult]
    exact fields.1

end MicroCFTA.SourceCurrentAllocatedNativeTopRowBodyReadback
