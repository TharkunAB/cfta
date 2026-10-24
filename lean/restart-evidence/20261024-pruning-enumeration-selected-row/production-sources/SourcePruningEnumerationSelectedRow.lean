import MicroCFTA.SourcePruningEnumerationCheckedArity
import MicroCFTA.SourcePruningEnumerationEdgeTraversal
import MicroCFTA.EqualityLeafProjectionPhysical

namespace MicroCFTA.SourcePruningEnumerationSelectedRow
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A selected actual normalized row retains its checked origin and supplies projected own bounds. -/
theorem selected_projected_arity [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (symbol : Symbol) (original : Constraint) (stored : SourceEqualityConstraintAllocation.Value)
    (children : List (InternedConstructorTemplates.Value Symbol Constraint))
    (before : SourceEqualityConstraintMemoAllocation.State)
    (heap current : InternedConstructorTemplates.State Symbol Constraint)
    (rows : List (InternedConstructorTemplates.EdgeValue Symbol Constraint))
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (heapReady : SourceEqualityRequiredCache.Ready heap)
    (available : SourceEqualityMkEdgeAllocation.accepted original children.length = true →
      InternedNestedProvenance.Values heap children)
    (advanced : SourceEqualityRequiredCache.Keeps
      (InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
        (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap).2 current)
    (resident : InternedNestedProvenance.Edges current rows)
    (closedRows : MergedColdReaderClosedInputs.ClosedEdges rows)
    (selected : (InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
        (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap).1 ∈
      InternedEdgeResidency.nodeEdges (InternedConstructorTemplates.run (InternedConstructorTemplates.makeNode rows) current).1) :
    let built := InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
      (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap
    let parent := InternedConstructorTemplates.run (InternedConstructorTemplates.makeNode rows) current
    let operations := SourceEqualityMkEdgeAllocation.outputState
      (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2
      (SourceEqualityMkEdgeAllocation.accepted original children.length)
    SourceEqualityMkEdgeAllocation.accepted original children.length = true ∧
    (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).1 = .ok true ∧
    SourceEqualityMkEdgeAllocation.build symbol stored original.guard children before heap =
      (.ok built.1, operations, built.2) ∧
    SourceEqualityConstraintMemoAllocation.Valid operations ∧
    SourceEqualityConstraintMemoAllocation.Grows before operations ∧
    built.1.entry.key.symbol = symbol ∧ built.1.entry.key.constraint = original ∧ built.1.children = children ∧
    InternedEdgeResidency.nodeEdges parent.1 = InternedConstructorTemplates.canonicalEdges
      (InternedConstructorTemplates.surviving rows) ∧
    built.1 ∈ rows ∧ EqualityLeafProjectionPhysical.dead built.1 = false ∧
    SourceEqualityRequiredCache.Keeps current parent.2 ∧ SourceEqualityRequiredCache.Keeps heap parent.2 ∧
    SourceEqualityRequiredCache.Ready parent.2 ∧ InternedProbeProvenance.Available parent.2 parent.1 ∧
    parent.1.free = [] ∧
    ∃ classes : EqualityNormalize.Constraints,
      SourceCompactGuards.sourceEqualities built.1.entry.key.constraint = some classes ∧
      SourcePruningEnumerationConstraint.project built.1.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive built.1.entry.key.constraint.guard).isSome
            then none else some built.1.entry.key.constraint) ∧
      (∀ trie ∈ EnumerationEquality.readClasses classes, EqualityTrie.Valid trie) ∧
      (∀ paths ∈ classes, ∀ path,
        path ∈ EqualityTrie.fromPathTrie (EnumerationEquality.classTrie paths) ↔ path ∈ paths) ∧
      ∀ start : Nat, arityAllows built.1.children.length
        (suspendedVars start (EnumerationEquality.readClasses classes)) = true := by
  let actualBuilt : InternedConstructorTemplates.EdgeValue Symbol Constraint ×
        InternedConstructorTemplates.State Symbol Constraint :=
      InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
        (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap
  let actualParent : InternedConstructorTemplates.Value Symbol Constraint ×
        InternedConstructorTemplates.State Symbol Constraint :=
      InternedConstructorTemplates.run (InternedConstructorTemplates.makeNode rows) current
  let actualOperations : SourceEqualityConstraintMemoAllocation.State :=
      SourceEqualityMkEdgeAllocation.outputState
        (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2
        (SourceEqualityMkEdgeAllocation.accepted original children.length)
  obtain ⟨checkedExact, receipt, operationsValid, operationsGrowth, checkedKept,
    _checkedResident, rowSymbol, rowGuard, rowChildren, classes, source, projected,
    validTries, pathReadback, ownArity⟩ :=
    SourcePruningEnumerationCheckedArity.checked_projected_arity symbol original stored children
      before heap cached physical storedReady valid heapReady available
  change actualBuilt.1.entry.key.constraint =
    (if SourceEqualityMkEdgeAllocation.accepted original children.length then original
      else SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) at rowGuard
  change actualBuilt.1.children =
    (if SourceEqualityMkEdgeAllocation.accepted original children.length then children else [.empty]) at rowChildren
  have normalized : InternedEdgeResidency.nodeEdges actualParent.1 =
        InternedConstructorTemplates.canonicalEdges (InternedConstructorTemplates.surviving rows) := by
    exact EqualityLeafProjectionPhysical.makeNode_edges rows current
      advanced.ready.semantic.1.normal.facts.coherent
      advanced.ready.semantic.1.normal.facts.linked resident
  obtain ⟨inputMember, live⟩ :=
    (EqualityLeafProjectionPhysical.normalized_member current
      advanced.ready.semantic.1.normal.facts.coherent rows resident actualBuilt.1).mp
        (normalized ▸ selected)
  have accepted : SourceEqualityMkEdgeAllocation.accepted original children.length = true := by
    cases keepEq : SourceEqualityMkEdgeAllocation.accepted original children.length
    case false =>
        simp only [keepEq, Bool.false_eq_true, ↓reduceIte] at rowChildren
        simp [EqualityLeafProjectionPhysical.dead, rowChildren, Value.referenceOf] at live
    case true => rfl
  simp only [accepted, ↓reduceIte] at checkedExact rowGuard rowChildren
  obtain ⟨parentKept, parentAvailable, parentClosed, _parentOrdinary⟩ :=
    SourceEqualityRequiredCache.node rows current advanced.ready resident closedRows
  exact ⟨accepted, checkedExact, receipt, operationsValid, operationsGrowth,
    rowSymbol, rowGuard, rowChildren, normalized, inputMember, live, parentKept,
    checkedKept.trans (advanced.trans parentKept), parentKept.ready, parentAvailable,
    parentClosed, classes, source, projected, validTries, pathReadback, ownArity⟩

/-- The same checked selected row runs its ordered edge preparation at the actual parent endpoint. -/
theorem prepare_selected_complete [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (symbol : Symbol) (original : Constraint) (stored : SourceEqualityConstraintAllocation.Value)
    (children : List (InternedConstructorTemplates.Value Symbol Constraint))
    (before : SourceEqualityConstraintMemoAllocation.State)
    (heap current : InternedConstructorTemplates.State Symbol Constraint)
    (rows : List (InternedConstructorTemplates.EdgeValue Symbol Constraint))
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (heapReady : SourceEqualityRequiredCache.Ready heap)
    (available : SourceEqualityMkEdgeAllocation.accepted original children.length = true →
      InternedNestedProvenance.Values heap children)
    (advanced : SourceEqualityRequiredCache.Keeps
      (InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
        (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap).2 current)
    (resident : InternedNestedProvenance.Edges current rows)
    (closedRows : MergedColdReaderClosedInputs.ClosedEdges rows)
    (selected : (InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
        (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap).1 ∈
      InternedEdgeResidency.nodeEdges (InternedConstructorTemplates.run (InternedConstructorTemplates.makeNode rows) current).1)
    (scs : List EnumerationState.Suspended)
    (enumBefore entry : EnumerationState.State Symbol Constraint)
    (realized : PendingRealized heap enumBefore)
    (frame : EnumerationCompressionFrame.Frame enumBefore entry)
    (aligned : enumBefore.counter = enumBefore.values.length)
    (allowed : arityAllows
      (InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
        (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap).1.children.length scs = true) :
    let built := InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
      (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap
    let parent := InternedConstructorTemplates.run (InternedConstructorTemplates.makeNode rows) current
    PendingRealized parent.2 entry ∧ entry.counter = entry.values.length ∧
    ∃ classes : EqualityNormalize.Constraints,
      SourcePruningEnumerationConstraint.project built.1.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive built.1.entry.key.constraint.guard).isSome
            then none else some built.1.entry.key.constraint) ∧
      let tries := EnumerationEquality.readClasses classes
      let residual := if (SourceCompactGuards.positive built.1.entry.key.constraint.guard).isSome
        then none else some built.1.entry.key.constraint
      let staged := built.1.children.zipIdx.map (fun indexed =>
        (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars entry.counter tries),
          SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
            (descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars entry.counter tries)) indexed.1))
      let stop := staged.findIdx (fun stage => stage.2.2.isNone)
      ∃ (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
        (childrenResult : Option (List (Fragments.Fragment Symbol)))
        (childrenAfter after : EnumerationState.State Symbol Constraint),
        SourcePruningEnumerationEdgeTraversal.prepare scs built.1 = some action ∧
        Success (SourcePruningEnumerationEdgeTraversal.runStaged staged)
          (suspendedState tries.length entry) childrenResult childrenAfter ∧
        Success (SourcePruningEnumerationEdgeTraversal.runStaged (staged.take stop))
          (suspendedState tries.length entry)
          (some ((List.range' (entry.counter + tries.length) stop).map
            (fun uv => (Fragments.Fragment.hole uv : Fragments.Fragment Symbol)))) childrenAfter ∧
        childrenResult = (if stop < staged.length then none else
          some ((List.range' (entry.counter + tries.length) staged.length).map
            (fun uv => (Fragments.Fragment.hole uv : Fragments.Fragment Symbol)))) ∧
        after = (match childrenResult with
          | none => childrenAfter
          | some fragments => match residual with
            | none => childrenAfter
            | some guard => {childrenAfter with obligations :=
                (guard, Fragments.Fragment.node built.1.entry.key.symbol fragments) :: childrenAfter.obligations}) ∧
        Success action entry (childrenResult.map (fun fragments =>
          Fragments.Fragment.node built.1.entry.key.symbol fragments)) after ∧
        after.counter = entry.counter + tries.length + stop ∧ after.counter = after.values.length ∧
        PendingRealized parent.2 after := by
  let selectedBuilt : InternedConstructorTemplates.EdgeValue Symbol Constraint ×
        InternedConstructorTemplates.State Symbol Constraint :=
      InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
        (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap
  let selectedParent : InternedConstructorTemplates.Value Symbol Constraint ×
        InternedConstructorTemplates.State Symbol Constraint :=
      InternedConstructorTemplates.run (InternedConstructorTemplates.makeNode rows) current
  obtain ⟨_accepted, _checked, _receipt, _operationsValid, _operationsGrowth,
    _rowSymbol, _rowGuard, _rowChildren, _normalized, _inputMember, _live,
    _parentKept, totalKept, parentReady, parentAvailable, parentClosed,
    classes, _source, projected, _validTries, _pathReadback, _ownArity⟩ :=
    selected_projected_arity symbol original stored children before heap current rows
      cached physical storedReady valid heapReady available advanced resident closedRows selected
  have entryRealized : PendingRealized selectedParent.2 entry := by
    exact realized_preserved heap selectedParent.2 enumBefore entry realized frame totalKept
  have entryAligned : entry.counter = entry.values.length := by
    rw [frame.counter, frame.values]
    exact aligned
  change InternedProbeProvenance.Available selectedParent.2 selectedParent.1 at parentAvailable
  change selectedParent.1.free = [] at parentClosed
  change selectedBuilt.1 ∈ InternedEdgeResidency.nodeEdges selectedParent.1 at selected
  refine ⟨entryRealized, entryAligned, classes, projected, ?_⟩
  cases parentEq : selectedParent.1
  case empty =>
      simp only [parentEq, InternedEdgeResidency.nodeEdges, List.not_mem_nil] at selected
  case reference name =>
      simp only [parentEq, InternedEdgeResidency.nodeEdges, List.not_mem_nil] at selected
  case node parentEntry parentRows depth free =>
      exact Eq.mp (by simp only [selectedBuilt, selectedParent, projected]; rfl)
        (SourcePruningEnumerationEdgeTraversal.prepare_complete scs selectedBuilt.1 selectedParent.2
        parentEntry parentRows depth free parentReady
        (by simpa only [parentEq] using parentAvailable)
        (by simpa only [parentEq, Value.free] using parentClosed)
        (by simpa only [parentEq, InternedEdgeResidency.nodeEdges] using selected)
        entry entryRealized entryAligned allowed)
  case union unionEntry members unionDepth unionFree =>
      simp only [parentEq, InternedEdgeResidency.nodeEdges, List.not_mem_nil] at selected
  case mu muEntry body depthShape ordinaryShape =>
      simp only [parentEq, InternedEdgeResidency.nodeEdges, List.not_mem_nil] at selected

end MicroCFTA.SourcePruningEnumerationSelectedRow
