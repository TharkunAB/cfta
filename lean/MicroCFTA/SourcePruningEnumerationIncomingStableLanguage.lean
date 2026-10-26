import MicroCFTA.SourcePruningEnumerationIncomingBranchesLanguage

/-!
# Assignment meaning of an actual stable incoming observation

Compare one canonical receipt with the supplied family at common bounds.
This result does not assert uniqueness for arbitrary low-fuel successes.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- The stable actual branch list has the canonical incoming assignment meaning. -/
theorem stable_semantics
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (uv : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (storage : StorageValid before) (root : EnumerationSchedule.IsRoot before.representatives uv)
    (pending : EnumerationCompleteness.PendingAt before uv)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (bounded : ∀ sc ∈ incomingScs, sc.var < before.counter)
    (ranges : match before.values[uv]? with
      | some (.unenumerated (some oldHandle) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
          | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
              beforeCaller.checked
          | none => True
      | _ => True)
    {r n p h : Nat}
    {raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))}
    {afterCaller : Caller width} {savedQueries : Queries} {read : EnumerationState.State Symbol EnumGuard}
    (observed : ∀ extra extraNative P H, p ≤ P → h ≤ H →
      run checkEmpty (r + extra) (n + extraNative) P H beforeCaller before uv incoming incomingScs memos.query =
        (.ok (some raw), afterCaller, savedQueries, read)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      (∃ output : EnumerationState.State Symbol EnumGuard,
        Except.ok ((), output) ∈ raw ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output) ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming (assignment uv) ∧
        ∀ sc ∈ incomingScs, EnumerationState.Suspended.Holds assignment (assignment uv) sc := by
  obtain ⟨r0, n0, p0, h0, _oldNode, _oldScs, read0, after0, caller0, queries0, _final, _next,
    replacement, _handle, _reading, _frame, running, _writing, _afterSame, _stored, _afterStorage,
    _afterRealized, _post, _querySame, _unfolding, _available, _closed, _encoded, _decoded,
    _optional, _present, _logical, branches⟩ :=
      run_complete_branches formulas solver inventory beforeCaller before checkEmpty uv incoming incomingScs memos
        initial realized storage root pending available closed bounded ranges
  have canonicalObserved :
      run checkEmpty (r + r0) (n + n0) (max p p0) (max h h0)
        beforeCaller before uv incoming incomingScs memos.query =
        (.ok (some (if replacement = .empty then [] else [.ok ((), after0)])), caller0, queries0, read0) := by
    simpa only [Nat.add_comm] using
      running r n (max p p0) (max h h0) (Nat.le_max_right p p0) (Nat.le_max_right h h0)
  have actualObserved :=
    observed r0 n0 (max p p0) (max h h0) (Nat.le_max_left p p0) (Nat.le_max_left h h0)
  have same : raw = (if replacement = .empty then [] else [.ok ((), after0)]) ∧
      afterCaller = caller0 ∧ savedQueries = queries0 ∧ read = read0 := by
    simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] using
      actualObserved.symm.trans canonicalObserved
  obtain ⟨rawSame, callerSame, _queriesSame, _readSame⟩ := same
  intro ambient residualMeaning assignment
  simpa only [rawSame, callerSame] using branches ambient residualMeaning assignment

end MicroCFTA.SourcePruningEnumerationIncomingNode
