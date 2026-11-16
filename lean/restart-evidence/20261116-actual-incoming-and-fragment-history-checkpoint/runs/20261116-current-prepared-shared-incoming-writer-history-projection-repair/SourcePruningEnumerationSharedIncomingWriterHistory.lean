import MicroCFTA.SourcePruningEnumerationSharedIncomingQueryHistory
import MicroCFTA.SourceCurrentAllocatedTargetCallerCreditResources
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionOutcome
import MicroCFTA.SourceCurrentNativeEdgeWriterGrowth
import MicroCFTA.SourcePruningEnumerationRecursiveResources
import MicroCFTA.SourcePruningEnumerationOwnInputShape

namespace MicroCFTA.SourcePruningEnumerationSharedIncomingWriterHistory
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet QueryHistory)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedNativeCreditProfile (Admits)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Child" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
variable {Typing : Type} {bits : Nat}
set_option autoImplicit false

/-- Actual prepared incoming success retains past writers at its returned caller. -/
theorem prepared_incoming_success_writer_history
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (fits : Fits profile caller.checked) (admitted : Admits bits profile)
    (past : History caller.checked)
    (parentEntry : Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry rows depth free))
    (parentClosed : free = []) (edge : EdgeValue Symbol Constraint) (rowSelected : edge ∈ rows)
    (preparationHeap : InternedConstructorTemplates.State Symbol Constraint)
    (parentBucket : List Suspended) (captured own : Cached)
    (symbol : Symbol) (staged : List Child) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare preparationHeap parentBucket edge captured =
      some [((symbol, staged, residual), own)])
    (position : Nat) (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (selected : staged[position]? = some (incoming, bucket, action))
    (checkEmpty : Bool) (representativeFuel nativeFuel p h target : Nat)
    (incomingScs : List Suspended)
    (raw : List (Except EnumerationState.Error (Unit × Core)))
    (afterCaller : Caller (bits + 2)) (savedQueries : Queries) (read : Core)
    (actual : SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
      caller before.core target incoming incomingScs memos.query =
        (.ok (some raw), afterCaller, savedQueries, read)) :
    Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      History afterCaller.checked ∧
      ((afterCaller = caller ∧ QueryHistory 0 caller afterCaller) ∨
        ∃ (found : UnionFind.Result) (oldHandle : Nat) (oldScs : List Suspended)
          (old query : Node) (queried : Checked (bits + 2))
          (phase : SourcePruningEnumerationSharedEnabledEmpty.Outcome (bits + 2))
          (phaseQueries : Queries) (answer : Bool) (next : Inventory) (final : Memos),
          UnionFind.findRoot representativeFuel before.core.representatives target = some found ∧
          before.core.values[found.representative]? = some (.unenumerated (some oldHandle) oldScs) ∧
          lookupNode caller.checked.native.machine.heap oldHandle = some old ∧
          Available caller.checked.native.machine.heap old ∧ old.free = [] ∧
          SourceEqualityNativeDemand.execute nativeFuel
            (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
            caller.checked = .done query queried ∧
          History queried ∧
          QueryHistory 1 caller
            (SourceCurrentAllocatedPartialState.advance caller queried caller.fourth caller.merge) ∧
          (if checkEmpty then SourcePruningEnumerationSharedEnabledEmpty.check p h query queried caller.fourth memos.query
            else (.skipped queried caller.fourth, memos.query)) = (phase, phaseQueries) ∧
          phase.completed = some answer ∧
          afterCaller = SourceCurrentAllocatedPartialState.advance caller phase.state phase.memo caller.merge ∧
          savedQueries = phaseQueries ∧ read = {before.core with representatives := found.forest} ∧
          next.source = caller.checked.native.machine.heap ∧
          next.roots = inventory.roots ++ [incoming, old] ∧
          Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
          afterCaller.checked.native.nodes = queried.native.nodes ∧
          afterCaller.checked.native.edges = queried.native.edges ∧
          afterCaller.checked.native.machine.domains = queried.native.machine.domains ∧
          (phase = .skipped queried caller.fourth → QueryHistory 1 caller afterCaller) ∧
          (checkEmpty = false → QueryHistory 1 caller afterCaller ∧ savedQueries = memos.query)) := by
  obtain ⟨incomingAvailable, incomingClosed, observation⟩ :=
    SourcePruningEnumerationSharedIncomingQueryHistory.prepared_incoming_success_query_history
      formulas solver inventory metadata caller before memos packet parentEntry rows depth free
      parentAvailable parentClosed edge rowSelected preparationHeap parentBucket captured own
      symbol staged residual prepared position incoming bucket action selected
      checkEmpty representativeFuel nativeFuel p h target incomingScs raw afterCaller savedQueries read actual
  rcases observation with same | native
  · refine ⟨incomingAvailable, incomingClosed, ?_, .inl same⟩
    rw [same.1]
    exact past
  · obtain ⟨found, oldHandle, oldScs, old, query, queried, phase, phaseQueries, answer,
      foundEq, storedEq, lookup, oldAvailable, oldClosed, nativeDone, queryHistory,
      phaseEq, completed, callerSame, savedEq, readEq, skippedHistory, disabledHistory⟩ := native
    obtain ⟨next, source, roots, receipt, nativePost, _queryFits, _mass⟩ :=
      SourceCurrentAllocatedTargetQuery.raw_done_caller_admitted_resources profile nativeFuel
        formulas solver inventory caller queried incoming old query memos packet.context fits admitted
        incomingAvailable oldAvailable incomingClosed oldClosed nativeDone
    let queriedCaller := SourceCurrentAllocatedPartialState.advance caller queried caller.fourth caller.merge
    have queryContext : Context formulas solver next queriedCaller memos := nativePost.context
    have queriedHistory : History queried := by
      cases receipt.actual with
      | @run traceFuel trace =>
          exact past.query ⟨IntersectionEmptyDomain.emptyDomain, incoming, old⟩ traceFuel query
            packet.context.ready.good trace
    have phaseResources : ∃ final,
        Post formulas solver next queriedCaller
          (SourceCurrentAllocatedPartialState.advance caller phase.state phase.memo caller.merge) final ∧
        History phase.state ∧ final.query = phaseQueries ∧
        phase.state.native.nodes = queried.native.nodes ∧
        phase.state.native.edges = queried.native.edges ∧
        phase.state.native.machine.domains = queried.native.machine.domains := by
      cases checkEmpty with
      | false =>
          have bypass :
              (SourcePruningEnumerationSharedEnabledEmpty.Outcome.skipped queried caller.fourth,
                memos.query) = (phase, phaseQueries) := by
            simpa only [Bool.false_eq_true, ite_false] using phaseEq
          have phaseSame : phase =
              SourcePruningEnumerationSharedEnabledEmpty.Outcome.skipped queried caller.fourth :=
            (congrArg Prod.fst bypass).symm
          have queriesSame := (congrArg Prod.snd bypass).symm
          rw [phaseSame]
          exact ⟨memos, Post.refl queryContext, queriedHistory, queriesSame.symm, rfl, rfl, rfl⟩
      | true =>
          have checked : SourcePruningEnumerationSharedEnabledEmpty.check p h query queried caller.fourth
              memos.query = (phase, phaseQueries) := by
            simpa only [ite_true] using phaseEq
          cases phase with
          | skipped kept keptMemo =>
              obtain ⟨gate, keptSame, memoSame⟩ :=
                SourcePruningEnumerationSharedEnabledEmpty.check_skipped_receipt
                  p h query queried kept caller.fourth keptMemo memos.query phaseQueries checked
              have gateChecked := SourceEndpointMemoCorrect.run_checked query
                queried.native.machine.heap queryContext.ready.good.native.machine.1.coherent
                receipt.available memos.query queryContext.globals.query
              rw [gate] at gateChecked
              have gateContext : Context formulas solver next queriedCaller
                  {memos with query := phaseQueries} :=
                ⟨queryContext.ready, queryContext.admitted, queryContext.sound, queryContext.stored,
                  queryContext.covered, queryContext.correct,
                  ⟨queryContext.globals.unfolding, gateChecked.valid⟩, queryContext.probes⟩
              subst kept
              subst keptMemo
              exact ⟨{memos with query := phaseQueries}, Post.refl gateContext,
                queriedHistory, rfl, rfl, rfl, rfl⟩
          | performed observed =>
              obtain ⟨gate, called⟩ :=
                SourcePruningEnumerationSharedEnabledEmpty.check_performed_receipt
                  p h query queried caller.fourth memos.query phaseQueries observed checked
              have gateChecked := SourceEndpointMemoCorrect.run_checked query
                queried.native.machine.heap queryContext.ready.good.native.machine.1.coherent
                receipt.available memos.query queryContext.globals.query
              rw [gate] at gateChecked
              have gateContext : Context formulas solver next queriedCaller
                  {memos with query := phaseQueries} :=
                ⟨queryContext.ready, queryContext.admitted, queryContext.sound, queryContext.stored,
                  queryContext.covered, queryContext.correct,
                  ⟨queryContext.globals.unfolding, gateChecked.valid⟩, queryContext.probes⟩
              have phaseOutcome := SourceCurrentAllocatedSharedConjunctionOutcome.verified
                formulas solver p h SourceCurrentConjunctionTupleBudget.currentTupleBudget
                queriedCaller query {memos with query := phaseQueries} gateContext receipt.available
              dsimp only at phaseOutcome
              obtain ⟨final, _reads, post, _available, _unfolding, querySame, _sound⟩ := phaseOutcome
              have growth : InternedConstructorTemplates.Grows queried.native.machine.heap
                  (SourceCurrentConjunctionSharedWorker.call p h
                    SourceCurrentConjunctionTupleBudget.currentTupleBudget caller.fourth query
                    (SourceCurrentAllocatedNativeEffects.physical queried)).state.storage.requirements.physical.heap := by
                exact post.effects.keeps.growth
              have returnedHistory : History
                  (SourceCurrentAllocatedSharedConjunctionWorker.call p h
                    SourceCurrentConjunctionTupleBudget.currentTupleBudget query queried caller.fourth).state := by
                rw [SourceCurrentAllocatedSharedConjunctionWorker.call_state,
                  SourceCurrentAllocatedSharedConjunctionWorker.call_snapshot]
                exact .advance queriedHistory _ growth
              have tables := SourceCurrentAllocatedQueryMemo.advance_tables queried
                (SourceCurrentConjunctionSharedWorker.call p h
                  SourceCurrentConjunctionTupleBudget.currentTupleBudget caller.fourth query
                  (SourceCurrentAllocatedNativeEffects.physical queried)).state.storage.requirements.physical
              rw [← called]
              refine ⟨final, ?_, returnedHistory, querySame, ?_⟩
              · change Post formulas solver next queriedCaller
                  (SourceCurrentAllocatedPartialState.advance caller
                    (SourceCurrentAllocatedSharedConjunctionWorker.call p h
                      SourceCurrentConjunctionTupleBudget.currentTupleBudget query queried caller.fourth).state
                    (SourceCurrentAllocatedSharedConjunctionWorker.call p h
                      SourceCurrentConjunctionTupleBudget.currentTupleBudget query queried caller.fourth).memo
                    caller.merge) final
                rw [SourceCurrentAllocatedSharedConjunctionWorker.call_state,
                  SourceCurrentAllocatedSharedConjunctionWorker.call_memo,
                  SourceCurrentAllocatedSharedConjunctionWorker.call_snapshot]
                exact post
              · simpa only [SourcePruningEnumerationSharedEnabledEmpty.Outcome.state,
                  SourceCurrentAllocatedSharedConjunctionWorker.call_state,
                  SourceCurrentAllocatedSharedConjunctionWorker.call_snapshot] using tables
    obtain ⟨final, phasePost, phaseHistory, querySame, tables⟩ := phaseResources
    have afterHistory : History afterCaller.checked := by
      rw [callerSame]
      exact phaseHistory
    have fullPost : Post formulas solver next caller afterCaller final := by
      rw [callerSame]
      exact nativePost.trans phasePost
    have afterTables : afterCaller.checked.native.nodes = queried.native.nodes ∧
        afterCaller.checked.native.edges = queried.native.edges ∧
        afterCaller.checked.native.machine.domains = queried.native.machine.domains := by
      rw [callerSame]
      exact tables
    exact ⟨incomingAvailable, incomingClosed, afterHistory,
      .inr ⟨found, oldHandle, oldScs, old, query, queried, phase, phaseQueries, answer, next, final,
        foundEq, storedEq, lookup, oldAvailable, oldClosed, nativeDone, queriedHistory, queryHistory,
        phaseEq, completed, callerSame, savedEq, readEq, source, roots, fullPost,
        querySame.trans savedEq.symm, afterTables.1, afterTables.2.1, afterTables.2.2,
        skippedHistory, disabledHistory⟩⟩

end MicroCFTA.SourcePruningEnumerationSharedIncomingWriterHistory
