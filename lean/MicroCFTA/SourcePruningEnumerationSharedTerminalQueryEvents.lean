import MicroCFTA.SourcePruningEnumerationSharedIncomingQuerySeeds
import MicroCFTA.SourcePruningEnumerationSharedTerminalAdmission
import MicroCFTA.SourcePruningEnumerationSharedTerminalScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEventResources
import MicroCFTA.SourcePruningEnumerationSharedTerminalFoldQueryEvents
import MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents

/-!
# Ordered explicit query events in the actual shared terminal operation

The fold executes before the incoming merge. The observer retains both
complete cached and raw observations. It counts explicit intersection calls.
It does not count internal calls in the enabled empty worker.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedDispatchQueryEvents (Event)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Waiting" => EnumerationWaitingIndex.Waiting
local notation "Raw" => List (Except Error (Unit × Core))
local notation "PrefixRaw" => List (Except Error ((List Nat × Nat × Waiting) × Core))
local notation "TerminalRaw" => List (Except Error (Fragments.Fragment Symbol × Core))
variable {width : Nat}
local notation "Fault" => SourceEqualityNativeDemand.Outcome width Node ⊕ SourcePruningEnumerationSharedEnabledEmpty.Outcome width
local notation "Incoming" => Except Fault (Option Raw) × Caller width × Queries × Core
local notation "Terminal" => Except (PrefixRaw ⊕ (Fault ⊕ Raw)) (Option TerminalRaw) × Caller width × Queries × Core × Waiting
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private noncomputable def incomingObserved
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (cache : Option Cached) (caller : Caller width) (before : Core) (target : Nat)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    (Incoming × Option Cached) × List (Event width) :=
  let observed := SourcePruningEnumerationSharedIncomingQueryEvents.observe
    checkEmpty representativeFuel nativeFuel p h caller before target incoming incomingScs queries
  ((observed.1, match cache with
    | none => none
    | some recovered =>
        match observed.1 with
        | (.ok (some raw), reached, _, read) =>
            SourcePruningEnumerationIncomingCacheAdapter.adapt reached.checked.native.machine.heap
              indexFuel target incomingScs (EnumerationExpandableIndex.frame before recovered) read raw
        | _ => none), observed.2)

/-- Retain every original terminal result and its ordered explicit query events. -/
noncomputable def runObserved
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    (Terminal × Option Cached) × List (Event width) :=
  if incoming = .empty then
    (((.ok (some []), caller, queries, before.core, before.waiting), some before), [])
  else
    match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run representativeFuel first rest before.waiting before.core) with
    | [.ok ((recorded, winner, moved), joined)] =>
        let fold := SourcePruningEnumerationSharedTerminalFoldQueryEvents.foldObserved
          checkEmpty nativeFuel p h recorded caller ⟨joined, before.expandable, moved⟩ winner queries
        match fold.1 with
        | ((.error fault, reached, saved, outer), _) =>
            (((.error (.inr (.inl fault)), reached, saved, outer, moved), none), fold.2)
        | ((.ok none, reached, saved, outer), _) =>
            (((.ok none, reached, saved, outer, moved), none), fold.2)
        | ((.ok (some raw), reached, saved, outer), cache) =>
            match raw with
            | [] => (((.ok (some []), reached, saved, outer, moved), cache), fold.2)
            | [.ok ((), folded)] =>
                let merged := incomingObserved checkEmpty representativeFuel nativeFuel p h indexFuel
                  cache reached folded winner incoming incomingScs saved
                match merged.1 with
                | ((.error fault, last, finalQueries, read), _) =>
                    (((.error (.inr (.inl fault)), last, finalQueries, read, moved), none), fold.2 ++ merged.2)
                | ((.ok none, last, finalQueries, read), _) =>
                    (((.ok none, last, finalQueries, read, moved), none), fold.2 ++ merged.2)
                | ((.ok (some rows), last, finalQueries, read), finalCache) =>
                    (((.ok (some (rows.map fun row => match row with
                      | .error fault => .error fault
                      | .ok result => .ok (.hole winner, result.2))), last, finalQueries, read, moved), finalCache), fold.2 ++ merged.2)
            | stopped => (((.error (.inr (.inr stopped)), reached, saved, outer, moved), none), fold.2)
    | stopped => (((.error (.inl stopped), caller, queries, before.core, before.waiting), none), [])

omit [DecidableEq Node] in
private def ValidLog (nativeFuel : Nat) (events : List (Event width)) : Prop :=
  ∀ start saved left right actual, (start, saved, left, right, actual) ∈ events →
    actual = SourceEqualityNativeDemand.execute nativeFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked

omit [DecidableEq Node] in
private theorem append_valid {nativeFuel : Nat} {first second : List (Event width)}
    (left : ValidLog nativeFuel first) (right : ValidLog nativeFuel second) :
    ValidLog nativeFuel (first ++ second) := by
  intro start saved lhs rhs actual member
  rcases List.mem_append.mp member with member | member
  · exact left start saved lhs rhs actual member
  · exact right start saved lhs rhs actual member

private theorem incoming_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (cache : Option Cached) (caller : Caller width) (before : Core) (target : Nat)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := incomingObserved checkEmpty representativeFuel nativeFuel p h indexFuel cache caller before target incoming incomingScs queries
    observed.1 = (match cache with
      | none => (SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h caller before target incoming incomingScs queries, none)
      | some recovered => SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter checkEmpty representativeFuel nativeFuel p h indexFuel
          caller (EnumerationExpandableIndex.frame before recovered) target incoming incomingScs queries) ∧
    observed.2.length ≤ 1 ∧ ValidLog nativeFuel observed.2 := by
  dsimp only
  cases entry : SourcePruningEnumerationSharedIncomingQueryEvents.observe checkEmpty representativeFuel nativeFuel p h caller before target incoming incomingScs queries with
  | mk observation events =>
      rcases observation with ⟨outcome, reached, saved, read⟩
      have checked := SourcePruningEnumerationSharedIncomingQueryEvents.observe_exact checkEmpty representativeFuel nativeFuel p h caller before target incoming incomingScs queries
      simp only [entry] at checked
      rcases checked with ⟨same, small, _literal, meanings⟩
      have valid : ValidLog nativeFuel events := fun start saved left right actual member => (meanings start saved left right actual member).2.2.2
      cases cache with
      | none =>
          simp only [incomingObserved, entry, ← same]
          exact ⟨True.intro, small, valid⟩
      | some recovered =>
          cases outcome with
          | error fault =>
              simp only [incomingObserved, entry, SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter, EnumerationExpandableIndex.frame, ← same]
              exact ⟨True.intro, small, valid⟩
          | ok returned =>
              cases returned with
              | none =>
                  simp only [incomingObserved, entry, SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter, EnumerationExpandableIndex.frame, ← same]
                  exact ⟨True.intro, small, valid⟩
              | some raw =>
                  simp only [incomingObserved, entry, SourcePruningEnumerationSharedCachedTerminal.incomingCacheAdapter, EnumerationExpandableIndex.frame, ← same]
                  exact ⟨True.intro, small, valid⟩

private theorem run_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := runObserved checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.run checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries ∧
    observed.2.length ≤ (match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run representativeFuel first rest before.waiting before.core) with
      | [.ok ((recorded, _, _), _)] => recorded.length + 1
      | _ => 1) ∧ ValidLog nativeFuel observed.2 := by
  dsimp only
  by_cases empty : incoming = .empty
  · simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_left empty]
    refine ⟨True.intro, Nat.zero_le _, ?_⟩
    intro start saved left right actual member
    exact False.elim (List.not_mem_nil member)
  · cases prefixEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run representativeFuel first rest before.waiting before.core) with
    | nil =>
        simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq]
        refine ⟨True.intro, Nat.zero_le _, ?_⟩
        intro start saved left right actual member
        exact False.elim (List.not_mem_nil member)
    | cons firstRow prefixTail =>
        cases firstRow with
        | error fault =>
            simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq]
            refine ⟨True.intro, Nat.zero_le _, ?_⟩
            intro start saved left right actual member
            exact False.elim (List.not_mem_nil member)
        | ok value =>
            rcases value with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases prefixTail with
            | cons next remaining =>
                simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq]
                refine ⟨True.intro, Nat.zero_le _, ?_⟩
                intro start saved left right actual member
                exact False.elim (List.not_mem_nil member)
            | nil =>
                cases scan : SourcePruningEnumerationSharedTerminalFoldQueryEvents.foldObserved checkEmpty nativeFuel p h recorded caller ⟨joined, before.expandable, moved⟩ winner queries with
                | mk observation events =>
                    rcases observation with ⟨⟨outcome, reached, saved, outer⟩, cache⟩
                    have checked := SourcePruningEnumerationSharedTerminalFoldQueryEvents.fold_observe_exact checkEmpty nativeFuel p h recorded caller ⟨joined, before.expandable, moved⟩ winner queries
                    simp only [scan] at checked
                    rcases checked with ⟨same, small, meanings⟩
                    have valid : ValidLog nativeFuel events := meanings
                    have stopped : events.length ≤ recorded.length + 1 := Nat.le_trans small (Nat.le_succ _)
                    cases outcome with
                    | error fault =>
                        simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq, scan, ← same]
                        exact ⟨True.intro, stopped, valid⟩
                    | ok returned =>
                        cases returned with
                        | none =>
                            simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq, scan, ← same]
                            exact ⟨True.intro, stopped, valid⟩
                        | some raw =>
                            cases raw with
                            | nil =>
                                simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq, scan, ← same]
                                exact ⟨True.intro, stopped, valid⟩
                            | cons firstRaw rawTail =>
                                cases firstRaw with
                                | error fault =>
                                    simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq, scan, ← same]
                                    exact ⟨True.intro, stopped, valid⟩
                                | ok result =>
                                    rcases result with ⟨returnedUnit, folded⟩
                                    cases returnedUnit
                                    cases rawTail with
                                    | cons next remaining =>
                                        simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq, scan, ← same]
                                        exact ⟨True.intro, stopped, valid⟩
                                    | nil =>
                                        cases mergedEq : incomingObserved checkEmpty representativeFuel nativeFuel p h indexFuel cache reached folded winner incoming incomingScs saved with
                                        | mk observation tailEvents =>
                                            rcases observation with ⟨⟨outcome, last, finalQueries, read⟩, finalCache⟩
                                            have checked := incoming_exact checkEmpty representativeFuel nativeFuel p h indexFuel cache reached folded winner incoming incomingScs saved
                                            simp only [mergedEq] at checked
                                            rcases checked with ⟨mergedSame, tailSmall, tailValid⟩
                                            have total : (events ++ tailEvents).length ≤ recorded.length + 1 := by
                                              rw [List.length_append]
                                              omega
                                            have allValid := append_valid valid tailValid
                                            let finalize : Incoming × Option Cached → Terminal × Option Cached := fun merged =>
                                              match merged.1.1 with
                                              | .error fault =>
                                                  ((.error (.inr (.inl fault)), merged.1.2.1, merged.1.2.2.1, merged.1.2.2.2, moved), none)
                                              | .ok none =>
                                                  ((.ok none, merged.1.2.1, merged.1.2.2.1, merged.1.2.2.2, moved), none)
                                              | .ok (some rows) =>
                                                  ((.ok (some (rows.map fun row => match row with
                                                    | .error fault => .error fault
                                                    | .ok result => .ok (.hole winner, result.2))), merged.1.2.1, merged.1.2.2.1, merged.1.2.2.2, moved), merged.2)
                                            have finishedSame := congrArg finalize mergedSame
                                            cases outcome with
                                            | error fault =>
                                                simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq, scan, ← same, mergedEq]
                                                exact ⟨finishedSame, total, allValid⟩
                                            | ok returned =>
                                                cases returned with
                                                | none =>
                                                    simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq, scan, ← same, mergedEq]
                                                    exact ⟨finishedSame, total, allValid⟩
                                                | some rows =>
                                                    simp only [runObserved, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_right empty, prefixEq, scan, ← same, mergedEq]
                                                    exact ⟨finishedSame, total, allValid⟩

/-- The complete cached and raw results retain the same ordered actual calls. -/
theorem run_observe_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := runObserved checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.run
      checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries ∧
    observed.1.1 = SourcePruningEnumerationSharedCachedTerminal.raw
      checkEmpty representativeFuel nativeFuel p h first rest before.waiting caller before.core incoming incomingScs queries ∧
    observed.2.length ≤ (match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      representativeFuel first rest before.waiting before.core) with
      | [.ok ((recorded, _, _), _)] => recorded.length + 1
      | _ => 1) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by
  dsimp only
  obtain ⟨same, small, valid⟩ := run_exact checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries
  refine ⟨same, ?_, small, valid⟩
  rw [same]
  exact SourcePruningEnumerationSharedCachedTerminal.erase checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries

end MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents

namespace MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents
open EnumerationState EnumerationCorrectness EnumerationCompleteness
open EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Resources before every actual terminal query]
The terminal observer keeps each query event before it inspects that outcome.
The literal prefix supplies the joined pending slots for the fold.
An actual singleton fold supplies the current input of the incoming merge.
Successful-bound uniqueness identifies that same caller, Core and memo state.
No final terminal output supplies facts about an earlier query input.
The source schedule counts every fold source and the final incoming call.
-/

private theorem actual_singleton_fold_inputs
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : Core) (sources : List Nat)
    (checkEmpty : Bool) (nativeFuel p h target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : PendingAt before target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before source)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed sources.length)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (reached : Caller (bits + 2)) (saved : Queries) (folded outer : Core)
    (observed : SourcePruningEnumerationSharedCachedTerminal.rawFold
      checkEmpty nativeFuel p h sources beforeCaller before target memos.query =
        (.ok (some [.ok ((), folded)]), reached, saved, outer)) :
    ∃ next final, Post formulas solver next beforeCaller reached final ∧ final.query = saved ∧
      PendingRealized reached.checked.native.machine.heap folded ∧
      Fits (advance seed sources.length).2 reached.checked ∧
      Heap (fun guard => guard ∈ (advance seed sources.length).1)
        reached.checked.native.machine.heap
 := by
  have ranges := SourcePruningEnumerationSharedCachedTerminal.initial_ranges
    seed formulas solver inventory beforeCaller before sources checkEmpty target memos
    initial realized targetPending selected fits reserved known
  obtain ⟨fuel, lowP, lowH, raw, actualCaller, actualCore, actualQueries, final, next,
    stable, post, querySame, finalRealized, _shape, _completed, _eliminated, _length,
    _forest, _counter, _obligations, _expansion, _ancestry, _rejection⟩ :=
    SourcePruningEnumerationSharedCachedTerminal.rawFold_complete
      formulas solver inventory beforeCaller before sources checkEmpty target memos
      initial realized targetPending (fun source member => Or.symm (selected source member)) ranges
  have adequate := stable 0 lowP lowH (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at adequate
  have resources := SourcePruningEnumerationSharedCachedTerminal.rawFold_observed_resources
    seed formulas solver inventory beforeCaller before sources checkEmpty nativeFuel p h
    target memos initial realized targetPending selected fits reserved known observed
  have coreSame := SourcePruningEnumerationSharedCachedTerminal.rawFold_singleton_core
    checkEmpty nativeFuel p h sources beforeCaller before target memos.query
    folded reached saved outer observed
  subst outer
  obtain ⟨_rawSame, callerSame, queriesSame, afterSame⟩ :=
    SourcePruningEnumerationSharedCachedTerminal.rawFold_ok_unique checkEmpty adequate observed
  subst actualCaller
  subst actualCore
  exact ⟨next, final, post, querySame.trans queriesSame, finalRealized,
    resources.1, resources.2⟩

theorem run_observe_query_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (first : Suspended) (rest : List Suspended)
    (incoming : Node) (incomingScs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming)
    (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed ((first :: rest).length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (representativeFuel nativeFuel p h indexFuel : Nat) :
    let observed := runObserved checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest beforeCaller before incoming incomingScs memos.query
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.run
      checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest beforeCaller before incoming incomingScs memos.query ∧
    observed.1.1 = SourcePruningEnumerationSharedCachedTerminal.raw
      checkEmpty representativeFuel nativeFuel p h first rest before.waiting
      beforeCaller before.core incoming incomingScs memos.query ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      ∃ consumed : Nat, consumed < (first :: rest).length + 1 ∧
        SourceCurrentConjunctionClassScan.Ready start.checked ∧
        Fits (advance seed consumed).2 start.checked ∧
        SourceCurrentAllocatedNativeCreditProfile.Admits bits (advance seed consumed).2 ∧
        Available start.checked.native.machine.heap left ∧
        Available start.checked.native.machine.heap right ∧
        left.free = [] ∧ right.free = [] ∧
        actual = SourceEqualityNativeDemand.execute nativeFuel
          (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
          start.checked
 := by
  dsimp only
  have literal := run_observe_exact checkEmpty representativeFuel nativeFuel p h indexFuel
    first rest beforeCaller before incoming incomingScs memos.query
  refine ⟨literal.1, literal.2.1, ?_⟩
  intro start saved left right actual member
  by_cases empty : incoming = .empty
  · simp only [runObserved, ite_eq_left empty, List.not_mem_nil] at member
  · cases prefixEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) with
    | nil =>
        simp only [runObserved, ite_eq_right empty, prefixEq, List.not_mem_nil] at member
    | cons firstRow prefixTail =>
        cases firstRow with
        | error fault =>
            simp only [runObserved, ite_eq_right empty, prefixEq, List.not_mem_nil] at member
        | ok value =>
            rcases value with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases prefixTail with
            | cons next remaining =>
                simp only [runObserved, ite_eq_right empty, prefixEq, List.not_mem_nil] at member
            | nil =>
                obtain ⟨recordedSame, joinedRealized, winnerPending, recordedPending⟩ :=
                  SourcePruningEnumerationSharedCachedTerminal.terminal_observed_prefix
                    beforeCaller.checked.native.machine.heap before.core first rest before.waiting
                    roots paths counts safe bounded pending realized prefixEq
                have lengthSame : recorded.length = (first :: rest).length := by
                  simp only [recordedSame, List.length_map]
                have reservation : Reserved bits seed (recorded.length + 1) := by
                  simpa only [lengthSame] using reserved
                have foldReservation : Reserved bits seed recorded.length :=
                  reservation.prefix (by omega)
                have selected : ∀ source ∈ recorded, PendingOrEliminated joined source :=
                  fun source sourceMember => .inl (recordedPending source sourceMember)
                cases scan : SourcePruningEnumerationSharedTerminalFoldQueryEvents.foldObserved
                    checkEmpty nativeFuel p h recorded beforeCaller
                    ⟨joined, before.expandable, moved⟩ winner memos.query with
                | mk observation events =>
                    rcases observation with ⟨⟨outcome, reached, queries, outer⟩, cache⟩
                    have foldFacts :=
                      SourcePruningEnumerationSharedTerminalFoldQueryEvents.fold_observe_query_resources
                        seed formulas solver inventory beforeCaller ⟨joined, before.expandable, moved⟩
                        recorded checkEmpty nativeFuel p h winner memos initial joinedRealized
                        winnerPending selected fits foldReservation known
                    rw [scan] at foldFacts
                    have foldEvents : ∀ eventCaller eventQueries lhs rhs result,
                        (eventCaller, eventQueries, lhs, rhs, result) ∈ events →
                        ∃ consumed : Nat, consumed < (first :: rest).length + 1 ∧
                          SourceCurrentConjunctionClassScan.Ready eventCaller.checked ∧
                          Fits (advance seed consumed).2 eventCaller.checked ∧
                          SourceCurrentAllocatedNativeCreditProfile.Admits bits (advance seed consumed).2 ∧
                          Available eventCaller.checked.native.machine.heap lhs ∧
                          Available eventCaller.checked.native.machine.heap rhs ∧
                          lhs.free = [] ∧ rhs.free = [] ∧
                          result = SourceEqualityNativeDemand.execute nativeFuel
                            (.code (SourceRecursiveIntersectionCode.requestNode
                              IntersectionEmptyDomain.emptyDomain lhs rhs)) eventCaller.checked := by
                      intro eventCaller eventQueries lhs rhs result eventMember
                      obtain ⟨consumed, less, resources⟩ :=
                        foldFacts.2 eventCaller eventQueries lhs rhs result eventMember
                      exact ⟨consumed, by omega, resources⟩
                    cases outcome with
                    | error fault =>
                        simp only [runObserved, ite_eq_right empty, prefixEq, scan] at member
                        exact foldEvents start saved left right actual member
                    | ok returned =>
                        cases returned with
                        | none =>
                            simp only [runObserved, ite_eq_right empty, prefixEq, scan] at member
                            exact foldEvents start saved left right actual member
                        | some raw =>
                            cases raw with
                            | nil =>
                                simp only [runObserved, ite_eq_right empty, prefixEq, scan] at member
                                exact foldEvents start saved left right actual member
                            | cons firstRaw rawTail =>
                                cases firstRaw with
                                | error fault =>
                                    simp only [runObserved, ite_eq_right empty, prefixEq, scan] at member
                                    exact foldEvents start saved left right actual member
                                | ok result =>
                                    rcases result with ⟨resultUnit, folded⟩
                                    cases resultUnit
                                    cases rawTail with
                                    | cons next remaining =>
                                        simp only [runObserved, ite_eq_right empty, prefixEq, scan] at member
                                        exact foldEvents start saved left right actual member
                                    | nil =>
                                        have rawObserved :
                                            SourcePruningEnumerationSharedCachedTerminal.rawFold
                                              checkEmpty nativeFuel p h recorded beforeCaller joined winner memos.query =
                                                (.ok (some [.ok ((), folded)]), reached, queries, outer) := by
                                          have erased := congrArg (fun observed => observed.1) foldFacts.1
                                          exact (erased.trans
                                            (SourcePruningEnumerationSharedCachedTerminal.fold_erase
                                              checkEmpty nativeFuel p h recorded beforeCaller
                                              ⟨joined, before.expandable, moved⟩ winner memos.query)).symm
                                        obtain ⟨nextInventory, final, post, querySame, finalRealized,
                                          finalFits, _finalKnown⟩ :=
                                          actual_singleton_fold_inputs seed formulas solver inventory beforeCaller
                                            joined recorded checkEmpty nativeFuel p h winner memos initial
                                            joinedRealized winnerPending selected fits foldReservation known
                                            reached queries folded outer rawObserved
                                        have remainingReservation :
                                            Reserved bits (advance seed recorded.length) 1 := reservation.after_prefix
                                        have incomingFacts :=
                                          SourcePruningEnumerationSharedIncomingQueryEvents.observe_query_resources
                                            (advance seed recorded.length) formulas solver nextInventory reached
                                            folded final post.context finalRealized finalFits remainingReservation
                                            checkEmpty representativeFuel nativeFuel p h winner incoming incomingScs
                                            (post.effects.keeps.available incoming available) closed
                                        rw [querySame] at incomingFacts
                                        cases mergedEq : incomingObserved
                                            checkEmpty representativeFuel nativeFuel p h indexFuel cache reached
                                            folded winner incoming incomingScs queries with
                                        | mk observation tailEvents =>
                                            rcases observation with ⟨⟨lastOutcome, last, finalQueries, read⟩, finalCache⟩
                                            have tailSame : tailEvents =
                                                (SourcePruningEnumerationSharedIncomingQueryEvents.observe
                                                  checkEmpty representativeFuel nativeFuel p h reached folded
                                                  winner incoming incomingScs queries).2 := by
                                              have projected := congrArg (fun observed => observed.2) mergedEq
                                              exact projected.symm
                                            have allEvents : ∀ eventCaller eventQueries lhs rhs result,
                                                (eventCaller, eventQueries, lhs, rhs, result) ∈ events ++ tailEvents →
                                                ∃ consumed : Nat, consumed < (first :: rest).length + 1 ∧
                                                  SourceCurrentConjunctionClassScan.Ready eventCaller.checked ∧
                                                  Fits (advance seed consumed).2 eventCaller.checked ∧
                                                  SourceCurrentAllocatedNativeCreditProfile.Admits bits (advance seed consumed).2 ∧
                                                  Available eventCaller.checked.native.machine.heap lhs ∧
                                                  Available eventCaller.checked.native.machine.heap rhs ∧
                                                  lhs.free = [] ∧ rhs.free = [] ∧
                                                  result = SourceEqualityNativeDemand.execute nativeFuel
                                                    (.code (SourceRecursiveIntersectionCode.requestNode
                                                      IntersectionEmptyDomain.emptyDomain lhs rhs)) eventCaller.checked := by
                                              intro eventCaller eventQueries lhs rhs result eventMember
                                              rcases List.mem_append.mp eventMember with headMember | tailMember
                                              · exact foldEvents eventCaller eventQueries lhs rhs result headMember
                                              · rw [tailSame] at tailMember
                                                have resources := incomingFacts.2
                                                  eventCaller eventQueries lhs rhs result tailMember
                                                refine ⟨recorded.length, by omega, ?_⟩
                                                exact resources.2.2.2
                                            cases lastOutcome with
                                            | error fault =>
                                                simp only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq] at member
                                                exact allEvents start saved left right actual member
                                            | ok returned =>
                                                cases returned with
                                                | none =>
                                                    simp only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq] at member
                                                    exact allEvents start saved left right actual member
                                                | some rows =>
                                                    simp only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq] at member
                                                    exact allEvents start saved left right actual member

end MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents

namespace MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents
open EnumerationState EnumerationCorrectness EnumerationCompleteness
open EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityNativeDemand (Control)
open SourceRecursiveIntersectionControl (identity)
open SourceRecursiveIntersectionCode (requestNode)
open InternedBinderProtocol (NodeKey)
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

open Cache (Interned)

/- Note [Source Seeds through the actual terminal fold and incoming merge]
The terminal prefix changes no native caller state.
The cached-fold law supplies Seeds at its literal returned caller.
The singleton fold observation supplies the same Post and current resources.
The incoming law uses that Post and the same fold result.
The cache adapter changes no native caller field or query-event position.
Each event retains its original execute fuel and every bounded Trace prefix.
-/

theorem run_original_source_observe_preserves_seeds
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (first : Suspended) (rest : List Suspended)
    (incoming : Node) (incomingScs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming)
    (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed ((first :: rest).length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (sourceGrowth : Grows sourceHeap beforeCaller.checked.native.machine.heap)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId beforeCaller.checked)
    (representativeFuel nativeFuel p h indexFuel : Nat) :
    let observed := runObserved checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest beforeCaller before incoming incomingScs memos.query
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.run
      checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest beforeCaller before incoming incomingScs memos.query ∧
    observed.1.1 = SourcePruningEnumerationSharedCachedTerminal.raw
      checkEmpty representativeFuel nativeFuel p h first rest before.waiting
      beforeCaller before.core incoming incomingScs memos.query ∧
    (Seeds sourceHeap entry body depth ordinary bodyId observed.1.1.2.1.checked ∧
      Grows sourceHeap observed.1.1.2.1.checked.native.machine.heap) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked ∧
      (Seeds sourceHeap entry body depth ordinary bodyId actual.state ∧
        Grows sourceHeap actual.state.native.machine.heap) ∧
      ∀ (count : Nat) (resume : Control Node) (after : SourceEqualityNativeDemand.State (bits + 2)),
        count ≤ nativeFuel → Trace count
          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked resume after →
        Seeds sourceHeap entry body depth ordinary bodyId after ∧
          Grows sourceHeap after.native.machine.heap
 := by
  dsimp only
  have literal := run_observe_exact checkEmpty representativeFuel nativeFuel p h indexFuel
    first rest beforeCaller before incoming incomingScs memos.query
  refine ⟨literal.1, literal.2.1, ?_⟩
  by_cases empty : incoming = .empty
  · simp only [runObserved, ite_eq_left empty]
    refine ⟨⟨pastSeeds, sourceGrowth⟩, ?_⟩
    intro start saved left right actual member
    simp only [List.not_mem_nil] at member
  · cases prefixEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) with
    | nil =>
        simp only [runObserved, ite_eq_right empty, prefixEq]
        refine ⟨⟨pastSeeds, sourceGrowth⟩, ?_⟩
        intro start saved left right actual member
        simp only [List.not_mem_nil] at member
    | cons firstRow prefixTail =>
        cases firstRow with
        | error fault =>
            simp only [runObserved, ite_eq_right empty, prefixEq]
            refine ⟨⟨pastSeeds, sourceGrowth⟩, ?_⟩
            intro start saved left right actual member
            simp only [List.not_mem_nil] at member
        | ok value =>
            rcases value with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases prefixTail with
            | cons next remaining =>
                simp only [runObserved, ite_eq_right empty, prefixEq]
                refine ⟨⟨pastSeeds, sourceGrowth⟩, ?_⟩
                intro start saved left right actual member
                simp only [List.not_mem_nil] at member
            | nil =>
                obtain ⟨recordedSame, joinedRealized, winnerPending, recordedPending⟩ :=
                  SourcePruningEnumerationSharedCachedTerminal.terminal_observed_prefix
                    beforeCaller.checked.native.machine.heap before.core first rest before.waiting
                    roots paths counts safe bounded pending realized prefixEq
                have lengthSame : recorded.length = (first :: rest).length := by
                  simp only [recordedSame, List.length_map]
                have reservation : Reserved bits seed (recorded.length + 1) := by
                  simpa only [lengthSame] using reserved
                have foldReservation : Reserved bits seed recorded.length :=
                  reservation.prefix (by omega)
                have selected : ∀ source ∈ recorded, PendingOrEliminated joined source :=
                  fun source sourceMember => .inl (recordedPending source sourceMember)
                cases scan : SourcePruningEnumerationSharedTerminalFoldQueryEvents.foldObserved
                    checkEmpty nativeFuel p h recorded beforeCaller
                    ⟨joined, before.expandable, moved⟩ winner memos.query with
                | mk observation events =>
                    rcases observation with ⟨⟨outcome, reached, queries, outer⟩, cache⟩
                    have foldSeeds :=
                      SourcePruningEnumerationSharedTerminalFoldQueryEvents.fold_original_source_observe_preserves_seeds
                        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
                        stored bodyId bodyIdentity seed formulas solver inventory beforeCaller
                        ⟨joined, before.expandable, moved⟩ recorded checkEmpty nativeFuel p h winner memos
                        initial joinedRealized winnerPending selected fits foldReservation known sourceGrowth pastSeeds
                    simp only [scan] at foldSeeds
                    cases outcome with
                    | error fault =>
                        simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldSeeds.2
                    | ok returned =>
                        cases returned with
                        | none =>
                            simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldSeeds.2
                        | some raw =>
                            cases raw with
                            | nil =>
                                simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldSeeds.2
                            | cons firstRaw rawTail =>
                                cases firstRaw with
                                | error fault =>
                                    simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldSeeds.2
                                | ok result =>
                                    rcases result with ⟨resultUnit, folded⟩
                                    cases resultUnit
                                    cases rawTail with
                                    | cons next remaining =>
                                        simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldSeeds.2
                                    | nil =>
                                        have rawObserved :
                                            SourcePruningEnumerationSharedCachedTerminal.rawFold
                                              checkEmpty nativeFuel p h recorded beforeCaller joined winner memos.query =
                                                (.ok (some [.ok ((), folded)]), reached, queries, outer) := by
                                          have erased := congrArg (fun observed => observed.1) foldSeeds.1
                                          exact (erased.trans
                                            (SourcePruningEnumerationSharedCachedTerminal.fold_erase
                                              checkEmpty nativeFuel p h recorded beforeCaller
                                              ⟨joined, before.expandable, moved⟩ winner memos.query)).symm
                                        obtain ⟨nextInventory, final, post, querySame, finalRealized,
                                          finalFits, _finalKnown⟩ :=
                                          actual_singleton_fold_inputs seed formulas solver inventory beforeCaller
                                            joined recorded checkEmpty nativeFuel p h winner memos initial
                                            joinedRealized winnerPending selected fits foldReservation known
                                            reached queries folded outer rawObserved
                                        have remainingReservation :
                                            Reserved bits (advance seed recorded.length) 1 := reservation.after_prefix
                                        have incomingSeeds :=
                                          SourcePruningEnumerationSharedIncomingQueryEvents.original_source_observe_preserves_seeds
                                            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
                                            stored bodyId bodyIdentity (advance seed recorded.length) formulas solver
                                            nextInventory reached folded final post.context finalRealized finalFits
                                            remainingReservation foldSeeds.2.1.2 foldSeeds.2.1.1
                                            checkEmpty representativeFuel nativeFuel p h winner incoming incomingScs
                                            (post.effects.keeps.available incoming available) closed
                                        rw [querySame] at incomingSeeds
                                        cases mergedEq : incomingObserved
                                            checkEmpty representativeFuel nativeFuel p h indexFuel cache reached
                                            folded winner incoming incomingScs queries with
                                        | mk observation tailEvents =>
                                            rcases observation with ⟨⟨lastOutcome, last, finalQueries, read⟩, finalCache⟩
                                            have tailSame : tailEvents =
                                                (SourcePruningEnumerationSharedIncomingQueryEvents.observe
                                                  checkEmpty representativeFuel nativeFuel p h reached folded
                                                  winner incoming incomingScs queries).2 := by
                                              have projected := congrArg (fun observed => observed.2) mergedEq
                                              exact projected.symm
                                            have callerSame :
                                                (SourcePruningEnumerationSharedIncomingQueryEvents.observe
                                                  checkEmpty representativeFuel nativeFuel p h reached folded
                                                  winner incoming incomingScs queries).1.2.1 = last := by
                                              exact congrArg (fun observed => observed.1.1.2.1) mergedEq
                                            have lastSeeds := incomingSeeds.2.1
                                            rw [callerSame] at lastSeeds
                                            have allEvents : ∀ eventCaller eventQueries lhs rhs result,
                                                (eventCaller, eventQueries, lhs, rhs, result) ∈ events ++ tailEvents →
                                                result = SourceEqualityNativeDemand.execute nativeFuel
                                                  (.code (requestNode IntersectionEmptyDomain.emptyDomain lhs rhs)) eventCaller.checked ∧
                                                (Seeds sourceHeap entry body depth ordinary bodyId result.state ∧
                                                  Grows sourceHeap result.state.native.machine.heap) ∧
                                                ∀ (count : Nat) (resume : Control Node)
                                                  (after : SourceEqualityNativeDemand.State (bits + 2)),
                                                  count ≤ nativeFuel → Trace count
                                                    (.code (requestNode IntersectionEmptyDomain.emptyDomain lhs rhs))
                                                    eventCaller.checked resume after →
                                                  Seeds sourceHeap entry body depth ordinary bodyId after ∧
                                                    Grows sourceHeap after.native.machine.heap := by
                                              intro eventCaller eventQueries lhs rhs result eventMember
                                              rcases List.mem_append.mp eventMember with fromFold | fromIncoming
                                              · exact foldSeeds.2.2 eventCaller eventQueries lhs rhs result fromFold
                                              · rw [tailSame] at fromIncoming
                                                exact (incomingSeeds.2.2
                                                  eventCaller eventQueries lhs rhs result fromIncoming).2.2.2
                                            cases lastOutcome with
                                            | error fault =>
                                                simpa only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq]
                                                  using And.intro lastSeeds allEvents
                                            | ok returned =>
                                                cases returned with
                                                | none =>
                                                    simpa only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq]
                                                      using And.intro lastSeeds allEvents
                                                | some rows =>
                                                    simpa only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq]
                                                      using And.intro lastSeeds allEvents

end MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents

namespace MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents
open EnumerationState EnumerationCorrectness EnumerationCompleteness
open EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityNativeDemand (Control)
open SourceRecursiveIntersectionControl (identity)
open SourceRecursiveIntersectionCode (requestNode)
open InternedBinderProtocol (NodeKey)
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

open Cache (Interned)

/- Note [No Mu through the actual terminal merge]
The prefix leaves the native caller unchanged.
The fold supplies inventory and growth at its actual returned caller.
The existing singleton helper recovers Post and resources for that same fold.
The incoming law uses those facts and the actual incoming observation.
Fold events precede incoming events. Every native prefix keeps its fuel.
-/

theorem run_original_source_observe_preserves_no_mu_inventory
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (sourceNoMu : ∀ (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node),
      sourceHeap.nodeRecords key ≠ some (.mu entry body depth ordinary))
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (first : Suspended) (rest : List Suspended)
    (incoming : Node) (incomingScs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming)
    (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed ((first :: rest).length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (sourceGrowth : Grows sourceHeap beforeCaller.checked.native.machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap beforeCaller.checked.native.machine.heap)
    (representativeFuel nativeFuel p h indexFuel : Nat) :
    let observed := runObserved checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest beforeCaller before incoming incomingScs memos.query
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.run
      checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest beforeCaller before incoming incomingScs memos.query ∧
    observed.1.1 = SourcePruningEnumerationSharedCachedTerminal.raw
      checkEmpty representativeFuel nativeFuel p h first rest before.waiting
      beforeCaller before.core incoming incomingScs memos.query ∧
    (InternedShallowHeap.NoNewMu sourceHeap observed.1.1.2.1.checked.native.machine.heap ∧
      Grows sourceHeap observed.1.1.2.1.checked.native.machine.heap) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked ∧
      (InternedShallowHeap.NoNewMu sourceHeap actual.state.native.machine.heap ∧
        Grows sourceHeap actual.state.native.machine.heap) ∧
      ∀ (count : Nat) (resume : Control Node) (after : SourceEqualityNativeDemand.State (bits + 2)),
        count ≤ nativeFuel → Trace count
          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked resume after →
        InternedShallowHeap.NoNewMu sourceHeap after.native.machine.heap ∧
          Grows sourceHeap after.native.machine.heap
 := by
  dsimp only
  have literal := run_observe_exact checkEmpty representativeFuel nativeFuel p h indexFuel
    first rest beforeCaller before incoming incomingScs memos.query
  refine ⟨literal.1, literal.2.1, ?_⟩
  by_cases empty : incoming = .empty
  · simp only [runObserved, ite_eq_left empty]
    refine ⟨⟨pastInventory, sourceGrowth⟩, ?_⟩
    intro start saved left right actual member
    simp only [List.not_mem_nil] at member
  · cases prefixEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) with
    | nil =>
        simp only [runObserved, ite_eq_right empty, prefixEq]
        refine ⟨⟨pastInventory, sourceGrowth⟩, ?_⟩
        intro start saved left right actual member
        simp only [List.not_mem_nil] at member
    | cons firstRow prefixTail =>
        cases firstRow with
        | error fault =>
            simp only [runObserved, ite_eq_right empty, prefixEq]
            refine ⟨⟨pastInventory, sourceGrowth⟩, ?_⟩
            intro start saved left right actual member
            simp only [List.not_mem_nil] at member
        | ok value =>
            rcases value with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases prefixTail with
            | cons next remaining =>
                simp only [runObserved, ite_eq_right empty, prefixEq]
                refine ⟨⟨pastInventory, sourceGrowth⟩, ?_⟩
                intro start saved left right actual member
                simp only [List.not_mem_nil] at member
            | nil =>
                obtain ⟨recordedSame, joinedRealized, winnerPending, recordedPending⟩ :=
                  SourcePruningEnumerationSharedCachedTerminal.terminal_observed_prefix
                    beforeCaller.checked.native.machine.heap before.core first rest before.waiting
                    roots paths counts safe bounded pending realized prefixEq
                have lengthSame : recorded.length = (first :: rest).length := by
                  simp only [recordedSame, List.length_map]
                have reservation : Reserved bits seed (recorded.length + 1) := by
                  simpa only [lengthSame] using reserved
                have foldReservation : Reserved bits seed recorded.length :=
                  reservation.prefix (by omega)
                have selected : ∀ source ∈ recorded, PendingOrEliminated joined source :=
                  fun source sourceMember => .inl (recordedPending source sourceMember)
                cases scan : SourcePruningEnumerationSharedTerminalFoldQueryEvents.foldObserved
                    checkEmpty nativeFuel p h recorded beforeCaller
                    ⟨joined, before.expandable, moved⟩ winner memos.query with
                | mk observation events =>
                    rcases observation with ⟨⟨outcome, reached, queries, outer⟩, cache⟩
                    have foldInventory :=
                      SourcePruningEnumerationSharedTerminalFoldQueryEvents.fold_original_source_observe_preserves_no_mu_inventory
                        lib query signed whole accepted rootValue sourceHeap built sourceNoMu seed formulas solver inventory beforeCaller
                        ⟨joined, before.expandable, moved⟩ recorded checkEmpty nativeFuel p h winner memos
                        initial joinedRealized winnerPending selected fits foldReservation known sourceGrowth pastInventory
                    simp only [scan] at foldInventory
                    cases outcome with
                    | error fault =>
                        simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldInventory.2
                    | ok returned =>
                        cases returned with
                        | none =>
                            simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldInventory.2
                        | some raw =>
                            cases raw with
                            | nil =>
                                simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldInventory.2
                            | cons firstRaw rawTail =>
                                cases firstRaw with
                                | error fault =>
                                    simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldInventory.2
                                | ok result =>
                                    rcases result with ⟨resultUnit, folded⟩
                                    cases resultUnit
                                    cases rawTail with
                                    | cons next remaining =>
                                        simpa only [runObserved, ite_eq_right empty, prefixEq, scan] using foldInventory.2
                                    | nil =>
                                        have rawObserved :
                                            SourcePruningEnumerationSharedCachedTerminal.rawFold
                                              checkEmpty nativeFuel p h recorded beforeCaller joined winner memos.query =
                                                (.ok (some [.ok ((), folded)]), reached, queries, outer) := by
                                          have erased := congrArg (fun observed => observed.1) foldInventory.1
                                          exact (erased.trans
                                            (SourcePruningEnumerationSharedCachedTerminal.fold_erase
                                              checkEmpty nativeFuel p h recorded beforeCaller
                                              ⟨joined, before.expandable, moved⟩ winner memos.query)).symm
                                        obtain ⟨nextInventory, final, post, querySame, finalRealized,
                                          finalFits, _finalKnown⟩ :=
                                          actual_singleton_fold_inputs seed formulas solver inventory beforeCaller
                                            joined recorded checkEmpty nativeFuel p h winner memos initial
                                            joinedRealized winnerPending selected fits foldReservation known
                                            reached queries folded outer rawObserved
                                        have remainingReservation :
                                            Reserved bits (advance seed recorded.length) 1 := reservation.after_prefix
                                        have incomingInventory :=
                                          SourcePruningEnumerationSharedIncomingQueryEvents.original_source_observe_preserves_no_mu_inventory
                                            lib query signed whole accepted rootValue sourceHeap built sourceNoMu (advance seed recorded.length) formulas solver
                                            nextInventory reached folded final post.context finalRealized finalFits
                                            remainingReservation foldInventory.2.1.2 foldInventory.2.1.1
                                            checkEmpty representativeFuel nativeFuel p h winner incoming incomingScs
                                            (post.effects.keeps.available incoming available) closed
                                        rw [querySame] at incomingInventory
                                        cases mergedEq : incomingObserved
                                            checkEmpty representativeFuel nativeFuel p h indexFuel cache reached
                                            folded winner incoming incomingScs queries with
                                        | mk observation tailEvents =>
                                            rcases observation with ⟨⟨lastOutcome, last, finalQueries, read⟩, finalCache⟩
                                            have tailSame : tailEvents =
                                                (SourcePruningEnumerationSharedIncomingQueryEvents.observe
                                                  checkEmpty representativeFuel nativeFuel p h reached folded
                                                  winner incoming incomingScs queries).2 := by
                                              have projected := congrArg (fun observed => observed.2) mergedEq
                                              exact projected.symm
                                            have callerSame :
                                                (SourcePruningEnumerationSharedIncomingQueryEvents.observe
                                                  checkEmpty representativeFuel nativeFuel p h reached folded
                                                  winner incoming incomingScs queries).1.2.1 = last := by
                                              exact congrArg (fun observed => observed.1.1.2.1) mergedEq
                                            have lastInventory := incomingInventory.2.1
                                            rw [callerSame] at lastInventory
                                            have allEvents : ∀ eventCaller eventQueries lhs rhs result,
                                                (eventCaller, eventQueries, lhs, rhs, result) ∈ events ++ tailEvents →
                                                result = SourceEqualityNativeDemand.execute nativeFuel
                                                  (.code (requestNode IntersectionEmptyDomain.emptyDomain lhs rhs)) eventCaller.checked ∧
                                                (InternedShallowHeap.NoNewMu sourceHeap result.state.native.machine.heap ∧
                                                  Grows sourceHeap result.state.native.machine.heap) ∧
                                                ∀ (count : Nat) (resume : Control Node)
                                                  (after : SourceEqualityNativeDemand.State (bits + 2)),
                                                  count ≤ nativeFuel → Trace count
                                                    (.code (requestNode IntersectionEmptyDomain.emptyDomain lhs rhs))
                                                    eventCaller.checked resume after →
                                                  InternedShallowHeap.NoNewMu sourceHeap after.native.machine.heap ∧
                                                    Grows sourceHeap after.native.machine.heap := by
                                              intro eventCaller eventQueries lhs rhs result eventMember
                                              rcases List.mem_append.mp eventMember with fromFold | fromIncoming
                                              · exact foldInventory.2.2 eventCaller eventQueries lhs rhs result fromFold
                                              · rw [tailSame] at fromIncoming
                                                exact (incomingInventory.2.2
                                                  eventCaller eventQueries lhs rhs result fromIncoming).2.2.2
                                            cases lastOutcome with
                                            | error fault =>
                                                simpa only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq]
                                                  using And.intro lastInventory allEvents
                                            | ok returned =>
                                                cases returned with
                                                | none =>
                                                    simpa only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq]
                                                      using And.intro lastInventory allEvents
                                                | some rows =>
                                                    simpa only [runObserved, ite_eq_right empty, prefixEq, scan, mergedEq]
                                                      using And.intro lastInventory allEvents

end MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents
