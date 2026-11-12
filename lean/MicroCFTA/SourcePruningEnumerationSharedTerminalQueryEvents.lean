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
