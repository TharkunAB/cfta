import MicroCFTA.SourcePruningEnumerationPathIncomingRaw
import MicroCFTA.SourcePruningEnumerationPathFoldRaw
import MicroCFTA.SourcePruningEnumerationPathOuter

/-!
# Paths in all raw child observation rows

The property covers PrefixRaw, FoldRaw and TerminalRaw successful rows.
Existing receipt paths cover the outer state and optional cache separately.
-/
namespace MicroCFTA.SourcePruningEnumerationPathObservationRaw
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open Fragments EnumerationSemantics EnumerationProgress SourcePruningEnumerationShallowChild
open SourcePruningEnumerationPathTransport SourcePruningEnumerationPathStorage
open SourcePruningEnumerationPathSelectedRaw (RawPaths)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat} {P : EqualityTrie.Path → Prop}

/-- Every successful raw row retained inside the observation has the supplied paths. -/
def ObservationPaths (P : EqualityTrie.Path → Prop)
    (observation : SourcePruningEnumerationChildDispatch.Observation width) : Prop :=
  match observation.1 with
  | .error (.inl prefixRaw) => RawPaths P prefixRaw
  | .error (.inr (.inr foldRaw)) => RawPaths P foldRaw
  | .error (.inr (.inl _nativeFault)) => True
  | .ok (some terminalRaw) => RawPaths P terminalRaw
  | .ok none => True

private theorem shallow_paths {EnumGuard NativeGuard : Type} {P : EqualityTrie.Path → Prop}
    (scs : List Suspended) (value : Value Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol)) (fragment : Fragments.Fragment Symbol)
    (paths : StatePaths P before) (inputs : BucketPaths P scs)
    (prepared : prepareChild scs value = some action)
    (success : Success action before fragment after) : StatePaths P after := by
  cases value with
  | empty =>
      simp only [prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at success
      exact (reject_unsuccessful before after fragment success).elim
  | reference name =>
      simp only [prepareChild, reduceCtorEq] at prepared
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have writtenPaths := SourcePruningEnumerationPathStorage.setValue_paths (P := P) before.counter
          (.unenumerated (some (entry.identity + 1)) scs)
          (allocated (some (entry.identity + 1)) before) written
          (paths.allocated (some (entry.identity + 1))) inputs writing
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst after
        exact writtenPaths
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst after
        exact paths.allocated (some (entry.identity + 1))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every raw terminal observation retains paths before singleton admission. -/
theorem terminal_paths
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (paths : StatePaths P before) (inputs : BucketPaths P incomingScs) :
    ObservationPaths P (SourcePruningEnumerationTerminal.run checkEmpty r n p h first rest waiting
      caller before incoming incomingScs queries) := by
  have prefixPaths : RawPaths P (ExceptT.run
      (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before)) := by
    intro result after member
    rcases result with ⟨recorded, winner, moved⟩
    exact SourcePruningEnumerationTerminalPrefix.run_paths r first rest waiting before after
      recorded winner moved paths member
  by_cases empty : incoming = .empty
  · simp only [SourcePruningEnumerationTerminal.run, empty, ↓reduceIte, ObservationPaths]
    intro result after member
    simp at member
  · unfold SourcePruningEnumerationTerminal.run
    simp only [ite_eq_right empty]
    cases prefixEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) with
    | nil => simpa only [ObservationPaths, prefixEq] using prefixPaths
    | cons row rows =>
        cases row with
        | error error => simpa only [ObservationPaths, prefixEq] using prefixPaths
        | ok pair =>
            rcases pair with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases rows with
            | cons second rest => simpa only [ObservationPaths, prefixEq] using prefixPaths
            | nil =>
                dsimp only
                have joinedPaths : StatePaths P joined :=
                  prefixPaths (recorded, winner, moved) joined (by simp only [prefixEq, List.mem_singleton])
                have foldedPaths := SourcePruningEnumerationPathFoldRaw.fold_raw_paths
                  checkEmpty n p h recorded caller joined winner queries joinedPaths
                cases foldedEq : SourcePruningEnumerationFold.run checkEmpty n p h recorded caller joined winner queries with
                | mk foldResult endpoint =>
                    rcases endpoint with ⟨foldCaller, foldQueries, foldOuter⟩
                    rw [foldedEq] at foldedPaths
                    try rw [foldedEq]
                    dsimp only [ObservationPaths] at foldedPaths ⊢
                    cases foldResult with
                    | error fault => trivial
                    | ok maybeRaw =>
                        cases maybeRaw with
                        | none => trivial
                        | some raw =>
                            cases raw with
                            | nil => intro result after member; simp at member
                            | cons firstRow restRows =>
                                cases firstRow with
                                | error error => exact foldedPaths
                                | ok firstPair =>
                                    rcases firstPair with ⟨resultUnit, folded⟩
                                    cases resultUnit
                                    cases restRows with
                                    | cons second rest => exact foldedPaths
                                    | nil =>
                                        have current : StatePaths P folded :=
                                          foldedPaths () folded (by simp only [List.mem_singleton])
                                        have received := SourcePruningEnumerationPathIncomingRaw.run_raw_paths
                                          checkEmpty r n p h foldCaller folded winner incoming incomingScs foldQueries
                                          current inputs
                                        cases incomingEq : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                                            foldCaller folded winner incoming incomingScs foldQueries with
                                        | mk incomingResult finalEndpoint =>
                                            rcases finalEndpoint with ⟨reached, saved, read⟩
                                            rw [incomingEq] at received
                                            dsimp only [ObservationPaths] at received ⊢
                                            rw [incomingEq]
                                            cases incomingResult with
                                            | error fault => trivial
                                            | ok maybeRaw =>
                                                cases maybeRaw with
                                                | none => trivial
                                                | some incomingRaw =>
                                                    dsimp only
                                                    intro fragment after member
                                                    obtain ⟨row, rowMember, mapped⟩ := List.mem_map.mp member
                                                    cases row with
                                                    | error error => cases mapped
                                                    | ok pair =>
                                                        rcases pair with ⟨resultUnit, returned⟩
                                                        cases resultUnit
                                                        have same : (Fragments.Fragment.hole winner, returned) = (fragment, after) :=
                                                          Except.ok.inj mapped
                                                        rw [← (Prod.mk.inj same).2]
                                                        exact received () returned rowMember

/-- Every actual child observation retains paths in all its successful raw rows. -/
theorem child_paths
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs) :
    ObservationPaths P (SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs incoming
      caller before queries).1 := by
  rw [SourcePruningEnumerationChildDispatch.erase checkEmpty r n p h k scs incoming caller before queries]
  by_cases empty : incoming = .empty
  · simp only [SourcePruningEnumerationChildDispatch.observe, empty, ↓reduceIte, ObservationPaths]
    intro result after member
    simp at member
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
        cases here with
        | nil =>
            cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
            | none =>
                simp only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty, partitioned, prepared,
                  ObservationPaths]
            | some action =>
                simp only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty, partitioned, prepared,
                  ObservationPaths]
                intro fragment after member
                exact shallow_paths scs incoming before.core after action fragment paths inputs prepared member
        | cons first rest =>
            have descendantsSame : scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie) = descendants := by
              simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
            have descendantPaths : BucketPaths P descendants := by
              intro sc member path represented
              have originalMember : sc ∈ scs := by
                have filteredMember : sc ∈ scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie) := by
                  simpa only [descendantsSame] using member
                exact (List.mem_filter.mp filteredMember).1
              exact inputs sc originalMember path represented
            simpa only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty, partitioned] using
              terminal_paths checkEmpty r n p h first rest before.waiting caller before.core incoming descendants
                queries paths descendantPaths

end MicroCFTA.SourcePruningEnumerationPathObservationRaw
