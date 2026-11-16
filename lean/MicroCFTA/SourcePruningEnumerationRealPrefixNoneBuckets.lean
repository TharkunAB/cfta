import MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
import MicroCFTA.SourcePruningEnumerationSelectedStepCompletion
import MicroCFTA.SourcePruningEnumerationActionTotal

namespace MicroCFTA.SourcePruningEnumerationRealPrefixNoneBuckets
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open SourcePruningEnumerationSharedEagerNoneBuckets
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Native" => InternedConstructorTemplates.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint
  (Node × Option (EnumerateM Symbol Constraint Unit))
local notation "Raw" α => List (Except Error (α × Core))
set_option autoImplicit false
variable {Typing Key : Type} {width : Nat}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem singleton_all (core : Core) (good : NoneBucketsEmpty core) :
    ∀ state ∈ [core], NoneBucketsEmpty state := by
  intro state member
  have same := List.mem_singleton.mp member
  subst state
  exact good

private theorem optional_raw_all {α : Type} (raw : Option (Raw α))
    (good : ∀ rows, raw = some rows → ∀ core ∈ rawCores rows, NoneBucketsEmpty core) :
    ∀ core ∈ raw.toList.flatMap rawCores, NoneBucketsEmpty core := by
  cases raw with
  | none => intro core impossible; cases impossible
  | some rows =>
      intro core member
      change core ∈ rawCores rows ++ [] at member
      rw [List.append_nil] at member
      exact good rows rfl core member

private theorem optional_cache_all (candidate : Option Cached)
    (good : ∀ after, candidate = some after → NoneBucketsEmpty after.core) :
    ∀ core ∈ candidate.toList.map (fun after => after.core), NoneBucketsEmpty core := by
  cases candidate with
  | none => intro core impossible; cases impossible
  | some after => exact singleton_all after.core (good after rfl)

private theorem stopped_all (read : Raw (UVarValue Symbol)) (checked : Option (Raw Bool))
    (readAll : ∀ core ∈ rawCores read, NoneBucketsEmpty core)
    (checkAll : ∀ rows, checked = some rows → ∀ core ∈ rawCores rows, NoneBucketsEmpty core) :
    ∀ core ∈ selectedCores (Typing := Typing) (width := width) (.stopped read checked),
      NoneBucketsEmpty core := by
  intro core member
  change core ∈ rawCores read ++ checked.toList.flatMap rawCores at member
  rcases List.mem_append.mp member with left | right
  · exact readAll core left
  · exact optional_raw_all checked checkAll core right

private theorem parked_all (checked : Core) (candidate : Option Cached)
    (raw : Option (Raw (Metadata Typing × Option Next)))
    (checkAll : NoneBucketsEmpty checked)
    (candidateAll : ∀ after, candidate = some after → NoneBucketsEmpty after.core)
    (rawAll : ∀ rows, raw = some rows → ∀ core ∈ rawCores rows, NoneBucketsEmpty core) :
    ∀ core ∈ selectedCores (width := width) (.parked checked candidate raw), NoneBucketsEmpty core := by
  intro core member
  rcases List.mem_cons.mp member with same | tail
  · subst core; exact checkAll
  · rcases List.mem_append.mp tail with left | right
    · exact optional_cache_all candidate candidateAll core left
    · exact optional_raw_all raw rawAll core right

private theorem narrowed_all (checked : Core) (prepared : Prepared) (caller : Caller width)
    (queries : Queries) (action : Option (Raw Unit)) (candidate : Option Cached)
    (right : Option (Raw (Bool × Metadata Typing))) (checkAll : NoneBucketsEmpty checked)
    (actionAll : ∀ rows, action = some rows → ∀ core ∈ rawCores rows, NoneBucketsEmpty core)
    (candidateAll : ∀ after, candidate = some after → NoneBucketsEmpty after.core)
    (rightAll : ∀ rows, right = some rows → ∀ core ∈ rawCores rows, NoneBucketsEmpty core) :
    ∀ core ∈ selectedCores (.narrowed checked prepared caller queries action candidate right none),
      NoneBucketsEmpty core := by
  intro core member
  simp only [selectedCores, Option.toList_none, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.mem_append, or_assoc] at member
  rcases member with same | left | middle | last
  · subst core; exact checkAll
  · exact optional_raw_all action actionAll core left
  · exact optional_cache_all candidate candidateAll core middle
  · exact optional_raw_all right rightAll core last

private theorem raw_all {α : Type} (program : EnumerateM Symbol Constraint α) (before : Core)
    (step : ∀ output after, Success program before output after → NoneBucketsEmpty after) :
    ∀ core ∈ rawCores (ExceptT.run (program before)), NoneBucketsEmpty core := by
  intro core member
  obtain ⟨row, selected, reached⟩ := List.mem_flatMap.mp member
  cases row with
  | error message => cases reached
  | ok pair =>
      obtain ⟨output, after⟩ := pair
      have same := List.mem_singleton.mp reached
      subst core
      exact step output after selected

private theorem pure_none {α : Type} (value result : α) (before after : Core)
    (initial : NoneBucketsEmpty before) (actual : Success (pure value) before result after) :
    NoneBucketsEmpty after :=
  none_buckets_of_values_eq before after initial (pure_frame value result before after actual).values

private theorem representative_none (fuel uv root : Nat) (before after : Core)
    (initial : NoneBucketsEmpty before) (actual : Success (representative fuel uv) before root after) :
    NoneBucketsEmpty after := by
  obtain ⟨found, _lookup, _same, rfl⟩ := (representative_success fuel uv before after root).mp actual
  exact none_buckets_of_values_eq before _ initial rfl

private theorem get_value_none (fuel uv : Nat) (before after : Core) (value : UVarValue Symbol)
    (initial : NoneBucketsEmpty before) (actual : Success (getValue fuel uv) before value after) :
    NoneBucketsEmpty after := by
  obtain ⟨found, _lookup, _stored, rfl⟩ := (getValue_success fuel uv before after value).mp actual
  exact none_buckets_of_values_eq before _ initial rfl

private theorem check_none (heap : Native) (fuel uv handle : Nat) (scs : List Suspended)
    (before after : Core) (repeated : Bool) (proper : NoneBucketsEmpty before)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) : NoneBucketsEmpty after := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before repeated after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after repeated impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        have resolvedProper := representative_none fuel uv root before resolved proper resolution
        obtain ⟨current, reading, read, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, readingSame⟩ := (EnumerationDriver.get_success resolved reading current).mp read
        subst current
        subst reading
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry root
        · rw [ite_eq_left seen] at continued
          obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          have writtenProper := some_write_none_buckets root handle [] resolved written resolvedProper writing
          exact pure_none true repeated written after writtenProper finished
        · rw [ite_eq_right seen] at continued
          exact pure_none false repeated resolved after resolvedProper continued
      · have pureObserved : Success (pure false) before repeated after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, ite_eq_right boundary] using observed
        exact pure_none false repeated before after proper pureObserved

private theorem action_none [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (oldValue value : Node) (heap afterHeap : Native)
    (operation : EnumerateM Symbol Constraint Unit) (input output : Core)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue heap = .done (value, some operation) afterHeap)
    (proper : NoneBucketsEmpty input) (successful : Success operation input () output) :
    NoneBucketsEmpty output := by
  dsimp only [SourcePruningEnumerationAction.prepare, SourcePruningEnumerationAction.prepareWithNarrow] at prepared
  all_goals try (split at prepared)
  all_goals try (split at prepared)
  all_goals try (split at prepared)
  all_goals try (split at prepared)
  all_goals cases prepared
  all_goals first
  | solve
    | dsimp only [Success, reject, ExceptT.run, ExceptT.mk,
        Membership.mem, List.instMembership] at successful
      cases successful
  | exact pure_none _ _ input output proper successful
  | exact some_write_none_buckets _ _ _ input output proper successful
  | obtain ⟨selected, intermediate, represented, stored⟩ :=
      (success_bind (representative representativeFuel uv) _ input () output).mp successful
    exact some_write_none_buckets _ _ _ intermediate output
      (representative_none representativeFuel uv selected input intermediate proper represented) stored

private theorem restart_none (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (captured : Cached) (before after : Core) (result : Metadata Typing × Option Next)
    (initial : NoneBucketsEmpty before)
    (actual : Success (SourcePruningEnumerationRestart.run stop order metadata captured) before result after) :
    NoneBucketsEmpty after := by
  unfold Success SourcePruningEnumerationRestart.run at actual
  split at actual
  · cases actual
  · have same := Except.ok.inj (List.mem_singleton.mp actual)
    have coreSame : after = before := congrArg Prod.snd same
    subst after
    exact initial

/-- Every actual real selected-prefix enum snapshot retains empty missing-domain buckets. -/
theorem real_prefix_none_buckets
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (initial : NoneBucketsEmpty before.core) :
    ∀ state ∈ selectedCores
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries),
      NoneBucketsEmpty state
 := by
  classical
  have readAll := raw_all (getValue readFuel uv) before.core
    (fun value after actual => get_value_none readFuel uv before.core after value initial actual)
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue readFuel uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    have readGood : NoneBucketsEmpty readAfter := get_value_none readFuel uv before.core readAfter
      (.unenumerated (some oldHandle) scs) initial (by rw [Success, reading]; exact List.mem_singleton_self _)
    have checkAll := raw_all
      (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        checkFuel uv oldHandle scs) readAfter
      (fun repeated after actual => check_none caller.checked.native.machine.heap
        checkFuel uv oldHandle scs readAfter after repeated readGood actual)
    by_cases fresh : ∃ checked : Core,
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)]
    · obtain ⟨checked, checking⟩ := fresh
      have checkedGood : NoneBucketsEmpty checked := check_none caller.checked.native.machine.heap
        checkFuel uv oldHandle scs readAfter checked false readGood
          (by rw [Success, checking]; exact List.mem_singleton_self _)
      cases decoded : lookupNode caller.checked.native.machine.heap oldHandle with
      | none =>
          simp only [SourcePruningEnumerationSelectedStep.runPrefix,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, decoded]
          apply stopped_all [.ok (.unenumerated (some oldHandle) scs, readAfter)]
            (some [.ok (false, checked)]) (singleton_all readAfter readGood)
          intro rows same
          cases same
          exact singleton_all checked checkedGood
      | some oldValue =>
          unfold SourcePruningEnumerationSelectedStep.runPrefix
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          simp only [reading, checking, decoded, ← SourcePruningEnumerationAction.prepare_configured_eq]
          generalize preparedEq : SourcePruningEnumerationAction.prepare holeKey fits admits metadata
            nativeFuel representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap = prepared
          cases prepared with
          | failed fault heap =>
              apply narrowed_all checked (.failed fault heap) caller queries none none none checkedGood
              all_goals intro rows impossible; cases impossible
          | done pair heap =>
              obtain ⟨value, action⟩ := pair
              cases action with
              | none =>
                  apply narrowed_all checked (.done (value, none) heap) caller queries none none none checkedGood
                  all_goals intro rows impossible; cases impossible
              | some action =>
                  dsimp only
                  generalize rawEq : ExceptT.run (action checked) = raw
                  have actionAll : ∀ core ∈ rawCores raw, NoneBucketsEmpty core := by
                    rw [← rawEq]
                    apply raw_all action checked
                    intro token after actual
                    cases token
                    exact action_none holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
                      scs oldValue value caller.checked.native.machine.heap heap action checked after
                      preparedEq checkedGood actual
                  by_cases succeeded : ∃ observed : Core, raw = [.ok ((), observed)]
                  · obtain ⟨observed, rawSame⟩ := succeeded
                    rw [rawSame]
                    dsimp only [Unit.unit]
                    have observedGood : NoneBucketsEmpty observed := actionAll observed (by rw [rawSame]; exact List.mem_singleton_self _)
                    cases encoded : encodeNode value with
                    | none =>
                        apply narrowed_all checked (.done (value, some action) heap) caller queries
                          (some [.ok ((), observed)]) none none checkedGood
                        · intro rows same; cases same; exact singleton_all observed observedGood
                        · intro rows impossible; cases impossible
                        · intro rows impossible; cases impossible
                    | some newHandle =>
                        dsimp only
                        cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel
                            uv oldHandle newHandle scs before observed with
                        | none =>
                            dsimp only
                            apply narrowed_all checked (.done (value, some action) heap) caller queries
                              (some [.ok ((), observed)]) none none checkedGood
                            · intro rows same; cases same; exact singleton_all observed observedGood
                            · intro rows impossible; cases impossible
                            · intro rows impossible; cases impossible
                        | some attached =>
                            dsimp only
                            have attachedGood : NoneBucketsEmpty attached.core := by
                              rw [SourcePruningEnumerationNarrowAdapter.adapt_core heap indexFuel
                                uv oldHandle newHandle scs before attached observed adapted]
                              exact observedGood
                            have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                graph templates callbackFuel metadata uv (.inr newHandle) attached.core) =
                                [.ok ((false, metadata), attached.core)] := by
                              rw [SourcePruningRecordTypes.recordTypes_inr]
                              rfl
                            rw [recorded]
                            apply narrowed_all checked (.done (value, some action) heap) caller queries
                              (some [.ok ((), observed)])
                              (some (EnumerationExpandableIndex.frame attached.core attached))
                              (some [.ok ((false, metadata), attached.core)]) checkedGood
                            · intro rows same; cases same; exact singleton_all observed observedGood
                            · intro after same; cases same; exact attachedGood
                            · intro rows same; cases same; exact singleton_all attached.core attachedGood
                  · split
                    · exact (succeeded ⟨_, rfl⟩).elim
                    · apply narrowed_all checked (.done (value, some action) heap) caller queries
                        (some raw) none none checkedGood
                      · intro rows same; cases same; exact actionAll
                      · intro rows impossible; cases impossible
                      · intro rows impossible; cases impossible
    · by_cases parked : ∃ checked : Core,
          ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
            checkFuel uv oldHandle scs readAfter) = [.ok (true, checked)]
      · obtain ⟨checked, checking⟩ := parked
        have checkedGood : NoneBucketsEmpty checked := check_none caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter checked true readGood
            (by rw [Success, checking]; exact List.mem_singleton_self _)
        unfold SourcePruningEnumerationSelectedStep.runPrefix
          SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        simp only [reading, checking]
        cases adapted : SourcePruningEnumerationParkedRestart.adapt
            caller.checked.native.machine.heap indexFuel uv oldHandle scs before checked with
        | none =>
            apply parked_all checked none none checkedGood
            · intro rows impossible; cases impossible
            · intro rows impossible; cases impossible
        | some attached =>
            have attachedGood : NoneBucketsEmpty attached.core := by
              rw [SourcePruningEnumerationParkedRestart.adapt_core caller.checked.native.machine.heap
                indexFuel uv oldHandle scs before attached checked adapted]
              exact checkedGood
            apply parked_all checked (some attached)
              (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata attached checked))) checkedGood
            · intro after same; cases same; exact attachedGood
            · intro rows same; cases same
              exact raw_all (SourcePruningEnumerationRestart.run stop order metadata attached) checked
                (fun result after actual => restart_none stop order metadata attached checked after result checkedGood actual)
      · have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
            stop order metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries =
              .stopped (ExceptT.run (getValue readFuel uv before.core))
                (some (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
                  caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter))) := by
          unfold SourcePruningEnumerationSelectedStep.runPrefix
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          rw [reading]
          dsimp only
          split
          · exact (parked ⟨_, by assumption⟩).elim
          · exact (fresh ⟨_, by assumption⟩).elim
          · rfl
        rw [stopped]
        apply stopped_all _ _ readAll
        intro rows same
        cases same
        exact checkAll
  · have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries =
          .stopped (ExceptT.run (getValue readFuel uv before.core)) none := by
      unfold SourcePruningEnumerationSelectedStep.runPrefix
        SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    rw [stopped]
    apply stopped_all _ _ readAll
    intro rows impossible
    cases impossible

end MicroCFTA.SourcePruningEnumerationRealPrefixNoneBuckets
