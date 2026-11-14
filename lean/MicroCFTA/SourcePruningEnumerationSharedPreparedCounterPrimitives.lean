import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive

/-!
# Counter preservation by actual prefix and callback reads

These laws track only the allocation counter. They do not need total
representative paths or a native caller context. Every successful branch
uses the literal action and its actual returned enumeration state.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedCounterPrimitives
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open Language Fragments SourcePruningPartialMatch SourcePruningTemplates
attribute [local instance] FormulaExecutable.formulaDecidableEq

local instance counterMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance counterLawfulMonadList : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

section Reads
variable {Symbol Guard : Type}

private theorem pure_counter {A : Type} (value result : A) (before after : EnumerationState.State Symbol Guard)
    (actual : Success (pure value) before result after) : after.counter = before.counter := by
  exact congrArg (fun state : EnumerationState.State Symbol Guard => state.counter)
    ((success_pure value result before after).mp actual).2

private theorem representative_counter (fuel uv root : Nat) (before after : EnumerationState.State Symbol Guard)
    (actual : Success (representative fuel uv) before root after) : after.counter = before.counter := by
  obtain ⟨found, _lookup, _root, same⟩ := (representative_success fuel uv before after root).mp actual
  rw [same]

private theorem getValue_counter (fuel uv : Nat) (value : UVarValue Symbol) (before after : EnumerationState.State Symbol Guard)
    (actual : Success (getValue fuel uv) before value after) : after.counter = before.counter := by
  obtain ⟨found, _lookup, _stored, same⟩ := (getValue_success fuel uv before after value).mp actual
  rw [same]

private theorem mapM_counter {A B : Type} (action : A → EnumerateM Symbol Guard B)
    (preserves : ∀ value before after result, Success (action value) before result after →
      after.counter = before.counter)
    (values : List A) (before after : EnumerationState.State Symbol Guard) (results : List B)
    (actual : Success (values.mapM action) before results after) : after.counter = before.counter := by
  exact mapM_invariant action (fun state => state.counter = before.counter) values
    (fun value _ previous result next prior observed => (preserves value previous next result observed).trans prior)
    before after results rfl actual

private theorem expandPartial_counter (graph : Graph Symbol Guard) (fuel : Nat)
    (fragment : Fragment Symbol) (before after : EnumerationState.State Symbol Guard)
    (term : Term (PartialSymbol Symbol)) (actual : Success (expandPartial graph fuel fragment) before term after) :
    after.counter = before.counter := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term actual).elim
  | succ fuel ih =>
    cases fragment with
    | node symbol children =>
      change Success (children.mapM (expandPartial graph fuel) >>= fun terms =>
        pure (.node (.concrete symbol) terms)) before term after at actual
      obtain ⟨terms, middle, traversed, finished⟩ := (success_bind _ _ _ _ _).mp actual
      exact (pure_counter _ _ middle after finished).trans
        (mapM_counter (expandPartial graph fuel) (fun child previous next result read =>
          ih child previous next result read) children before middle terms traversed)
    | hole uv =>
      change Success (getValue (fuel + 1) uv >>= fun value => match value with
        | .enumerated stored => expandPartial graph fuel stored
        | .unenumerated (some node) [] => match graph.node node with
          | .recursive _ => pure (.node .truncated [])
          | _ => pure (.node (.hole uv) [])
        | _ => pure (.node (.hole uv) [])) before term after at actual
      obtain ⟨value, middle, reading, finished⟩ := (success_bind _ _ _ _ _).mp actual
      have first := getValue_counter (fuel + 1) uv value before middle reading
      cases value with
      | eliminated => exact (pure_counter _ _ middle after finished).trans first
      | enumerated stored => exact (ih stored middle after term finished).trans first
      | unenumerated node scs =>
        cases node with
        | none => exact (pure_counter _ _ middle after finished).trans first
        | some node =>
          cases scs with
          | cons head tail => exact (pure_counter _ _ middle after finished).trans first
          | nil =>
            cases view : graph.node node <;> simp only [view] at finished <;>
              exact (pure_counter _ _ middle after finished).trans first
end Reads

private theorem resume_counter {Guard : Type} (fuel current : Nat)
    (term : Term (PartialSymbol SourcePruningTemplates.Symbol)) (pending : Pending SourcePruningTemplates.Symbol)
    (before after : EnumerationState.State SourcePruningTemplates.Symbol Guard) (result : Option (Pending SourcePruningTemplates.Symbol))
    (actual : Success (SourcePruningResume.resume fuel current term pending) before result after) :
    after.counter = before.counter := by
  change Success (pending.mapM (fun entry => do
    let root ← representative fuel entry.2
    pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)])) >>= fun results =>
      pure ((results.mapM id : Option (List (Pending SourcePruningTemplates.Symbol))).map
        (fun pieces => pieces.flatMap id))) before result after at actual
  obtain ⟨results, middle, traversed, finished⟩ := (success_bind _ _ _ _ _).mp actual
  have step : ∀ (entry : Template.Pattern SourcePruningTemplates.Symbol × Nat)
      (previous next : EnumerationState.State SourcePruningTemplates.Symbol Guard) result,
      Success (do
        let root ← representative fuel entry.2
        pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)])) previous result next →
      next.counter = previous.counter := by
    intro entry previous next result observed
    obtain ⟨root, resolved, reading, finished⟩ := (success_bind _ _ _ _ _).mp observed
    exact (pure_counter _ _ resolved next finished).trans (representative_counter fuel entry.2 root previous resolved reading)
  exact (pure_counter _ _ middle after finished).trans (mapM_counter _ step pending before middle results traversed)

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Metadata" => SourcePruningRecordTypes.Metadata

private theorem oracle_counter (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (pending : List (Pending Symbol)) (uv : Nat) (input : Sum (Fragment Symbol) Nat)
    (before after : Core) (result : Bool × List (Pending Symbol))
    (actual : Success (SourcePruningOracle.oracle graph templates fuel pending uv input) before result after) :
    after.counter = before.counter := by
  cases input with
  | inr node => exact pure_counter _ _ before after actual
  | inl fragment =>
    unfold SourcePruningOracle.oracle at actual
    dsimp only at actual
    split at actual
    · exact pure_counter _ _ before after actual
    · split at actual
      · exact pure_counter _ _ before after actual
      · change Success (do
          let term ← expandPartial graph fuel fragment
          let resumed ← pending.mapM (SourcePruningResume.resume fuel uv term)
          pure (finishChecks resumed (startMatches templates term))) before result after at actual
        obtain ⟨term, rendered, reading, continued⟩ := (success_bind _ _ _ _ _).mp actual
        obtain ⟨resumed, middle, traversed, finished⟩ := (success_bind _ _ _ _ _).mp continued
        exact (pure_counter _ _ middle after finished).trans
          ((mapM_counter (SourcePruningResume.resume fuel uv term)
            (fun group previous next result observed => resume_counter fuel uv term group previous next result observed)
            pending rendered middle resumed traversed).trans
            (expandPartial_counter graph fuel fragment before rendered term reading))

/-- Every actual successful callback retains the allocation counter without a forest premise. -/
theorem recordTypes_counter {Typing : Type}
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol)) (fuel : Nat)
    (metadata : Metadata Typing) (uv : Nat) (input : Sum (Fragment Symbol) Nat)
    (before after : Core) (result : Bool × Metadata Typing)
    (actual : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input) before result after) :
    after.counter = before.counter := by
  unfold SourcePruningRecordTypes.recordTypes at actual
  split at actual
  · obtain ⟨observed, middle, reading, finished⟩ := (success_bind _ _ _ _ _).mp actual
    exact (pure_counter _ _ middle after finished).trans (pure_counter _ _ before middle reading)
  · obtain ⟨observed, middle, reading, finished⟩ := (success_bind _ _ _ _ _).mp actual
    exact (pure_counter _ _ middle after finished).trans
      (oracle_counter graph templates fuel metadata.pending uv input before middle observed reading)

private theorem setValue_counter (uv : Nat) (value : UVarValue Symbol) (before after : Core)
    (actual : Success (setValue uv value) before () after) : after.counter = before.counter := by
  have same := (EnumerationDriver.modify_success _ before after).mp actual
  rw [same]

/-- Every actual successful selected entry retains the allocation counter. -/
theorem entry_counter (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv : Nat)
    (before after : Core) (result : Nat × Nat × List Suspended × Node)
    (actual : Success (SourcePruningEnumerationEntry.enter heap fuel uv) before result after) :
    after.counter = before.counter := by
  unfold SourcePruningEnumerationEntry.enter at actual
  obtain ⟨value, resolved, reading, continued⟩ := (success_bind _ _ _ _ _).mp actual
  have first := getValue_counter fuel uv value before resolved reading
  cases value with
  | eliminated | enumerated _ => simp only [Success, reject, ExceptT.run, List.not_mem_nil] at continued
  | unenumerated node scs =>
    cases node with
    | none => simp only [Success, reject, ExceptT.run, List.not_mem_nil] at continued
    | some handle =>
      obtain ⟨target, captured, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
      have second := representative_counter fuel uv target resolved captured reading
      split at continued
      · exact (success_failure .unresolvedReference captured after result continued).elim
      · obtain ⟨token, updated, written, finished⟩ := (success_bind _ _ _ _ _).mp continued
        cases token
        have shape := (EnumerationDriver.modify_success _ captured updated).mp written
        have third : updated.counter = captured.counter := by rw [shape]
        exact (pure_counter _ _ updated after finished).trans (third.trans (second.trans first))

private theorem checkRepeated_counter (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel uv handle : Nat) (scs : List Suspended) (before after : Core) (result : Bool)
    (actual : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs) before result after) :
    after.counter = before.counter := by
  unfold SourcePruningEnumerationRecursion.checkRepeated at actual
  split at actual
  · exact (success_failure .unresolvedReference before after result actual).elim
  · split at actual
    · obtain ⟨root, resolved, reading, continued⟩ := (success_bind _ _ _ _ _).mp actual
      obtain ⟨current, middle, observing, continued⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨sameCurrent, sameMiddle⟩ := (EnumerationDriver.get_success resolved middle current).mp observing
      subst current
      subst middle
      have first := representative_counter fuel uv root before resolved reading
      split at continued
      · obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
        cases token
        exact (pure_counter _ _ written after finished).trans
          ((setValue_counter root (.unenumerated (some handle) []) resolved written writing).trans first)
      · exact (pure_counter _ _ resolved after continued).trans first
    · exact pure_counter _ _ before after actual

section Prefix
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem action_counter {Typing Key : Type}
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (prepared : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) (NativeGuard := Constraint) holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (before after : Core) (actual : Success action before () after) : after.counter = before.counter := by
  have all : match SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) (NativeGuard := Constraint) holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap with
    | .failed .. => True
    | .done (_, none) _ => True
    | .done (_, some selected) _ =>
        ∀ previous next, Success selected previous () next → next.counter = previous.counter := by
    unfold SourcePruningEnumerationAction.prepare
      SourcePruningEnumerationAction.prepareWithNarrow
    cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap with
    | failed fault reached => trivial
    | done result reached =>
      cases result with
      | empty =>
        intro previous next observed
        simp only [Success, reject, ExceptT.run, List.not_mem_nil] at observed
      | reference name => trivial
      | node entry rows depth free | union entry rows depth free | mu entry rows depth free =>
        dsimp only [SourcePruningEnumerationNodes.encodeNode]
        split
        · intro previous next observed
          exact pure_counter _ _ previous next observed
        · intro previous next observed
          obtain ⟨root, resolved, reading, written⟩ := (success_bind _ _ _ _ _).mp observed
          exact (setValue_counter root (.unenumerated (some _ ) scs) resolved next written).trans
            (representative_counter representativeFuel uv root previous resolved reading)
  rw [prepared] at all
  exact all before after actual

/-- Counter facts for the retained parked restart or narrowed cache. -/
def PrefixCounters {Typing : Type} (counter : Nat) :
    SourcePruningEnumerationSelectedStep.Result width Typing → Prop
  | .parked _ _ raw => ∀ updated next core,
      raw = some [.ok ((updated, next), core)] → core.counter = counter
  | .narrowed _ _ _ _ _ candidate _ _ => ∀ after,
      candidate = some after → after.core.counter = counter
  | .stopped _ _ => True

/-- Every actual prefix continuation retains its original counter without current validity assumptions. -/
theorem prefix_counter {Typing Key : Type} {width : Nat}
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : SourceEndpointMemo.Memos) :
    PrefixCounters before.core.counter (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph
      templates stop order metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel
      uv caller before queries) := by
  unfold SourcePruningEnumerationSelectedStep.runPrefix
    SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
  simp only [← SourcePruningEnumerationAction.prepare_configured_eq]
  split
  · rename_i oldHandle scs readAfter readEq
    have readCount := getValue_counter readFuel uv (.unenumerated (some oldHandle) scs) before.core readAfter
      (by simp only [Success, readEq, List.mem_singleton])
    split
    · rename_i checked checkEq
      have checkedCount := (checkRepeated_counter caller.checked.native.machine.heap checkFuel uv oldHandle scs
        readAfter checked true (by simp only [Success, checkEq, List.mem_singleton])).trans readCount
      intro updated next core recorded
      cases adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
          indexFuel uv oldHandle scs before checked with
      | none =>
        simp only [adapted, Option.map_none] at recorded
        cases recorded
      | some parked =>
        simp only [adapted, Option.map_some, Option.some.injEq] at recorded
        unfold SourcePruningEnumerationRestart.run at recorded
        split at recorded
        · cases recorded
        · have same : core = checked := (Prod.mk.inj (Except.ok.inj (List.cons.inj recorded).1)).2.symm
          exact (congrArg EnumerationState.State.counter same).trans checkedCount
    · rename_i checked checkEq
      have checkedCount := (checkRepeated_counter caller.checked.native.machine.heap checkFuel uv oldHandle scs
        readAfter checked false (by simp only [Success, checkEq, List.mem_singleton])).trans readCount
      split
      · trivial
      · rename_i oldValue decoded
        split
        · intro cached impossible; cases impossible
        · intro cached impossible; cases impossible
        · rename_i value action heap prepared
          split
          · rename_i observed actionEq
            have actionCount := (action_counter holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
              scs oldValue value caller.checked.native.machine.heap heap action prepared checked observed
              (by simp only [Success, actionEq, List.mem_singleton])).trans checkedCount
            split
            · intro cached impossible; cases impossible
            · rename_i newHandle encoded
              split
              · intro cached impossible; cases impossible
              · rename_i attached adapted
                have attachedCount := (congrArg EnumerationState.State.counter
                  (SourcePruningEnumerationNarrowAdapter.adapt_core heap indexFuel uv oldHandle newHandle scs
                    before attached observed adapted)).trans actionCount
                split
                · rename_i updated callbackCore recorded
                  intro cached same
                  have equal := Option.some.inj same
                  subst cached
                  have returned := recordTypes_counter graph templates callbackFuel metadata uv (.inr newHandle)
                    attached.core callbackCore (false, updated)
                    (by simp only [Success, recorded, List.mem_singleton])
                  exact returned.trans attachedCount
                · intro cached same
                  have equal := Option.some.inj same
                  subst cached
                  exact attachedCount
          · intro cached impossible; cases impossible
    · trivial
  · trivial
end Prefix

end MicroCFTA.SourcePruningEnumerationSharedPreparedCounterPrimitives
