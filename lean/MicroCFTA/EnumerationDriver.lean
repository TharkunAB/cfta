import MicroCFTA.EnumerationSchedule

/-!
# Safety of the concrete enumeration caller

The child traversal preserves the selected root before the caller writes its
completed fragment. The proof uses the source actions and scheduler scan.
-/

namespace MicroCFTA.EnumerationDriver
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
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

/-- A traversal retains one root, its stored value, and its complete class. -/
structure Protected (held : Nat) (before after : State Symbol Guard) : Prop where
  value : after.values[held]? = before.values[held]?
  root : IsRoot after.representatives held
  classes : ∀ uv, UnionFind.SameClass after.representatives held uv ↔
    UnionFind.SameClass before.representatives held uv

/-- An unchanged state retains its protected root. -/
theorem Protected.refl (held : Nat) (state : State Symbol Guard) (root : IsRoot state.representatives held) :
    Protected held state state := ⟨rfl, root, fun _ => Iff.rfl⟩

/-- Consecutive traversals retain the same protected value and class. -/
theorem Protected.trans (left : Protected held before middle) (right : Protected held middle after) :
    Protected held before after :=
  ⟨right.value.trans left.value, right.root, fun uv => (right.classes uv).trans (left.classes uv)⟩

/-- Preserving the complete class preserves all separate suspended inputs. -/
theorem Protected.avoids (frame : Protected held before after) (scs : List Suspended)
    (separate : Avoids before.representatives held scs) : Avoids after.representatives held scs := by
  intro sc member same
  exact separate sc member ((frame.classes sc.var).mp same)

/-- Allocation retains each previously allocated protected slot. -/
theorem allocation_protected (held : Nat) (node : Option Nat) (before : State Symbol Guard)
    (safe : Safe before) (inside : held < before.counter) (root : IsRoot before.representatives held) :
    Protected held before (allocated node before) := by
  have bound : held < before.values.length := by rw [← safe.1.aligned]; exact inside
  exact ⟨by simp [allocated, List.getElem?_append_left bound], root, fun _ => Iff.rfl⟩

/-- Class allocation retains the protected root through every fresh variable. -/
theorem suspension_protected (held count : Nat) (before : State Symbol Guard)
    (safe : Safe before) (inside : held < before.counter) (root : IsRoot before.representatives held) :
    Protected held before (suspendedState count before) := by
  induction count generalizing before with
  | zero => exact .refl held before root
  | succ count ih =>
      have first := allocation_protected held none before safe inside root
      exact first.trans (ih (allocated none before)
        ⟨allocation_storage none before safe.1, allocation_live none before safe.1 safe.2⟩
        (by simpa [allocated] using Nat.lt_succ_of_lt inside) first.root)

/-- Adding a residual obligation retains all values and representatives. -/
theorem recordResidual_protected (residual : Option Guard) (fragment : Fragment Symbol) (held : Nat)
    (before after : State Symbol Guard) (root : IsRoot before.representatives held)
    (success : Success (recordResidual residual fragment) before () after) : Protected held before after := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact .refl held before root
  | some guard =>
      have same : after = {before with obligations := (guard, fragment) :: before.obligations} := by
        simpa [Success, recordResidual, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
      subst after
      exact ⟨rfl, root, fun _ => Iff.rfl⟩

/-- Every actual node and edge traversal preserves a separate allocated root. -/
theorem enumeration_protected (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node held (before after : State Symbol Guard) fragment, Safe before →
      held < before.counter → IsRoot before.representatives held →
      (∀ sc ∈ scs, sc.var < before.counter) → Avoids before.representatives held scs →
      Success (enumerateNode graph fuel scs node) before fragment after → Protected held before after) ∧
    (∀ scs edge held (before after : State Symbol Guard) fragment, Safe before →
      held < before.counter → IsRoot before.representatives held →
      (∀ sc ∈ scs, sc.var < before.counter) → Avoids before.representatives held scs →
      Success (enumerateEdge graph fuel scs edge) before fragment after → Protected held before after) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node held before after fragment _ _ _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge held before after fragment _ _ _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node held before after fragment safe inside root bounded avoids success
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | alternatives edges | recursive body | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                obtain ⟨frame, rootAfter, classes, _⟩ := enumerateNode_terminal_protected graph fuel node scs first rest held
                  before after fragment (by simp [view]) terminal safe.1.total safe.2 root avoids success
                exact ⟨frame, rootAfter, classes⟩
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨_, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact ih.2 scs edge held before after fragment safe inside root bounded avoids continued)
                | (obtain ⟨uv, middle, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
                   have allocatedExact : uv = before.counter ∧ middle = allocated (some node) before := by
                     simpa [Success, allocate_exact, ExceptT.run] using allocation
                   obtain ⟨uvSame, middleSame⟩ := allocatedExact
                   subst uv
                   subst middle
                   obtain ⟨_, afterSame⟩ := (success_pure (.hole before.counter) fragment (allocated (some node) before) after).mp final
                   subst after
                   exact allocation_protected held (some node) before safe inside root)
      · intro scs edge held before after fragment safe inside root bounded avoids success
        rw [edge_action graph fuel scs edge] at success
        obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp success
        cases ignored
        obtain ⟨_, same⟩ := (require_success _ before checked).mp required
        subst checked
        obtain ⟨added, suspended, suspension, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have suspensionExact : added = suspendedVars before.counter edge.equalities ∧
            suspended = suspendedState edge.equalities.length before := by
          simpa [Success, suspendMany_exact, ExceptT.run] using suspension
        obtain ⟨addedSame, suspendedSame⟩ := suspensionExact
        subst added
        subst suspended
        let start := suspendedState edge.equalities.length before
        let inputs := scs ++ suspendedVars before.counter edge.equalities
        have startSafe : Safe start := suspension_safe edge.equalities.length before safe
        have startFrame : Protected held before start := suspension_protected held edge.equalities.length before safe inside root
        have startGrowth : before.counter ≤ start.counter := by simp [start, suspended_counter]
        have startInside : held < start.counter := Nat.lt_of_lt_of_le inside startGrowth
        have inputBound : ∀ sc ∈ inputs, sc.var < start.counter := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact Nat.lt_of_lt_of_le (bounded sc old) startGrowth
          · simpa [start, suspended_counter] using suspended_bounded before.counter edge.equalities sc fresh
        have inputAvoid : Avoids start.representatives held inputs := by
          apply startFrame.avoids
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact avoids sc old
          · exact fresh_avoids before safe.1 held inside edge.equalities sc fresh
        obtain ⟨children, expanded, traversed, continued⟩ := (success_bind _ _ _ _ _).mp continued
        let invariant := fun state : State Symbol Guard =>
          Safe state ∧ start.counter ≤ state.counter ∧ Protected held start state
        have childStep : ∀ entry ∈ edge.children.zipIdx, ∀ previous child next, invariant previous →
            Success (enumerateNode graph fuel (descendScs entry.2 inputs) entry.1) previous child next → invariant next := by
          intro entry _ previous child next valid childSuccess
          have childBound : ∀ sc ∈ descendScs entry.2 inputs, sc.var < previous.counter := by
            apply descend_bounded
            intro sc member
            exact Nat.lt_of_lt_of_le (inputBound sc member) valid.2.1
          have childAvoid := descend_avoids previous.representatives held entry.2 inputs (valid.2.2.avoids inputs inputAvoid)
          obtain ⟨nextSafe, growth, _⟩ := (enumeration_safety graph fuel).1 _ entry.1 previous next child valid.1 childBound childSuccess
          have frame := ih.1 _ entry.1 held previous next child valid.1
            (Nat.lt_of_lt_of_le startInside valid.2.1) valid.2.2.root childBound childAvoid childSuccess
          exact ⟨nextSafe, Nat.le_trans valid.2.1 growth, valid.2.2.trans frame⟩
        have expandedValid := mapM_invariant
          (fun entry => enumerateNode graph fuel (descendScs entry.2 inputs) entry.1) invariant edge.children.zipIdx childStep
          start expanded children ⟨startSafe, Nat.le_refl _, .refl held start startFrame.root⟩ traversed
        obtain ⟨ignored, guarded, residual, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have guardedFrame := recordResidual_protected edge.residual (.node edge.symbol children) held expanded guarded
          expandedValid.2.2.root residual
        obtain ⟨_, afterSame⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst after
        exact startFrame.trans (expandedValid.2.2.trans guardedFrame)

/-- Reading the state has one result and changes no field. -/
theorem get_success (before after : State Symbol Guard) (value : State Symbol Guard) :
    Success get before value after ↔ value = before ∧ after = before := by
  simp [Success, get, getThe, MonadStateOf.get, StateT.get, pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm]

/-- A state update has exactly its stated result. -/
theorem modify_success (update : State Symbol Guard → State Symbol Guard) (before after : State Symbol Guard) :
    Success (modify update) before () after ↔ after = update before := by
  simp [Success, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

/-- Path compression preserves safety and the complete protected class. -/
theorem compression_safe (before : State Symbol Guard) (safe : Safe before) (fuel uv held : Nat)
    (inside : uv < before.counter) (root : IsRoot before.representatives held) (found : UnionFind.Result)
    (lookup : UnionFind.findRoot fuel before.representatives uv = some found) :
    Safe {before with representatives := found.forest} ∧
      Protected held before {before with representatives := found.forest} := by
  have rootSame := findRoot_isRoot before.representatives safe.1.total fuel uv found lookup
  refine ⟨⟨representative_storage before safe.1 fuel uv inside found lookup, ?_⟩,
    rfl, (rootSame held).mpr root, fun other => UnionFind.findRoot_classes safe.1.total lookup held other⟩
  intro other value stored
  exact (safe.2 other value stored).trans (rootSame other).symm

/-- Looking up a known root returns its own slot and preserves its complete class. -/
theorem getValue_root (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (safe : Safe before) (inside : uv < before.counter) (root : IsRoot before.representatives uv)
    (success : Success (getValue fuel uv) before value after) :
    Safe after ∧ after.counter = before.counter ∧ Protected uv before after ∧
      after.values[uv]? = some value := by
  obtain ⟨found, lookup, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  have fixed : found.representative = uv :=
    (UnionFind.reaches_unique (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1 root.choose_spec).1
  obtain ⟨safeAfter, frame⟩ := compression_safe before safe fuel uv uv inside root found lookup
  exact ⟨safeAfter, rfl, frame, by simpa [fixed] using stored⟩

/-- A representative lookup of a root returns that same root. -/
theorem representative_root (fuel uv result : Nat) (before after : State Symbol Guard)
    (safe : Safe before) (inside : uv < before.counter) (root : IsRoot before.representatives uv)
    (success : Success (representative fuel uv) before result after) :
    result = uv ∧ Safe after ∧ after.counter = before.counter ∧ Protected uv before after := by
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after result).mp success
  have fixed : found.representative = uv :=
    (UnionFind.reaches_unique (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1 root.choose_spec).1
  obtain ⟨safeAfter, frame⟩ := compression_safe before safe fuel uv uv inside root found lookup
  exact ⟨fixed, safeAfter, rfl, frame⟩

/-- Replacing a root by another live bounded value preserves both safety invariants. -/
theorem setValue_safe (uv : Nat) (value : UVarValue Symbol) (before after : State Symbol Guard)
    (safe : Safe before) (root : IsRoot before.representatives uv)
    (live : value ≠ .eliminated) (bounded : SlotBound before.counter value)
    (success : Success (setValue uv value) before () after) : Safe after ∧ after.counter = before.counter := by
  obtain rfl := (modify_success (fun state => {state with values := state.values.set uv value}) before after).mp success
  refine ⟨⟨set_storage before safe.1 uv value bounded, ?_⟩, rfl⟩
  intro other stored read
  by_cases same : other = uv
  · subst other
    have sameValue : stored = value := by
      have bound := (List.getElem?_eq_some_iff.mp read).1
      simp only [List.length_set] at bound
      simpa [List.getElem?_set, bound] using read.symm
    subst stored
    exact ⟨fun _ => root, fun _ => live⟩
  · apply safe.2 other stored
    simpa [List.getElem?_set, same, Ne.symm same] using read

/-- Ancestry bookkeeping does not affect storage or root liveness. -/
theorem ancestry_safe (before : State Symbol Guard) (ancestry : List RecursionKey) (safe : Safe before) :
    Safe {before with expansionAncestry := ancestry} := by
  exact ⟨⟨safe.1.aligned, safe.1.total, safe.1.forest, safe.1.values, safe.1.guards⟩, safe.2⟩

/-- The final root write is safe after the actual protected child traversal. -/
theorem enumerateOut_safe (graph : Graph Symbol Guard) (fuel uv : Nat)
    (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (safe : Safe before) (inside : uv < before.counter) (root : IsRoot before.representatives uv)
    (avoids : ∀ node scs, before.values[uv]? = some (.unenumerated (some node) scs) →
      Avoids before.representatives uv scs)
    (success : Success (enumerateOut graph fuel uv) before fragment after) :
    Safe after ∧ before.counter ≤ after.counter ∧ FragmentBound after.counter fragment := by
  unfold enumerateOut at success
  obtain ⟨value, readState, read, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readSafe, readCounter, readFrame, stored⟩ := getValue_root (fuel + 1) uv before readState value safe inside root read
  cases value with
  | eliminated | enumerated _ => exact (reject_unsuccessful readState after fragment continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful readState after fragment continued).elim
      | some node =>
          obtain ⟨selected, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨selectedSame, resolvedSafe, resolvedCounter, resolvedFrame⟩ := representative_root (fuel + 1) uv selected
            readState resolved readSafe (by simpa [readCounter] using inside) readFrame.root resolution
          subst selected
          obtain ⟨current, currentState, currentRead, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨currentSame, currentStateSame⟩ := (get_success resolved currentState current).mp currentRead
          subst current
          subst currentState
          obtain ⟨ignored, started, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ resolved started).mp bookkeeping
          obtain ⟨produced, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have oldStored : before.values[uv]? = some (.unenumerated (some node) scs) := readFrame.value ▸ stored
          have bounded : ∀ sc ∈ scs, sc.var < resolved.counter := by
            have bounds := safe.1.values _ (List.mem_of_getElem? oldStored)
            simpa [resolvedCounter, readCounter, SlotBound] using bounds
          have frame := readFrame.trans resolvedFrame
          have separate := frame.avoids scs (avoids node scs oldStored)
          let ancestry := match graph.node node with
            | .recursive _ => (recursionKey node scs :: resolved.recursionAncestry uv).eraseDups
            | _ => resolved.recursionAncestry uv
          obtain ⟨expandedSafe, growth, fragmentBound⟩ := (enumeration_safety graph fuel).1 _ _ _ expanded produced
            (ancestry_safe resolved ancestry resolvedSafe) bounded expansion
          have expandedFrame := (enumeration_protected graph fuel).1 _ _ uv _ expanded produced
            (ancestry_safe resolved ancestry resolvedSafe) (by simpa [resolvedCounter, readCounter] using inside)
            resolvedFrame.root bounded separate expansion
          obtain ⟨ignored, cleared, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ expanded cleared).mp bookkeeping
          obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain ⟨writtenSafe, writtenCounter⟩ := setValue_safe uv (.enumerated produced) _ written
            (ancestry_safe expanded [] expandedSafe) expandedFrame.root (by simp) fragmentBound writing
          obtain ⟨rfl, rfl⟩ := (success_pure produced fragment written after).mp final
          refine ⟨writtenSafe, ?_, ?_⟩
          · simpa [writtenCounter, resolvedCounter, readCounter] using growth
          · simpa [writtenCounter] using fragmentBound

/-- A source fold preserves an invariant when each listed input does. -/
theorem foldlM_invariant (action : α → β → EnumerateM Symbol Guard α)
    (invariant : State Symbol Guard → Prop) (inputs : List β)
    (step : ∀ input ∈ inputs, ∀ accumulator before result after, invariant before →
      Success (action accumulator input) before result after → invariant after)
    (accumulator result : α) (before after : State Symbol Guard) (valid : invariant before)
    (success : Success (inputs.foldlM action accumulator) before result after) : invariant after := by
  induction inputs generalizing accumulator before with
  | nil =>
      obtain ⟨_, same⟩ := (success_pure accumulator result before after).mp success
      subst after
      exact valid
  | cons input rest ih =>
      rw [List.foldlM_cons] at success
      obtain ⟨middle, intermediate, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      exact ih (fun input member => step input (List.mem_cons_of_mem _ member)) middle intermediate
        (step input (by simp) accumulator before middle intermediate valid first) continued

/-- The entire scheduler scan preserves bounded storage and the allocation supply. -/
theorem findExpandable_storage (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) (storage : StorageValid before)
    (success : Success (findExpandable graph fuel) before result after) : Stable before.counter after := by
  unfold findExpandable at success
  change Success (get >>= fun state => do
    let summary ← state.values.zipIdx.foldlM (collect graph fuel) ([], [])
    finishScan summary) before result after at success
  obtain ⟨current, readState, read, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨currentSame, readSame⟩ := (get_success before readState current).mp read
  subst current
  subst readState
  obtain ⟨summary, scanned, scan, final⟩ := (success_bind _ _ _ _ _).mp continued
  have step : ∀ entry ∈ before.values.zipIdx, ∀ accumulator previous result next, Stable before.counter previous →
      Success (collect graph fuel accumulator entry) previous result next → Stable before.counter next := by
    intro entry member accumulator previous result next valid success
    obtain ⟨value, index⟩ := entry
    obtain ⟨candidates, blocked⟩ := accumulator
    cases value with
    | eliminated | enumerated _ =>
        obtain ⟨_, same⟩ := (success_pure (candidates, blocked) result previous next).mp success
        subst next
        exact valid
    | unenumerated node scs =>
        have bounds : ∀ sc ∈ scs, sc.var < before.counter :=
          storage.values _ (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp member))
        unfold collect at success
        obtain ⟨blockedResult, resolved, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
        have localStep : ∀ sc ∈ scs, ∀ accumulator (old : State Symbol Guard) output new, Stable before.counter old →
            Success (resolve fuel accumulator sc) old output new → Stable before.counter new := by
          intro sc present accumulator old output new oldValid resolvedSuccess
          unfold resolve at resolvedSuccess
          obtain ⟨root, middle, resolution, final⟩ := (success_bind _ _ _ _ _).mp resolvedSuccess
          obtain ⟨validMiddle, _⟩ := representative_stable before.counter fuel sc.var root old middle oldValid
            (bounds sc present) resolution
          obtain ⟨_, same⟩ := (success_pure (root :: accumulator) output middle new).mp final
          subst new
          exact validMiddle
        have resolvedValid := foldlM_invariant (resolve fuel) (Stable before.counter) scs localStep
          blocked blockedResult previous resolved valid traversed
        obtain ⟨_, same⟩ := (success_pure _ result resolved next).mp final
        subst next
        exact resolvedValid
  have scannedValid := foldlM_invariant (collect graph fuel) (Stable before.counter) before.values.zipIdx step
    ([], []) summary before scanned ⟨storage, rfl⟩ scan
  obtain ⟨_, same⟩ := (finishScan_success summary scanned after result).mp final
  subst after
  exact scannedValid

/-- Every completed scheduler scan preserves both reachable-state invariants. -/
theorem findExpandable_safety (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) (safe : Safe before)
    (success : Success (findExpandable graph fuel) before result after) :
    Safe after ∧ after.counter = before.counter := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives safe.1.total
  obtain ⟨valid, _⟩ := findExpandable_exact graph fuel roots before after result paths success
  obtain ⟨storage, counter⟩ := findExpandable_storage graph fuel before after result safe.1 success
  exact ⟨⟨storage, scan_live before after roots paths valid safe.2⟩, counter⟩

/-- The selected allocated root has no self-reference in its pending constraints. -/
structure Ready (uv : Nat) (state : State Symbol Guard) : Prop where
  safe : Safe state
  inside : uv < state.counter
  root : IsRoot state.representatives uv
  avoids : ∀ node scs, state.values[uv]? = some (.unenumerated (some node) scs) →
    Avoids state.representatives uv scs

/-- Scheduler selection establishes the precondition for the caller's final write. -/
theorem findExpandable_ready (graph : Graph Symbol Guard) (fuel uv : Nat) (before after : State Symbol Guard)
    (available : Option (List Nat)) (preference : List Nat → Option Nat) (safe : Safe before)
    (success : Success (findExpandable graph fuel) before available after)
    (selected : pickNext preference available = .expand uv) : Ready uv after := by
  cases available with
  | none => cases selected
  | some available =>
      have member := pickNext_safe preference available uv selected
      obtain ⟨_, root, ⟨value, stored, _⟩, avoids⟩ := findExpandable_safe graph fuel before after available uv
        safe.1.total safe.2 success member
      have safeAfter := (findExpandable_safety graph fuel before after (some available) safe success).1
      refine ⟨safeAfter, ?_, root, fun node scs stored => avoids uv (some node) scs stored⟩
      have bound := (List.getElem?_eq_some_iff.mp stored).1
      rw [safeAfter.1.aligned]
      exact bound

/-- A root read retains the caller's ready-to-expand condition. -/
theorem getValue_ready (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (ready : Ready uv before) (success : Success (getValue fuel uv) before value after) :
    Ready uv after ∧ after.counter = before.counter := by
  obtain ⟨safeAfter, counter, frame, _⟩ := getValue_root fuel uv before after value ready.safe ready.inside ready.root success
  refine ⟨⟨safeAfter, by simpa [counter] using ready.inside, frame.root, ?_⟩, counter⟩
  intro node scs stored
  exact frame.avoids scs (ready.avoids node scs (frame.value ▸ stored))

/-- The source repeated-recursion branch clears only the selected pending constraints. -/
def checkRepeated (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended) :
    EnumerateM Symbol Guard Bool := do
  match graph.node node with
  | .recursive _ =>
      let root ← representative fuel uv
      let current : State Symbol Guard ← get
      if recursionKey node scs ∈ current.recursionAncestry root then
        setValue root (.unenumerated (some node) [])
        pure true
      else pure false
  | _ => pure false

/-- Repeated-recursion bookkeeping preserves the selected root's safety conditions. -/
theorem checkRepeated_ready (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (repeated : Bool) (ready : Ready uv before)
    (success : Success (checkRepeated graph fuel uv node scs) before repeated after) :
    Ready uv after ∧ after.counter = before.counter := by
  cases view : graph.node node with
  | empty | alternatives _ | unresolved _ =>
      have action : Success (pure false) before repeated after := by simpa [checkRepeated, view] using success
      obtain ⟨_, same⟩ := (success_pure false repeated before after).mp action
      subst after
      exact ⟨ready, rfl⟩
  | recursive body =>
      simp only [checkRepeated, view] at success
      obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨rootSame, resolvedSafe, resolvedCounter, frame⟩ := representative_root fuel uv root before resolved
        ready.safe ready.inside ready.root resolution
      subst root
      obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨currentSame, currentStateSame⟩ := (get_success resolved currentState current).mp reading
      subst current
      subst currentState
      split at continued
      · obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        obtain ⟨writtenSafe, writtenCounter⟩ := setValue_safe uv (.unenumerated (some node) []) resolved written
          resolvedSafe frame.root (by simp) (by simp [SlotBound]) writing
        have writtenSame := (modify_success _ resolved written).mp writing
        obtain ⟨_, afterSame⟩ := (success_pure true repeated written after).mp final
        subst after
        refine ⟨⟨writtenSafe, by simpa [writtenCounter, resolvedCounter] using ready.inside, ?_, ?_⟩,
          writtenCounter.trans resolvedCounter⟩
        · simpa [writtenSame] using frame.root
        · intro selected constraints stored
          have inside : uv < resolved.values.length := by rw [← resolvedSafe.1.aligned, resolvedCounter]; exact ready.inside
          have exactValue : selected = node ∧ constraints = [] := by
            simpa [writtenSame, List.getElem?_set, inside] using stored.symm
          simp [exactValue.2, Avoids]
      · obtain ⟨_, same⟩ := (success_pure false repeated resolved after).mp continued
        subst after
        refine ⟨⟨resolvedSafe, by simpa [resolvedCounter] using ready.inside, frame.root, ?_⟩, resolvedCounter⟩
        intro selected constraints stored
        exact frame.avoids constraints (ready.avoids selected constraints (frame.value ▸ stored))

/-- An observing callback can accept or reject work but does not change machine state. -/
def ReadOnlyOracle (oracle : Oracle Symbol Guard OracleState) : Prop :=
  ∀ oracleState uv input before output after, Success (oracle oracleState uv input) before output after → after = before

/-- The ordinary enumerator's callback leaves every state unchanged. -/
theorem noPruning_readOnly : ReadOnlyOracle (noPruning : Oracle Symbol Guard Unit) := by
  intro oracleState uv input before output after success
  exact ((success_pure (false, oracleState) output before after).mp success).2

/-- The source caller equation exposes its repeated-recursion bookkeeping. -/
theorem fully_action (graph : Graph Symbol Guard) (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState) (fuel : Nat) (oracleState : OracleState) :
    enumerateFully graph order oracle (fuel + 1) oracleState = (do
      let next := pickNext (order oracleState) (← findExpandable graph (fuel + 1))
      match next with
      | .done => pure ()
      | .stuck => reject
      | .expand uv =>
          match ← getValue (fuel + 1) uv with
          | .unenumerated (some node) scs =>
              let repeated ← checkRepeated graph (fuel + 1) uv node scs
              if repeated then enumerateFully graph order oracle fuel oracleState
              else
                let (beforeReject, beforeState) ← oracle oracleState uv (.inr node)
                require (!beforeReject)
                let fragment ← enumerateOut graph (fuel + 1) uv
                let (afterReject, afterState) ← oracle beforeState uv (.inl fragment)
                require (!afterReject)
                enumerateFully graph order oracle fuel afterState
          | _ => reject) := by
  simp only [enumerateFully, checkRepeated]
  congr 1
  funext available
  cases selected : pickNext (order oracleState) available with
  | done => rfl
  | stuck => rfl
  | expand uv =>
      simp only
      congr 1
      funext value
      cases value with
      | eliminated | enumerated _ => rfl
      | unenumerated node scs =>
          cases node with
          | none => rfl
          | some node =>
              cases view : graph.node node <;> simp [view, bind_assoc]
              congr 1
              funext root
              congr 1
              funext state
              split <;> simp_all

/-- A completed caller has no slot that can initiate more expansion. -/
def Finished (graph : Graph Symbol Guard) (state : State Symbol Guard) : Prop :=
  ∀ value ∈ state.values, candidate graph value = false

/-- The scheduler reports completion only when every slot is ineligible. -/
theorem findExpandable_finished (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (safe : Safe before) (success : Success (findExpandable graph fuel) before none after) : Finished graph after := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives safe.1.total
  obtain ⟨scanned, result⟩ := findExpandable_exact graph fuel roots before after none paths success
  have empty : (before.values.zipIdx.foldl (collectPure graph roots) ([], [])).1 = [] := by
    unfold offered at result
    dsimp only at result
    split at result
    · simpa using (List.isEmpty_iff.mp ‹_›)
    · cases result
  intro value member
  rw [scanned.values] at member
  cases chosen : candidate graph value with
  | false => rfl
  | true =>
      obtain ⟨index, stored⟩ := List.mem_iff_getElem?.mp member
      have present : (value, index) ∈ before.values.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr stored
      have impossible := (candidates_exact graph roots before.values.zipIdx ([], []) index).mpr
        (Or.inr ⟨(value, index), present, rfl, chosen⟩)
      simp [empty] at impossible

/-- The complete source caller preserves safety and finishes all eligible slots. -/
theorem enumerateFully_outcome (graph : Graph Symbol Guard) (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle) (fuel : Nat)
    (oracleState : OracleState) (before after : State Symbol Guard) (safe : Safe before)
    (success : Success (enumerateFully graph order oracle fuel oracleState) before () after) :
    Safe after ∧ before.counter ≤ after.counter ∧ Finished graph after := by
  induction fuel generalizing oracleState before with
  | zero => exact (success_failure .fuelExhausted before after () success).elim
  | succ fuel ih =>
      rw [fully_action] at success
      obtain ⟨available, scanned, scan, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨scannedSafe, scannedCounter⟩ := findExpandable_safety graph (fuel + 1) before scanned available safe scan
      cases selected : pickNext (order oracleState) available with
      | done =>
          simp only [selected] at continued
          obtain ⟨_, same⟩ := (success_pure () () scanned after).mp continued
          subst after
          have noneSelected : available = none := by
            cases available with
            | none => rfl
            | some available =>
                cases available with
                | nil => cases selected
                | cons first rest =>
                    simp only [pickNext] at selected
                    split at selected
                    · split at selected <;> cases selected
                    · cases selected
          subst available
          exact ⟨scannedSafe, Nat.le_of_eq scannedCounter.symm, findExpandable_finished graph (fuel + 1) before scanned safe scan⟩
      | stuck =>
          simp only [selected] at continued
          exact (reject_unsuccessful scanned after () continued).elim
      | expand uv =>
          have ready := findExpandable_ready graph (fuel + 1) uv before scanned available (order oracleState) safe scan selected
          simp only [selected] at continued
          obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨readReady, readCounter⟩ := getValue_ready (fuel + 1) uv scanned readState value ready reading
          cases value with
          | eliminated | enumerated _ => exact (reject_unsuccessful readState after () continued).elim
          | unenumerated node scs =>
              cases node with
              | none => exact (reject_unsuccessful readState after () continued).elim
              | some node =>
                  obtain ⟨repeated, checked, checking, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  obtain ⟨checkedReady, checkedCounter⟩ := checkRepeated_ready graph (fuel + 1) uv node scs
                    readState checked repeated readReady checking
                  cases repeated with
                  | true =>
                      obtain ⟨safeAfter, growth, finished⟩ := ih oracleState checked checkedReady.safe continued
                      exact ⟨safeAfter, by simpa [checkedCounter, readCounter, scannedCounter] using growth, finished⟩
                  | false =>
                      obtain ⟨⟨beforeReject, beforeState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                      have observedSame := observer oracleState uv (.inr node) checked _ observed observation
                      subst observed
                      obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                      cases ignored
                      obtain ⟨_, same⟩ := (require_success (!beforeReject) checked accepted).mp acceptance
                      subst accepted
                      obtain ⟨fragment, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
                      obtain ⟨expandedSafe, expansionGrowth, _⟩ := enumerateOut_safe graph (fuel + 1) uv checked expanded fragment
                        checkedReady.safe checkedReady.inside checkedReady.root checkedReady.avoids expansion
                      obtain ⟨⟨afterReject, afterState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                      have observedSame := observer beforeState uv (.inl fragment) expanded _ observed observation
                      subst observed
                      obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                      cases ignored
                      obtain ⟨_, same⟩ := (require_success (!afterReject) expanded accepted).mp acceptance
                      subst accepted
                      obtain ⟨safeAfter, growth, finished⟩ := ih afterState expanded expandedSafe continued
                      refine ⟨safeAfter, ?_, finished⟩
                      have totalGrowth := Nat.le_trans expansionGrowth growth
                      simpa [checkedCounter, readCounter, scannedCounter] using totalGrowth

/-- Every successful source caller preserves storage and live roots. -/
theorem enumerateFully_safety (graph : Graph Symbol Guard) (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle) (fuel : Nat)
    (oracleState : OracleState) (before after : State Symbol Guard) (safe : Safe before)
    (success : Success (enumerateFully graph order oracle fuel oracleState) before () after) :
    Safe after ∧ before.counter ≤ after.counter := by
  obtain ⟨safeAfter, growth, _⟩ := enumerateFully_outcome graph order oracle observer fuel oracleState before after safe success
  exact ⟨safeAfter, growth⟩

/-- Every pending graph slot at completion is an unconstrained recursive marker. -/
theorem finished_pending (graph : Graph Symbol Guard) (state : State Symbol Guard) (finished : Finished graph state)
    (uv node : Nat) (scs : List Suspended) (stored : state.values[uv]? = some (.unenumerated (some node) scs)) :
    scs = [] ∧ ∃ body, graph.node node = .recursive body := by
  have ineligible := finished _ (List.mem_of_getElem? stored)
  cases view : graph.node node <;> simp [candidate, view] at ineligible
  exact ⟨ineligible, _, rfl⟩

/-- Starting the ordinary caller at its real initial state establishes its safety invariant. -/
theorem initialized_enumeration_safe (graph : Graph Symbol Guard) (fuel root : Nat) (after : State Symbol Guard)
    (success : Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) (initial root) () after) :
    Safe after ∧ 1 ≤ after.counter :=
  enumerateFully_safety graph (fun _ _ => none) noPruning noPruning_readOnly fuel () (initial root) after
    ⟨initial_storage root, initial_live root⟩ success

/-- Rendering changes only union-find compression and retains all stored payloads. -/
structure RenderStable (before after : State Symbol Guard) : Prop where
  safe : Safe after
  counter : after.counter = before.counter
  values : after.values = before.values
  obligations : after.obligations = before.obligations
  classes : ∀ left right, UnionFind.SameClass after.representatives left right ↔ UnionFind.SameClass before.representatives left right

/-- An unchanged rendering state retains all stored data. -/
theorem RenderStable.refl (state : State Symbol Guard) (safe : Safe state) : RenderStable state state :=
  ⟨safe, rfl, rfl, rfl, fun _ _ => Iff.rfl⟩

/-- Rendering preservation composes through consecutive actions. -/
theorem RenderStable.trans (left : RenderStable before middle) (right : RenderStable middle after) :
    RenderStable before after :=
  ⟨right.safe, right.counter.trans left.counter, right.values.trans left.values, right.obligations.trans left.obligations,
    fun first second => (right.classes first second).trans (left.classes first second)⟩

/-- A bounded UVar read preserves storage and returns a bounded stored value. -/
theorem getValue_storage (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (safe : Safe before) (inside : uv < before.counter)
    (success : Success (getValue fuel uv) before value after) : RenderStable before after ∧ SlotBound after.counter value := by
  obtain ⟨found, lookup, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  have reached := (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1
  have root : IsRoot before.representatives found.representative := ⟨found.size, .root (UnionFind.reaches_terminal reached)⟩
  have safeAfter := (compression_safe before safe fuel uv found.representative inside root found lookup).1
  exact ⟨⟨safeAfter, rfl, rfl, rfl, UnionFind.findRoot_classes safe.1.total lookup⟩,
    safe.1.values value (List.mem_of_getElem? stored)⟩

/-- A bounded fragment list bounds each listed child. -/
theorem fragmentsBound_member (limit : Nat) (children : List (Fragment Symbol))
    (bounded : FragmentsBound limit children) (child : Fragment Symbol) (member : child ∈ children) :
    FragmentBound limit child := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | present
      · exact bounded.1
      · exact ih bounded.2 present

/-- Actual fragment rendering preserves every stored value and obligation. -/
theorem expandFragment_storage (graph : Graph Symbol Guard) (marker : Symbol) (fuel : Nat)
    (fragment : Fragment Symbol) (before after : State Symbol Guard) (term : Term Symbol)
    (safe : Safe before) (bounded : FragmentBound before.counter fragment)
    (success : Success (expandFragment graph marker fuel fragment) before term after) : RenderStable before after := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term success).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          change Success (children.mapM (expandFragment graph marker fuel) >>= fun terms => pure (.node symbol terms))
            before term after at success
          obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
          have step : ∀ child ∈ children, ∀ previous output next, RenderStable before previous →
              Success (expandFragment graph marker fuel child) previous output next → RenderStable before next := by
            intro child member previous output next valid childSuccess
            have childBound : FragmentBound previous.counter child := by
              rw [valid.counter]
              exact fragmentsBound_member before.counter children bounded child member
            exact valid.trans (ih child previous next output valid.safe childBound childSuccess)
          have rendered := mapM_invariant (expandFragment graph marker fuel) (RenderStable before) children step
            before middle terms (.refl before safe) traversed
          obtain ⟨_, same⟩ := (success_pure (.node symbol terms) term middle after).mp final
          subst after
          exact rendered
      | hole uv =>
          change Success (getValue (fuel + 1) uv >>= fun value => match value with
            | .enumerated fragment => expandFragment graph marker fuel fragment
            | .unenumerated (some node) _ => match graph.node node with
              | .recursive _ => pure (.node marker [])
              | _ => EnumerationState.failure .unfinishedFragment
            | _ => EnumerationState.failure .unfinishedFragment) before term after at success
          obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨readStable, valueBound⟩ := getValue_storage (fuel + 1) uv before middle value safe bounded reading
          cases value with
          | eliminated => exact (success_failure .unfinishedFragment middle after term final).elim
          | enumerated stored => exact readStable.trans (ih stored middle after term readStable.safe valueBound final)
          | unenumerated node scs =>
              cases node with
              | none => exact (success_failure .unfinishedFragment middle after term final).elim
              | some node =>
                  cases view : graph.node node with
                  | recursive body =>
                      simp only [view] at final
                      obtain ⟨_, same⟩ := (success_pure (.node marker []) term middle after).mp final
                      subst after
                      exact readStable
                  | empty | alternatives _ | unresolved _ =>
                      simp only [view] at final
                      exact (success_failure .unfinishedFragment middle after term final).elim

/-- The top-level UVar renderer retains the caller's safe stored state. -/
theorem expandUVar_storage (graph : Graph Symbol Guard) (marker : Symbol) (fuel uv : Nat)
    (before after : State Symbol Guard) (term : Term Symbol) (safe : Safe before) (inside : uv < before.counter)
    (success : Success (expandUVar graph marker fuel uv) before term after) : RenderStable before after := by
  unfold expandUVar at success
  obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readStable, valueBound⟩ := getValue_storage (fuel + 1) uv before middle value safe inside reading
  cases value with
  | enumerated fragment =>
      exact readStable.trans (expandFragment_storage graph marker fuel fragment middle after term readStable.safe valueBound final)
  | eliminated => exact (reject_unsuccessful middle after term final).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful middle after term final).elim
      | some node =>
          cases view : graph.node node with
          | recursive body =>
              simp only [view] at final
              obtain ⟨_, same⟩ := (success_pure (.node marker []) term middle after).mp final
              subst after
              exact readStable
          | empty | alternatives _ | unresolved _ =>
              simp only [view] at final
              exact (reject_unsuccessful middle after term final).elim

/-- Every successful ordinary run retains safe storage after term and residual rendering. -/
theorem runs_safe (graph : Graph Symbol Guard) (marker : Symbol) (fuel root : Nat)
    (term : Term Symbol) (pending : List (Guard × Term Symbol)) (after : State Symbol Guard)
    (success : .ok ((term, pending), after) ∈ runs graph marker fuel root) :
    Safe after ∧ 1 ≤ after.counter ∧ Finished graph after := by
  unfold runs at success
  change Success _ (initial root) (term, pending) after at success
  obtain ⟨ignored, enumerated, enumeration, continued⟩ := (success_bind _ _ _ _ _).mp success
  cases ignored
  obtain ⟨enumeratedSafe, supply, finished⟩ := enumerateFully_outcome graph (fun _ _ => none) noPruning noPruning_readOnly
    fuel () (initial root) enumerated ⟨initial_storage root, initial_live root⟩ enumeration
  obtain ⟨rendered, renderedState, rendering, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have rootBound : 0 < enumerated.counter := by change 1 ≤ enumerated.counter at supply; omega
  have renderedStable := expandUVar_storage graph marker fuel 0 enumerated renderedState rendered enumeratedSafe rootBound rendering
  obtain ⟨current, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨currentSame, readSame⟩ := (get_success renderedState readState current).mp reading
  subst current
  subst readState
  obtain ⟨obligations, guarded, traversal, final⟩ := (success_bind _ _ _ _ _).mp continued
  have step : ∀ obligation ∈ renderedState.obligations, ∀ previous output next, RenderStable renderedState previous →
      Success (do pure (obligation.1, ← expandFragment graph marker fuel obligation.2)) previous output next →
      RenderStable renderedState next := by
    intro obligation member previous output next valid renderedSuccess
    obtain ⟨guardedTerm, middle, rendering, final⟩ := (success_bind _ _ _ _ _).mp renderedSuccess
    have bounded : FragmentBound previous.counter obligation.2 := by
      rw [valid.counter]
      exact renderedStable.safe.1.guards obligation member
    have rendered := expandFragment_storage graph marker fuel obligation.2 previous middle guardedTerm valid.safe bounded rendering
    obtain ⟨_, same⟩ := (success_pure (obligation.1, guardedTerm) output middle next).mp final
    subst next
    exact valid.trans rendered
  have guardedStable := mapM_invariant
    (fun obligation => do pure (obligation.1, ← expandFragment graph marker fuel obligation.2))
    (RenderStable renderedState) renderedState.obligations step renderedState guarded obligations
    (.refl renderedState renderedStable.safe) traversal
  obtain ⟨_, same⟩ := (success_pure (rendered, obligations) (term, pending) guarded after).mp final
  subst after
  have finalStable := renderedStable.trans guardedStable
  refine ⟨finalStable.safe, ?_, ?_⟩
  · simpa [finalStable.counter, initial] using supply
  · intro value member
    exact finished value (by simpa [finalStable.values] using member)

end MicroCFTA.EnumerationDriver
