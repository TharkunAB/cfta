import MicroCFTA.EnumerationDependencies

/-!
# Allowed suspended-reference targets

Stored references originate in earlier references, inherited inputs, or fresh
equality variables. A fixed predicate records the allowed target variables.
-/

namespace MicroCFTA.EnumerationReferences
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Every listed suspended reference has an allowed variable. -/
def InputsAllowed (allowed : Nat → Prop) (scs : List Suspended) : Prop := ∀ sc ∈ scs, allowed sc.var

/-- Every suspended reference in the store has an allowed variable. -/
def ReferencesAllowed (allowed : Nat → Prop) (state : State Symbol Guard) : Prop :=
  ∀ value ∈ state.values, InputsAllowed allowed (references value)

/-- Descent retains the variable of each input constraint. -/
theorem descend_allowed (allowed : Nat → Prop) (scs : List Suspended) (index : Nat) (inputs : InputsAllowed allowed scs) :
    InputsAllowed allowed (descendScs index scs) := by
  intro sc member
  simp only [descendScs, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨original, present, rfl⟩, _⟩ := member
  exact inputs original present

/-- A slot write retains the allowed-reference predicate. -/
theorem setValue_allowed (allowed : Nat → Prop) (uv : Nat) (value : UVarValue Symbol) (before after : State Symbol Guard)
    (valid : ReferencesAllowed allowed before) (payload : InputsAllowed allowed (references value))
    (success : Success (setValue uv value) before () after) : ReferencesAllowed allowed after := by
  obtain rfl := (modify_success _ before after).mp success
  intro stored member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid stored old
  · simpa [same] using payload

/-- Raw reading retains the store and exposes its allowed references. -/
theorem rawValue_allowed (allowed : Nat → Prop) (uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (valid : ReferencesAllowed allowed before) (success : Success (rawValue uv) before value after) :
    ReferencesAllowed allowed after ∧ InputsAllowed allowed (references value) := by
  obtain ⟨stored, same⟩ := (rawValue_success uv before after value).mp success
  subst after
  exact ⟨valid, valid value (List.mem_of_getElem? stored)⟩

/-- Representative lookup changes no suspended reference. -/
theorem representative_allowed (allowed : Nat → Prop) (fuel uv root : Nat) (before after : State Symbol Guard)
    (valid : ReferencesAllowed allowed before) (success : Success (representative fuel uv) before root after) : ReferencesAllowed allowed after := by
  obtain ⟨found, _, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact valid

/-- Union changes no suspended reference. -/
theorem unionVariables_allowed (allowed : Nat → Prop) (fuel left right : Nat) (before after : State Symbol Guard)
    (valid : ReferencesAllowed allowed before) (success : Success (unionVariables fuel left right) before () after) : ReferencesAllowed allowed after := by
  obtain ⟨forest, _, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact valid

/-- Pending-slot intersection concatenates only references from its two inputs. -/
theorem intersection_allowed (allowed : Nat → Prop) (graph : Graph Symbol Guard) (left right merged : UVarValue Symbol)
    (leftValid : InputsAllowed allowed (references left)) (rightValid : InputsAllowed allowed (references right))
    (success : intersectValues graph left right = some merged) : InputsAllowed allowed (references merged) := by
  cases left <;> cases right <;> simp only [intersectValues] at success
  all_goals try cases success
  intro sc member
  rcases List.mem_append.mp member with left | right
  · exact leftValid sc left
  · exact rightValid sc right

/-- The complete source assimilation action creates no new suspended reference. -/
theorem assimilate_allowed (allowed : Nat → Prop) (graph : Graph Symbol Guard) (target source : Nat) (before after : State Symbol Guard)
    (valid : ReferencesAllowed allowed before) (success : Success (EnumerationState.assimilate graph target source) before () after) : ReferencesAllowed allowed after := by
  by_cases same : target = source
  · subst source
    have unchanged : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    simpa [unchanged] using valid
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, readSource, readingSource, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨sourceValid, sourcePayload⟩ := rawValue_allowed allowed source before readSource sourceValue valid readingSource
    cases sourceValue with
    | eliminated =>
        obtain ⟨_, same⟩ := (success_pure () () readSource after).mp continued
        subst after
        exact sourceValid
    | enumerated fragment =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        exact (success_failure .invalidIntersection readTarget after () continued).elim
    | unenumerated node scs =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨targetValid, targetPayload⟩ := rawValue_allowed allowed target readSource readTarget targetValue sourceValid readingTarget
        cases intersection : intersectValues graph (.unenumerated node scs) targetValue with
        | none =>
            simp only [intersection] at continued
            exact (success_failure .invalidIntersection readTarget after () continued).elim
        | some merged =>
            have mergedValid := intersection_allowed allowed graph (.unenumerated node scs) targetValue merged sourcePayload targetPayload intersection
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            obtain ⟨_, same⟩ := (require_success _ readTarget checked).mp required
            subst checked
            obtain ⟨ignored, targetWritten, targetWrite, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have targetWrittenValid := setValue_allowed allowed target merged readTarget targetWritten targetValid mergedValid targetWrite
            obtain ⟨ignored, sourceWritten, sourceWrite, final⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have sourceWrittenValid := setValue_allowed allowed source .eliminated targetWritten sourceWritten targetWrittenValid
              (by simp [references, InputsAllowed]) sourceWrite
            obtain rfl := (modify_success _ sourceWritten after).mp final
            exact sourceWrittenValid

/-- Source node restriction adds only its inherited suspended references. -/
theorem mergeNode_allowed (allowed : Nat → Prop) (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (valid : ReferencesAllowed allowed before) (inputs : InputsAllowed allowed scs)
    (success : Success (mergeNode graph fuel uv node scs) before () after) : ReferencesAllowed allowed after := by
  unfold mergeNode at success
  obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp success
  have resolvedValid := representative_allowed allowed fuel uv root before resolved valid resolution
  obtain ⟨previous, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨readValid, payloadValid⟩ := rawValue_allowed allowed root resolved readState previous resolvedValid reading
  cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
  | none =>
      simp only [intersection] at continued
      exact (success_failure .invalidIntersection readState after () continued).elim
  | some merged =>
      have mergedValid := intersection_allowed allowed graph (.unenumerated (some node) scs) previous merged inputs payloadValid intersection
      simp only [intersection] at continued
      obtain ⟨ignored, written, writing, continued⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      have writtenValid := setValue_allowed allowed root merged readState written readValid mergedValid writing
      obtain ⟨ignored, inherited, inheriting, final⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain rfl := (modify_success _ written inherited).mp inheriting
      obtain ⟨_, same⟩ := (require_success _ _ after).mp final
      subst after
      exact writtenValid

/-- The actual terminal merge only moves existing suspended references. -/
theorem mergeTerminal_allowed (allowed : Nat → Prop) (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (valid : ReferencesAllowed allowed before)
    (success : Success (mergeTerminal graph fuel first rest) before target after) : ReferencesAllowed allowed after := by
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedValid := mapM_invariant (fun sc => representative fuel sc.var) (ReferencesAllowed allowed) (first :: rest)
    (fun sc _ previous result next valid step => representative_allowed allowed fuel sc.var result previous next valid step)
    before scanned recorded valid scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedValid := forM_invariant (fun sc => unionVariables fuel first.var sc.var) (ReferencesAllowed allowed) rest
    (fun sc _ previous next valid step => unionVariables_allowed allowed fuel first.var sc.var previous next valid step)
    scanned united scannedValid unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedValid := representative_allowed allowed fuel first.var winner united resolved unitedValid resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have assimilatedValid := forM_invariant (EnumerationState.assimilate graph winner) (ReferencesAllowed allowed) recorded
    (fun source _ previous next valid step => assimilate_allowed allowed graph winner source previous next valid step)
    resolved assimilated resolvedValid assimilation
  obtain ⟨_, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst after
  exact assimilatedValid

/-- The actual terminal node branch retains only existing and inherited allowed references. -/
theorem enumerateNode_terminal_allowed (allowed : Nat → Prop) (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (first : Suspended) (rest : List Suspended) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (valid : ReferencesAllowed allowed before) (inputs : InputsAllowed allowed scs) (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) : ReferencesAllowed allowed after := by
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, merging, continued⟩ := (success_bind _ _ _ _ _).mp success
  have mergedValid := mergeTerminal_allowed allowed graph (fuel + 1) first rest before merged root valid merging
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have restrictedValid := mergeNode_allowed allowed graph (fuel + 1) root node _ merged restricted mergedValid
    (fun sc member => inputs sc (List.mem_filter.mp member).1) restriction
  obtain ⟨_, same⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst after
  exact restrictedValid

/-- A fresh pending slot contains no reference. -/
theorem allocation_allowed (allowed : Nat → Prop) (node : Option Nat) (state : State Symbol Guard) (valid : ReferencesAllowed allowed state) :
    ReferencesAllowed allowed (allocated node state) := by
  intro value member
  rcases List.mem_append.mp member with old | fresh
  · exact valid value old
  · have same : value = .unenumerated node [] := by simpa using fresh
    simp [same, references, InputsAllowed]

/-- Repeated class allocation creates no stored references. -/
theorem suspension_allowed (allowed : Nat → Prop) (count : Nat) (state : State Symbol Guard) (valid : ReferencesAllowed allowed state) :
    ReferencesAllowed allowed (suspendedState count state) := by
  induction count generalizing state with
  | zero => exact valid
  | succ count ih => exact ih (allocated none state) (allocation_allowed allowed none state valid)

/-- Each returned fresh class variable is inside the future allocation region. -/
theorem suspended_allowed (allowed : Nat → Prop) (limit start : Nat) (tries : List EqualityTrie.Trie)
    (lower : limit ≤ start) (future : ∀ uv, limit ≤ uv → allowed uv) : InputsAllowed allowed (suspendedVars start tries) := by
  intro sc member
  have listed : sc.var ∈ (suspendedVars start tries).map EqualityTrie.Suspended.var := List.mem_map.mpr ⟨sc, member, rfl⟩
  rw [suspendedVars_variables] at listed
  obtain ⟨index, _, same⟩ := List.mem_range'.mp listed
  apply future sc.var
  omega

/-- Residual recording changes no suspended reference. -/
theorem recordResidual_allowed (allowed : Nat → Prop) (residual : Option Guard) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (valid : ReferencesAllowed allowed before) (success : Success (recordResidual residual fragment) before () after) : ReferencesAllowed allowed after := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact valid
  | some guard =>
      obtain rfl := (modify_success _ before after).mp success
      exact valid

/-- Actual traversal retains allowed targets when all future fresh variables are allowed. -/
theorem enumeration_allowed (allowed : Nat → Prop) (limit : Nat) (future : ∀ uv, limit ≤ uv → allowed uv)
    (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node (before after : State Symbol Guard) fragment, Safe before → limit ≤ before.counter →
      ReferencesAllowed allowed before → InputsAllowed allowed scs → (∀ sc ∈ scs, sc.var < before.counter) →
      Success (enumerateNode graph fuel scs node) before fragment after → ReferencesAllowed allowed after) ∧
    (∀ scs edge (before after : State Symbol Guard) fragment, Safe before → limit ≤ before.counter →
      ReferencesAllowed allowed before → InputsAllowed allowed scs → (∀ sc ∈ scs, sc.var < before.counter) →
      Success (enumerateEdge graph fuel scs edge) before fragment after → ReferencesAllowed allowed after) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node before after fragment _ _ _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge before after fragment _ _ _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node before after fragment safe lower valid inputs bounded success
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | alternatives edges | recursive body | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                exact enumerateNode_terminal_allowed allowed graph fuel node scs first rest before after fragment valid inputs
                  (by simp [view]) terminal success
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨_, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact ih.2 scs edge before after fragment safe lower valid inputs bounded continued)
                | (obtain ⟨uv, middle, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
                   have exactState : uv = before.counter ∧ middle = allocated (some node) before := by
                     simpa [Success, allocate_exact, ExceptT.run] using allocation
                   obtain ⟨uvSame, middleSame⟩ := exactState
                   subst uv
                   subst middle
                   obtain ⟨_, same⟩ := (success_pure (.hole before.counter) fragment (allocated (some node) before) after).mp final
                   subst after
                   exact allocation_allowed allowed (some node) before valid)
      · intro scs edge before after fragment safe lower valid inputs bounded success
        rw [edge_action graph fuel scs edge] at success
        obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp success
        cases ignored
        obtain ⟨_, same⟩ := (require_success _ before checked).mp required
        subst checked
        obtain ⟨added, suspended, suspension, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have exactState : added = suspendedVars before.counter edge.equalities ∧
            suspended = suspendedState edge.equalities.length before := by
          simpa [Success, suspendMany_exact, ExceptT.run] using suspension
        obtain ⟨addedSame, suspendedSame⟩ := exactState
        subst added
        subst suspended
        let start := suspendedState edge.equalities.length before
        let allInputs := scs ++ suspendedVars before.counter edge.equalities
        have startSafe : Safe start := suspension_safe edge.equalities.length before safe
        have startGrowth : before.counter ≤ start.counter := by simp [start, suspended_counter]
        have startValid : ReferencesAllowed allowed start := suspension_allowed allowed edge.equalities.length before valid
        have inputBound : ∀ sc ∈ allInputs, sc.var < start.counter := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact Nat.lt_of_lt_of_le (bounded sc old) startGrowth
          · simpa [start, suspended_counter] using suspended_bounded before.counter edge.equalities sc fresh
        have inputsAllowed : InputsAllowed allowed allInputs := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact inputs sc old
          · exact suspended_allowed allowed limit before.counter edge.equalities lower future sc fresh
        obtain ⟨children, expanded, traversal, continued⟩ := (success_bind _ _ _ _ _).mp continued
        let invariant := fun state : State Symbol Guard => Safe state ∧ start.counter ≤ state.counter ∧ ReferencesAllowed allowed state
        have childStep : ∀ entry ∈ edge.children.zipIdx, ∀ previous child next, invariant previous →
            Success (enumerateNode graph fuel (descendScs entry.2 allInputs) entry.1) previous child next → invariant next := by
          intro entry _ previous child next valid step
          have childBound : ∀ sc ∈ descendScs entry.2 allInputs, sc.var < previous.counter := by
            apply descend_bounded
            intro sc member
            exact Nat.lt_of_lt_of_le (inputBound sc member) valid.2.1
          have childAllowed := descend_allowed allowed allInputs entry.2 inputsAllowed
          obtain ⟨nextSafe, growth, _⟩ := (enumeration_safety graph fuel).1 _ entry.1 previous next child valid.1 childBound step
          exact ⟨nextSafe, Nat.le_trans valid.2.1 growth,
            ih.1 _ entry.1 previous next child valid.1 (Nat.le_trans lower (Nat.le_trans startGrowth valid.2.1))
              valid.2.2 childAllowed childBound step⟩
        have expandedValid := mapM_invariant
          (fun entry => enumerateNode graph fuel (descendScs entry.2 allInputs) entry.1) invariant edge.children.zipIdx childStep
          start expanded children ⟨startSafe, Nat.le_refl _, startValid⟩ traversal
        obtain ⟨ignored, guarded, guarding, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have guardedValid := recordResidual_allowed allowed edge.residual (.node edge.symbol children) expanded guarded expandedValid.2.2 guarding
        obtain ⟨_, same⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst after
        exact guardedValid

/-- Every stored reference avoids one protected root class. -/
def IncomingAvoid (held : Nat) (state : State Symbol Guard) : Prop :=
  ReferencesAllowed (fun uv => ¬UnionFind.SameClass state.representatives held uv) state

/-- All fresh variables avoid an allocated old class. -/
theorem fresh_separate (state : State Symbol Guard) (safe : Safe state) (held : Nat) (inside : held < state.counter) :
    ∀ uv, state.counter ≤ uv → ¬UnionFind.SameClass state.representatives held uv := by
  intro uv outside same
  have equal := outside_class state.representatives state.counter uv held safe.1.forest outside (UnionFind.sameClass_symm same)
  omega

/-- Actual node traversal retains the absence of incoming references to its protected root. -/
theorem enumerateNode_incoming (graph : Graph Symbol Guard) (fuel node held : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (inside : held < before.counter) (root : IsRoot before.representatives held)
    (incoming : IncomingAvoid held before) (inputs : Avoids before.representatives held scs)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (success : Success (enumerateNode graph fuel scs node) before fragment after) : IncomingAvoid held after := by
  have allowed := (enumeration_allowed (fun uv => ¬UnionFind.SameClass before.representatives held uv) before.counter
    (fresh_separate before safe held inside) graph fuel).1 scs node before after fragment safe (Nat.le_refl _) incoming inputs bounded success
  have frame := (enumeration_protected graph fuel).1 scs node held before after fragment safe inside root bounded inputs success
  intro value member sc listed same
  exact allowed value member sc listed ((frame.classes sc.var).mp same)

/-- Every stored suspended reference avoids all expanded slots. -/
def PendingReferences (state : State Symbol Guard) : Prop :=
  ∀ held fragment, state.values[held]? = some (.enumerated fragment) → IncomingAvoid held state

/-- A stored pending payload inherits the state's avoidance of every expanded slot. -/
theorem pending_inputs (state : State Symbol Guard) (pending : PendingReferences state)
    (uv : Nat) (node : Option Nat) (scs : List Suspended) (stored : state.values[uv]? = some (.unenumerated node scs)) :
    InputsPending state scs := by
  intro held fragment expanded
  exact pending held fragment expanded _ (List.mem_of_getElem? stored)

/-- The actual child traversal preserves pending-reference targets. -/
theorem enumerateNode_pending (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (pending : PendingReferences before) (inputs : InputsPending before scs)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (success : Success (enumerateNode graph fuel scs node) before fragment after) : PendingReferences after := by
  intro held storedFragment stored
  have original := (enumeration_origin graph fuel).1 scs node before after fragment success held storedFragment stored
  obtain ⟨inside, root⟩ := enumerated_root before safe held storedFragment original
  exact enumerateNode_incoming graph fuel node held scs before after fragment safe inside root (pending held storedFragment original)
    (inputs held storedFragment original) bounded success

/-- The initial root contains no references to expanded slots. -/
theorem initial_pending (root : Nat) : PendingReferences (initial root : State Symbol Guard) := by
  intro held fragment stored
  cases held <;> simp [initial] at stored

/-- A value-preserving class-preserving read retains a protected root's incoming-reference condition. -/
theorem incoming_read (held : Nat) (before after : State Symbol Guard) (stable : RenderStable before after)
    (incoming : IncomingAvoid held before) : IncomingAvoid held after := by
  intro value member sc listed same
  exact incoming value (by simpa [stable.values] using member) sc listed ((stable.classes held sc.var).mp same)

/-- Reads retain the avoidance of every expanded slot. -/
theorem pending_read (before after : State Symbol Guard) (stable : RenderStable before after)
    (pending : PendingReferences before) : PendingReferences after := by
  intro held fragment stored
  have original : before.values[held]? = some (.enumerated fragment) := by simpa [stable.values] using stored
  exact incoming_read held before after stable (pending held fragment original)

/-- Representative lookup retains the same values, obligations, and equivalence classes. -/
theorem representative_read (fuel uv root : Nat) (before after : State Symbol Guard) (safe : Safe before)
    (inside : uv < before.counter) (success : Success (representative fuel uv) before root after) : RenderStable before after := by
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after root).mp success
  have reached := (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1
  have rootBefore : IsRoot before.representatives found.representative := ⟨found.size, .root (UnionFind.reaches_terminal reached)⟩
  have safeAfter := (compression_safe before safe fuel uv found.representative inside rootBefore found lookup).1
  exact ⟨safeAfter, rfl, rfl, rfl, UnionFind.findRoot_classes safe.1.total lookup⟩

/-- The actual scheduler selects a root with no incoming suspended reference. -/
theorem selected_incoming (graph : Graph Symbol Guard) (fuel uv : Nat) (before after : State Symbol Guard)
    (available : Option (List Nat)) (preference : List Nat → Option Nat) (safe : Safe before)
    (success : Success (findExpandable graph fuel) before available after)
    (selected : pickNext preference available = .expand uv) : IncomingAvoid uv after := by
  cases available with
  | none => cases selected
  | some available =>
      have offered := pickNext_safe preference available uv selected
      have avoided := (findExpandable_safe graph fuel before after available uv safe.1.total safe.2 success offered).2.2.2
      intro value member
      obtain ⟨index, stored⟩ := List.mem_iff_getElem?.mp member
      cases value with
      | eliminated | enumerated _ => simp [references, InputsAllowed]
      | unenumerated node scs => exact avoided index node scs stored

/-- Writing an expanded value is safe for references when the selected root has no incoming reference. -/
theorem setValue_pending (uv : Nat) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (pending : PendingReferences before) (incoming : IncomingAvoid uv before)
    (success : Success (setValue uv (.enumerated fragment)) before () after) : PendingReferences after := by
  have stateSame := (modify_success _ before after).mp success
  intro held storedFragment stored
  have oldIncoming : IncomingAvoid held before := by
    by_cases same : held = uv
    · simpa [same] using incoming
    · apply pending held storedFragment
      simpa [stateSame, Ne.symm same] using stored
  have allowed := setValue_allowed (fun other => ¬UnionFind.SameClass before.representatives held other)
    uv (.enumerated fragment) before after oldIncoming (by simp [references, InputsAllowed]) success
  simpa [IncomingAvoid, stateSame] using allowed

/-- The actual selected-slot expansion preserves pending targets for every suspended reference. -/
theorem enumerateOut_pending (graph : Graph Symbol Guard) (fuel uv : Nat) (before after : State Symbol Guard)
    (fragment : Fragment Symbol) (ready : Ready uv before) (pending : PendingReferences before) (incoming : IncomingAvoid uv before)
    (success : Success (enumerateOut graph fuel uv) before fragment after) : PendingReferences after := by
  unfold enumerateOut at success
  obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readSafe, readCounter, readFrame, stored⟩ := getValue_root (fuel + 1) uv before readState value ready.safe ready.inside ready.root reading
  have readStable := (getValue_storage (fuel + 1) uv before readState value ready.safe ready.inside reading).1
  have readPending := pending_read before readState readStable pending
  have readIncoming := incoming_read uv before readState readStable incoming
  cases value with
  | eliminated | enumerated _ => exact (reject_unsuccessful readState after fragment continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful readState after fragment continued).elim
      | some node =>
          obtain ⟨selected, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨selectedSame, resolvedSafe, resolvedCounter, resolvedFrame⟩ := representative_root (fuel + 1) uv selected
            readState resolved readSafe (by simpa [readCounter] using ready.inside) readFrame.root resolution
          subst selected
          have resolvedStable := representative_read (fuel + 1) uv uv readState resolved readSafe
            (by simpa [readCounter] using ready.inside) resolution
          have resolvedPending := pending_read readState resolved resolvedStable readPending
          have resolvedIncoming := incoming_read uv readState resolved resolvedStable readIncoming
          have resolvedStored : resolved.values[uv]? = some (.unenumerated (some node) scs) := resolvedFrame.value ▸ stored
          have bounded : ∀ sc ∈ scs, sc.var < resolved.counter := resolvedSafe.1.values _ (List.mem_of_getElem? resolvedStored)
          obtain ⟨current, currentState, currentRead, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨currentSame, currentStateSame⟩ := (get_success resolved currentState current).mp currentRead
          subst current
          subst currentState
          obtain ⟨ignored, started, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ resolved started).mp bookkeeping
          obtain ⟨produced, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
          let ancestry := match graph.node node with
            | .recursive _ => (recursionKey node scs :: resolved.recursionAncestry uv).eraseDups
            | _ => resolved.recursionAncestry uv
          let start := {resolved with expansionAncestry := ancestry}
          have startSafe : Safe start := ancestry_safe resolved ancestry resolvedSafe
          have expandedPending := enumerateNode_pending graph fuel _ scs start expanded produced startSafe resolvedPending
            (pending_inputs start resolvedPending uv (some node) scs resolvedStored) bounded expansion
          have expandedIncoming := enumerateNode_incoming graph fuel _ uv scs start expanded produced startSafe
            (by simpa [start, resolvedCounter, readCounter] using ready.inside) resolvedFrame.root resolvedIncoming
            (resolvedIncoming _ (List.mem_of_getElem? resolvedStored)) bounded expansion
          obtain ⟨ignored, cleared, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ expanded cleared).mp bookkeeping
          obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          have writtenPending := setValue_pending uv produced {expanded with expansionAncestry := []} written expandedPending expandedIncoming writing
          obtain ⟨_, same⟩ := (success_pure produced fragment written after).mp final
          subst after
          exact writtenPending

/-- The actual scheduler scan retains pending-reference targets. -/
theorem findExpandable_pending (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) (total : UnionFind.Total before.representatives) (pending : PendingReferences before)
    (success : Success (findExpandable graph fuel) before result after) : PendingReferences after := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  have scan := (findExpandable_exact graph fuel roots before after result paths success).1
  intro held fragment stored value member sc listed same
  have original : before.values[held]? = some (.enumerated fragment) := by simpa [scan.values] using stored
  apply pending held fragment original value (by simpa [scan.values] using member) sc listed
  exact (class_iff before.representatives roots paths held sc.var).mpr
    ((class_iff after.representatives roots scan.roots held sc.var).mp same)

/-- The complete-graph caller retains pending-reference targets from its actual input state. -/
theorem enumerateFully_pending (graph : Graph Symbol Guard) (complete : CompleteGraph graph)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle)
    (fuel : Nat) (oracleState : OracleState) (before after : State Symbol Guard) (safe : Safe before) (pending : PendingReferences before)
    (success : Success (enumerateFully graph order oracle fuel oracleState) before () after) : PendingReferences after := by
  induction fuel generalizing oracleState before with
  | zero => exact (success_failure .fuelExhausted before after () success).elim
  | succ fuel ih =>
      rw [fully_action] at success
      obtain ⟨available, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨scannedSafe, _⟩ := findExpandable_safety graph (fuel + 1) before scanned available safe scanning
      have scannedPending := findExpandable_pending graph (fuel + 1) before scanned available safe.1.total pending scanning
      cases selected : pickNext (order oracleState) available with
      | done =>
          simp only [selected] at continued
          obtain ⟨_, same⟩ := (success_pure () () scanned after).mp continued
          subst after
          exact scannedPending
      | stuck =>
          simp only [selected] at continued
          exact (reject_unsuccessful scanned after () continued).elim
      | expand uv =>
          have ready := findExpandable_ready graph (fuel + 1) uv before scanned available (order oracleState) safe scanning selected
          have incoming := selected_incoming graph (fuel + 1) uv before scanned available (order oracleState) safe scanning selected
          simp only [selected] at continued
          obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨readReady, _⟩ := getValue_ready (fuel + 1) uv scanned readState value ready reading
          have stable := (getValue_storage (fuel + 1) uv scanned readState value scannedSafe ready.inside reading).1
          have readPending := pending_read scanned readState stable scannedPending
          have readIncoming := incoming_read uv scanned readState stable incoming
          cases value with
          | eliminated | enumerated _ => exact (reject_unsuccessful readState after () continued).elim
          | unenumerated node scs =>
              cases node with
              | none => exact (reject_unsuccessful readState after () continued).elim
              | some node =>
                  obtain ⟨repeated, checked, checking, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  obtain ⟨repeatedSame, checkedSame⟩ := checkRepeated_complete graph complete (fuel + 1) uv node scs readState checked repeated checking
                  subst repeated
                  subst checked
                  obtain ⟨⟨beforeReject, beforeState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have observedSame := observer oracleState uv (.inr node) readState _ observed observation
                  subst observed
                  obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  cases ignored
                  obtain ⟨_, same⟩ := (require_success (!beforeReject) readState accepted).mp acceptance
                  subst accepted
                  obtain ⟨fragment, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have expandedSafe := (enumerateOut_safe graph (fuel + 1) uv readState expanded fragment
                    readReady.safe readReady.inside readReady.root readReady.avoids expansion).1
                  have expandedPending := enumerateOut_pending graph (fuel + 1) uv readState expanded fragment readReady readPending readIncoming expansion
                  obtain ⟨⟨afterReject, afterState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have observedSame := observer beforeState uv (.inl fragment) expanded _ observed observation
                  subst observed
                  obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  cases ignored
                  obtain ⟨_, same⟩ := (require_success (!afterReject) expanded accepted).mp acceptance
                  subst accepted
                  exact ih afterState expanded expandedSafe expandedPending continued

/-- The initialized complete caller establishes pending-reference targets. -/
theorem initialized_pending (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (fuel root : Nat)
    (after : State Symbol Guard)
    (success : Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) (initial root) () after) : PendingReferences after :=
  enumerateFully_pending graph complete (fun _ _ => none) noPruning noPruning_readOnly fuel () (initial root) after
    ⟨initial_storage root, initial_live root⟩ (initial_pending root) success

end MicroCFTA.EnumerationReferences
