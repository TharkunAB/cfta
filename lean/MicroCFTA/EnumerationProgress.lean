import MicroCFTA.EnumerationSoundness

/-!
# Strict suspended dependencies

Stored pending constraints refer to proper descendants. A finite complete
assignment therefore rules out a scheduler result in which all work is blocked.
-/

namespace MicroCFTA.EnumerationProgress
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- A stored pending trie contains at least one proper descendant path. -/
def ProperTrie (trie : EqualityTrie.Trie) : Prop :=
  EqualityTrie.Valid trie ∧ EqualityTrie.isEmpty trie = false ∧ EqualityTrie.isTerminal trie = false

/-- Pure equality slots carry no paths; graph slots carry only proper pending paths. -/
def ProperValue : UVarValue Symbol → Prop
  | .unenumerated none scs => scs = []
  | .unenumerated (some _) scs => ∀ sc ∈ scs, ProperTrie sc.trie
  | _ => True

/-- All stored pending slots meet the source scheduler's strict-path invariant. -/
def ProperState (state : State Symbol Guard) : Prop := ∀ value ∈ state.values, ProperValue value

/-- Inherited inputs contain canonical nonempty tries, including terminals. -/
def ProperInputs (scs : List Suspended) : Prop :=
  ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧ EqualityTrie.isEmpty sc.trie = false

/-- Every stored pending input is a canonical nonempty trie. -/
theorem proper_inputs (value : UVarValue Symbol) (proper : ProperValue value) : ProperInputs (references value) := by
  cases value with
  | eliminated | enumerated _ => simp [references, ProperInputs]
  | unenumerated node scs =>
      cases node with
      | none => simp [ProperValue] at proper; simp [references, proper, ProperInputs]
      | some node => exact fun sc member => ⟨(proper sc member).1, (proper sc member).2.1⟩

/-- Filtering reached terminals leaves only proper descendant constraints. -/
theorem proper_below (scs : List Suspended) (inputs : ProperInputs scs) :
    ∀ sc ∈ scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie), ProperTrie sc.trie := by
  intro sc member
  obtain ⟨present, below⟩ := List.mem_filter.mp member
  exact ⟨(inputs sc present).1, (inputs sc present).2, by simpa using below⟩

/-- Child descent supplies canonical nonempty inputs. -/
theorem descend_proper (scs : List Suspended) (index : Nat) (valid : ValidSuspended scs) :
    ProperInputs (descendScs index scs) := by
  intro sc member
  have canonical := descend_valid scs index valid sc member
  have nonempty := (List.mem_filter.mp member).2
  exact ⟨canonical, by simpa using nonempty⟩

/-- The initial pending root has no suspended dependencies. -/
theorem initial_proper (root : Nat) : ProperState (initial root : State Symbol Guard) := by
  simp [ProperState, initial, ProperValue]

/-- Updating one stored slot preserves the pending-path invariant. -/
theorem setValue_proper (uv : Nat) (value : UVarValue Symbol) (before after : State Symbol Guard)
    (proper : ProperState before) (payload : ProperValue value)
    (success : Success (setValue uv value) before () after) : ProperState after := by
  obtain rfl := (modify_success _ before after).mp success
  intro stored member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact proper stored old
  · simpa [same] using payload

/-- Raw reads retain proper pending paths and expose their payload invariant. -/
theorem rawValue_proper (uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (proper : ProperState before) (success : Success (rawValue uv) before value after) :
    ProperState after ∧ ProperValue value := by
  obtain ⟨stored, same⟩ := (rawValue_success uv before after value).mp success
  subst after
  exact ⟨proper, proper value (List.mem_of_getElem? stored)⟩

/-- Representative lookup changes no pending payload. -/
theorem representative_proper (fuel uv root : Nat) (before after : State Symbol Guard)
    (proper : ProperState before) (success : Success (representative fuel uv) before root after) : ProperState after := by
  obtain ⟨found, _, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact proper

/-- Union changes no pending payload. -/
theorem unionVariables_proper (fuel left right : Nat) (before after : State Symbol Guard)
    (proper : ProperState before) (success : Success (unionVariables fuel left right) before () after) : ProperState after := by
  obtain ⟨forest, _, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact proper

/-- Intersecting proper pending payloads retains empty pure slots and proper graph paths. -/
theorem intersection_proper (graph : Graph Symbol Guard) (left right merged : UVarValue Symbol)
    (leftProper : ProperValue left) (rightProper : ProperValue right)
    (success : intersectValues graph left right = some merged) : ProperValue merged := by
  cases left <;> cases right <;> simp only [intersectValues] at success
  all_goals try cases success
  rename_i left leftScs right rightScs
  cases left <;> cases right
  · simp only [ProperValue] at leftProper rightProper ⊢
    simp [leftProper, rightProper]
  · simp only [ProperValue] at leftProper rightProper ⊢
    simpa [leftProper] using rightProper
  · simp only [ProperValue] at leftProper rightProper ⊢
    simpa [rightProper] using leftProper
  · intro sc member
    rcases List.mem_append.mp member with left | right
    · exact leftProper sc left
    · exact rightProper sc right

/-- Actual assimilation preserves the proper pending-path invariant. -/
theorem assimilate_proper (graph : Graph Symbol Guard) (target source : Nat) (before after : State Symbol Guard)
    (proper : ProperState before) (success : Success (EnumerationState.assimilate graph target source) before () after) : ProperState after := by
  by_cases same : target = source
  · subst source
    have unchanged : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    simpa [unchanged] using proper
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, readSource, readingSource, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨sourceProper, sourcePayload⟩ := rawValue_proper source before readSource sourceValue proper readingSource
    cases sourceValue with
    | eliminated =>
        obtain ⟨_, same⟩ := (success_pure () () readSource after).mp continued
        subst after
        exact sourceProper
    | enumerated fragment =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        exact (success_failure .invalidIntersection readTarget after () continued).elim
    | unenumerated node scs =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨targetProper, targetPayload⟩ := rawValue_proper target readSource readTarget targetValue sourceProper readingTarget
        cases intersection : intersectValues graph (.unenumerated node scs) targetValue with
        | none =>
            simp only [intersection] at continued
            exact (success_failure .invalidIntersection readTarget after () continued).elim
        | some merged =>
            have mergedProper := intersection_proper graph (.unenumerated node scs) targetValue merged sourcePayload targetPayload intersection
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            obtain ⟨_, same⟩ := (require_success _ readTarget checked).mp required
            subst checked
            obtain ⟨ignored, targetWritten, targetWrite, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have targetWrittenProper := setValue_proper target merged readTarget targetWritten targetProper mergedProper targetWrite
            obtain ⟨ignored, sourceWritten, sourceWrite, final⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have sourceWrittenProper := setValue_proper source .eliminated targetWritten sourceWritten targetWrittenProper trivial sourceWrite
            obtain rfl := (modify_success _ sourceWritten after).mp final
            exact sourceWrittenProper

/-- Node restriction stores only its proper descendant constraints. -/
theorem mergeNode_proper (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (proper : ProperState before) (inputs : ∀ sc ∈ scs, ProperTrie sc.trie)
    (success : Success (mergeNode graph fuel uv node scs) before () after) : ProperState after := by
  unfold mergeNode at success
  obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp success
  have resolvedProper := representative_proper fuel uv root before resolved proper resolution
  obtain ⟨previous, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨readProper, payloadProper⟩ := rawValue_proper root resolved readState previous resolvedProper reading
  cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
  | none =>
      simp only [intersection] at continued
      exact (success_failure .invalidIntersection readState after () continued).elim
  | some merged =>
      have mergedProper := intersection_proper graph (.unenumerated (some node) scs) previous merged inputs payloadProper intersection
      simp only [intersection] at continued
      obtain ⟨ignored, written, writing, continued⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      have writtenProper := setValue_proper root merged readState written readProper mergedProper writing
      obtain ⟨ignored, inherited, inheriting, final⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain rfl := (modify_success _ written inherited).mp inheriting
      obtain ⟨_, same⟩ := (require_success _ _ after).mp final
      subst after
      exact writtenProper

/-- Every successful complete terminal merge retains proper stored paths. -/
theorem mergeTerminal_proper (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (proper : ProperState before)
    (success : Success (mergeTerminal graph fuel first rest) before target after) : ProperState after := by
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedProper := mapM_invariant (fun sc => representative fuel sc.var) ProperState (first :: rest)
    (fun sc _ previous result next proper step => representative_proper fuel sc.var result previous next proper step)
    before scanned recorded proper scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedProper := forM_invariant (fun sc => unionVariables fuel first.var sc.var) ProperState rest
    (fun sc _ previous next proper step => unionVariables_proper fuel first.var sc.var previous next proper step)
    scanned united scannedProper unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedProper := representative_proper fuel first.var winner united resolved unitedProper resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have assimilatedProper := forM_invariant (EnumerationState.assimilate graph winner) ProperState recorded
    (fun source _ previous next proper step => assimilate_proper graph winner source previous next proper step)
    resolved assimilated resolvedProper assimilation
  obtain ⟨_, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst after
  exact assimilatedProper

/-- The terminal node branch stores only the inherited proper descendant paths. -/
theorem enumerateNode_terminal_proper (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (first : Suspended) (rest : List Suspended) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (proper : ProperState before) (inputs : ProperInputs scs) (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) : ProperState after := by
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, merging, continued⟩ := (success_bind _ _ _ _ _).mp success
  have mergedProper := mergeTerminal_proper graph (fuel + 1) first rest before merged root proper merging
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have restrictedProper := mergeNode_proper graph (fuel + 1) root node _ merged restricted mergedProper (proper_below scs inputs) restriction
  obtain ⟨_, same⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst after
  exact restrictedProper

/-- A fresh graph or equality variable starts with no suspended paths. -/
theorem allocation_proper (node : Option Nat) (state : State Symbol Guard) (proper : ProperState state) :
    ProperState (allocated node state) := by
  intro value member
  rcases List.mem_append.mp member with old | fresh
  · exact proper value old
  · have same : value = .unenumerated node [] := by simpa using fresh
    subst value
    cases node <;> simp [ProperValue]

/-- Repeated equality allocation preserves all prior proper paths. -/
theorem suspension_proper (count : Nat) (state : State Symbol Guard) (proper : ProperState state) :
    ProperState (suspendedState count state) := by
  induction count generalizing state with
  | zero => exact proper
  | succ count ih => exact ih (allocated none state) (allocation_proper none state proper)

/-- Residual recording changes no pending slot. -/
theorem recordResidual_proper (residual : Option Guard) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (proper : ProperState before) (success : Success (recordResidual residual fragment) before () after) : ProperState after := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact proper
  | some guard =>
      obtain rfl := (modify_success _ before after).mp success
      exact proper

/-- The actual mutual traversal retains the scheduler's strict pending-path invariant. -/
theorem enumeration_proper (graph : Graph Symbol Guard)
    (graphValid : ∀ node edges, graph.node node = .alternatives edges → ∀ edge ∈ edges, ValidEdge edge)
    (fuel : Nat) :
    (∀ scs node (before after : State Symbol Guard) fragment, ProperState before → ProperInputs scs →
      Success (enumerateNode graph fuel scs node) before fragment after → ProperState after) ∧
    (∀ scs edge (before after : State Symbol Guard) fragment, ProperState before → ProperInputs scs → ValidEdge edge →
      Success (enumerateEdge graph fuel scs edge) before fragment after → ProperState after) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node before after fragment _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge before after fragment _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node before after fragment proper inputs success
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | alternatives edges | recursive body | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                exact enumerateNode_terminal_proper graph fuel node scs first rest before after fragment proper inputs
                  (by simp [view]) terminal success
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨member, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact ih.2 scs edge before after fragment proper inputs (graphValid node edges view edge member) continued)
                | (obtain ⟨uv, middle, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
                   have exactState : uv = before.counter ∧ middle = allocated (some node) before := by
                     simpa [Success, allocate_exact, ExceptT.run] using allocation
                   obtain ⟨uvSame, middleSame⟩ := exactState
                   subst uv
                   subst middle
                   obtain ⟨_, same⟩ := (success_pure (.hole before.counter) fragment (allocated (some node) before) after).mp final
                   subst after
                   exact allocation_proper (some node) before proper)
      · intro scs edge before after fragment proper inputs edgeValid success
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
        have startProper := suspension_proper edge.equalities.length before proper
        have inputsValid : ValidSuspended (scs ++ suspendedVars before.counter edge.equalities) := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact (inputs sc old).1
          · have member : sc.trie ∈ edge.equalities := by
              rw [← suspendedVars_tries before.counter edge.equalities]
              exact List.mem_map.mpr ⟨sc, fresh, rfl⟩
            exact edgeValid.1 sc.trie member
        obtain ⟨children, expanded, traversal, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have expandedProper := mapM_invariant
          (fun entry => enumerateNode graph fuel (descendScs entry.2 (scs ++ suspendedVars before.counter edge.equalities)) entry.1)
          ProperState edge.children.zipIdx
          (fun entry _ previous child next proper step => ih.1 _ entry.1 previous next child proper
            (descend_proper _ entry.2 inputsValid) step)
          _ expanded children startProper traversal
        obtain ⟨ignored, guarded, guarding, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have guardedProper := recordResidual_proper edge.residual (.node edge.symbol children) expanded guarded expandedProper guarding
        obtain ⟨_, same⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst after
        exact guardedProper

/-- Every proper stored state has canonical suspended tries. -/
theorem proper_canonical (state : State Symbol Guard) (proper : ProperState state) : Canonical state := by
  intro value member sc reference
  exact (proper_inputs value (proper value member) sc reference).1

/-- Representative reads retain proper pending slots. -/
theorem getValue_proper (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (proper : ProperState before) (success : Success (getValue fuel uv) before value after) :
    ProperState after ∧ ProperValue value := by
  obtain ⟨found, _, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  exact ⟨proper, proper value (List.mem_of_getElem? stored)⟩

/-- The complete selected-slot expansion retains proper pending slots. -/
theorem enumerateOut_proper (graph : Graph Symbol Guard)
    (graphValid : ∀ node edges, graph.node node = .alternatives edges → ∀ edge ∈ edges, ValidEdge edge)
    (fuel uv : Nat) (before after : State Symbol Guard) (fragment : Fragment Symbol) (proper : ProperState before)
    (success : Success (enumerateOut graph fuel uv) before fragment after) : ProperState after := by
  unfold enumerateOut at success
  obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readProper, payloadProper⟩ := getValue_proper (fuel + 1) uv before readState value proper reading
  cases value with
  | eliminated | enumerated _ => exact (reject_unsuccessful readState after fragment continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful readState after fragment continued).elim
      | some node =>
          obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have resolvedProper := representative_proper (fuel + 1) uv root readState resolved readProper resolution
          obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨currentSame, stateSame⟩ := (get_success resolved currentState current).mp reading
          subst current
          subst currentState
          obtain ⟨ignored, started, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ resolved started).mp bookkeeping
          obtain ⟨produced, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have expandedProper := (enumeration_proper graph graphValid fuel).1 scs _
            {resolved with expansionAncestry := match graph.node node with
              | .recursive _ => (recursionKey node scs :: resolved.recursionAncestry root).eraseDups
              | _ => resolved.recursionAncestry root}
            expanded produced resolvedProper (proper_inputs _ payloadProper) expansion
          obtain ⟨ignored, cleared, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ expanded cleared).mp bookkeeping
          obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          have writtenProper := setValue_proper root (.enumerated produced) {expanded with expansionAncestry := []} written expandedProper trivial writing
          obtain ⟨_, same⟩ := (success_pure produced fragment written after).mp final
          subst after
          exact writtenProper

/-- A scheduler scan retains all proper pending paths. -/
theorem findExpandable_proper (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) (total : UnionFind.Total before.representatives) (proper : ProperState before)
    (success : Success (findExpandable graph fuel) before result after) : ProperState after := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  have values := (findExpandable_exact graph fuel roots before after result paths success).1.values
  intro value member
  exact proper value (by simpa [values] using member)

/-- The full complete-graph caller retains proper pending paths at every successful return. -/
theorem enumerateFully_proper (graph : Graph Symbol Guard) (complete : CompleteGraph graph)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle)
    (fuel : Nat) (oracleState : OracleState) (before after : State Symbol Guard) (safe : Safe before) (proper : ProperState before)
    (success : Success (enumerateFully graph order oracle fuel oracleState) before () after) : ProperState after := by
  induction fuel generalizing oracleState before with
  | zero => exact (success_failure .fuelExhausted before after () success).elim
  | succ fuel ih =>
      rw [fully_action] at success
      obtain ⟨available, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨scannedSafe, _⟩ := findExpandable_safety graph (fuel + 1) before scanned available safe scanning
      have scannedProper := findExpandable_proper graph (fuel + 1) before scanned available safe.1.total proper scanning
      cases selected : pickNext (order oracleState) available with
      | done =>
          simp only [selected] at continued
          obtain ⟨_, same⟩ := (success_pure () () scanned after).mp continued
          subst after
          exact scannedProper
      | stuck =>
          simp only [selected] at continued
          exact (reject_unsuccessful scanned after () continued).elim
      | expand uv =>
          have ready := findExpandable_ready graph (fuel + 1) uv before scanned available (order oracleState) safe scanning selected
          simp only [selected] at continued
          obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨readReady, _⟩ := getValue_ready (fuel + 1) uv scanned readState value ready reading
          obtain ⟨readProper, _⟩ := getValue_proper (fuel + 1) uv scanned readState value scannedProper reading
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
                  have expandedProper := enumerateOut_proper graph complete.2 (fuel + 1) uv readState expanded fragment readProper expansion
                  obtain ⟨⟨afterReject, afterState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have observedSame := observer beforeState uv (.inl fragment) expanded _ observed observation
                  subst observed
                  obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  cases ignored
                  obtain ⟨_, same⟩ := (require_success (!afterReject) expanded accepted).mp acceptance
                  subst accepted
                  exact ih afterState expanded expandedSafe expandedProper continued

/-- A successful initialized complete caller establishes the strict pending-path invariant. -/
theorem initialized_proper (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (fuel root : Nat)
    (after : State Symbol Guard)
    (success : Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) (initial root) () after) : ProperState after :=
  enumerateFully_proper graph complete (fun _ _ => none) noPruning noPruning_readOnly fuel () (initial root) after
    ⟨initial_storage root, initial_live root⟩ (initial_proper root) success

/-- At complete-graph termination every remaining pending slot is a free equality variable. -/
theorem finished_free (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (state : State Symbol Guard)
    (proper : ProperState state) (finished : Finished graph state) (uv : Nat) (node : Option Nat) (scs : List Suspended)
    (stored : state.values[uv]? = some (.unenumerated node scs)) : node = none ∧ scs = [] := by
  cases node with
  | none => exact ⟨rfl, proper _ (List.mem_of_getElem? stored)⟩
  | some node =>
      obtain ⟨_, body, recursive⟩ := finished_pending graph state finished uv node scs stored
      exact (complete.1 node body recursive).elim

/-- Every proper stored trie supplies a nonempty represented path. -/
theorem proper_path (trie : EqualityTrie.Trie) (proper : ProperTrie trie) :
    ∃ path ∈ EqualityTrie.fromPathTrie trie, path ≠ [] := by
  have nonempty : trie ≠ .empty := by intro same; simp [ProperTrie, same, EqualityTrie.isEmpty] at proper
  obtain ⟨path, member⟩ := EqualityTrie.valid_has_path trie proper.1 nonempty
  refine ⟨path, member, ?_⟩
  intro same
  subst path
  have terminal := (EqualityTrie.nil_mem trie).mp member
  simp [ProperTrie, terminal, EqualityTrie.isTerminal] at proper

/-- A stored reference necessarily belongs to an eligible graph slot. -/
theorem referenced_candidate (graph : Graph Symbol Guard) (value : UVarValue Symbol) (sc : Suspended)
    (proper : ProperValue value) (member : sc ∈ references value) : candidate graph value = true ∧ ProperTrie sc.trie := by
  cases value with
  | eliminated | enumerated _ => cases member
  | unenumerated node scs =>
      cases node with
      | none => simp [ProperValue] at proper; simp [references, proper] at member
      | some node =>
          have nonempty : scs ≠ [] := by intro same; simp [references, same] at member
          refine ⟨?_, proper sc member⟩
          cases view : graph.node node <;> simp [candidate, view, nonempty]

/-- An actual blocked scheduler result contradicts a complete finite assignment to proper pending slots. -/
theorem findExpandable_not_stuck (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol) (fuel : Nat)
    (before after : State Symbol Guard) (safe : Safe before) (proper : ProperState before)
    (satisfies : Satisfies language meaning assignment before)
    (success : Success (findExpandable graph fuel) before (some []) after) : False := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives safe.1.total
  obtain ⟨_, result⟩ := findExpandable_exact graph fuel roots before after (some []) paths success
  let summary := before.values.zipIdx.foldl (collectPure graph roots) ([], [])
  have offeredEmpty : offered summary.1 summary.2 = some [] := result.symm
  have nonempty : summary.1 ≠ [] := by
    intro empty
    simp [offered, empty] at offeredEmpty
  have blocked : ∀ uv ∈ summary.1, uv ∈ summary.2 := by
    intro uv candidateMember
    have filtered : summary.1.filter (fun uv => !(uv ∈ summary.2)) = [] := by
      simpa [offered, nonempty] using offeredEmpty
    by_cases member : uv ∈ summary.2
    · exact member
    · have available : uv ∈ summary.1.filter (fun uv => !(uv ∈ summary.2)) := List.mem_filter.mpr ⟨candidateMember, by simp [member]⟩
      simp [filtered] at available
  apply strict_dependency_stuck_impossible summary.1 nonempty assignment
  intro target targetMember
  have targetBlocked := blocked target targetMember
  obtain ⟨entry, present, sc, scMember, sameRoot⟩ :=
    ((blocked_exact graph roots before.values.zipIdx ([], []) target).mp targetBlocked).resolve_left (by simp)
  have stored : before.values[entry.2]? = some entry.1 := List.mem_zipIdx_iff_getElem?.mp present
  obtain ⟨sourceCandidate, properTrie⟩ := referenced_candidate graph entry.1 sc (proper entry.1 (List.mem_of_getElem? stored)) scMember
  have sourceMember : entry.2 ∈ summary.1 := (candidates_exact graph roots before.values.zipIdx ([], []) entry.2).mpr
    (Or.inr ⟨entry, present, rfl, sourceCandidate⟩)
  obtain ⟨path, pathMember, pathProper⟩ := proper_path sc.trie properTrie
  have storedHolds := satisfies.1.2 entry.2
  rw [heap, stored, Option.getD_some] at storedHolds
  have suspended : Suspended.Holds assignment (assignment entry.2) sc := by
    obtain ⟨value, index⟩ := entry
    cases value with
    | eliminated | enumerated _ => cases scMember
    | unenumerated node scs =>
        exact storedHolds.2 _ (List.mem_map.mpr ⟨sc, scMember, rfl⟩)
  obtain ⟨size, reached⟩ := paths sc.var
  have assigned : assignment sc.var = assignment target := by
    rw [← sameRoot]
    exact satisfies.1.1 sc.var (roots sc.var) (UnionFind.sameClass_root reached)
  exact ⟨entry.2, sourceMember, path, pathProper, by simpa [assigned] using suspended path pathMember⟩

end MicroCFTA.EnumerationProgress
