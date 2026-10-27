import MicroCFTA.EnumerationFrame

/-!
# Canonical suspended tries in reachable enumeration states

The source edge constructor supplies valid tries. The enumeration actions
retain this representation through allocation, intersection, and descent.
-/

namespace MicroCFTA.EnumerationValidity
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Every stored suspended constraint uses a canonical trie. -/
def Canonical (state : State Symbol Guard) : Prop :=
  ∀ value ∈ state.values, ValidSuspended (references value)

/-- The initialized root has no suspended constraints. -/
theorem initial_canonical (root : Nat) : Canonical (initial root : State Symbol Guard) := by
  simp [Canonical, initial, references, ValidSuspended]

/-- Replacing one slot preserves canonical tries when its new payload is canonical. -/
theorem set_canonical (uv : Nat) (value : UVarValue Symbol) (state : State Symbol Guard)
    (valid : Canonical state) (newValue : ValidSuspended (references value)) :
    Canonical {state with values := state.values.set uv value} := by
  intro stored member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid stored old
  · simpa [same] using newValue

/-- A successful source slot write preserves canonical tries. -/
theorem setValue_canonical (uv : Nat) (value : UVarValue Symbol) (before after : State Symbol Guard)
    (valid : Canonical before) (newValue : ValidSuspended (references value))
    (success : Success (setValue uv value) before () after) : Canonical after := by
  obtain rfl := (modify_success _ before after).mp success
  exact set_canonical uv value before valid newValue

/-- A raw read retains every trie and exposes a canonical payload. -/
theorem rawValue_canonical (uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (valid : Canonical before) (success : Success (rawValue uv) before value after) :
    Canonical after ∧ ValidSuspended (references value) := by
  obtain ⟨stored, same⟩ := (rawValue_success uv before after value).mp success
  subst after
  exact ⟨valid, valid value (List.mem_of_getElem? stored)⟩

/-- Representative compression changes no stored trie. -/
theorem representative_canonical (fuel uv root : Nat) (before after : State Symbol Guard)
    (valid : Canonical before) (success : Success (representative fuel uv) before root after) : Canonical after := by
  obtain ⟨found, _, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact valid

/-- A representative read exposes canonical suspended constraints. -/
theorem getValue_canonical (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (valid : Canonical before) (success : Success (getValue fuel uv) before value after) :
    Canonical after ∧ ValidSuspended (references value) := by
  obtain ⟨found, _, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  exact ⟨valid, valid value (List.mem_of_getElem? stored)⟩

/-- Pending-slot intersection concatenates only canonical suspended constraints. -/
theorem intersection_canonical (graph : Graph Symbol Guard) (left right merged : UVarValue Symbol)
    (leftValid : ValidSuspended (references left)) (rightValid : ValidSuspended (references right))
    (success : intersectValues graph left right = some merged) : ValidSuspended (references merged) := by
  cases left <;> cases right <;> simp only [intersectValues] at success
  all_goals try cases success
  intro sc member
  rcases List.mem_append.mp member with left | right
  · exact leftValid sc left
  · exact rightValid sc right

/-- Actual assimilation preserves canonical tries on every successful source branch. -/
theorem assimilate_canonical (graph : Graph Symbol Guard) (target source : Nat) (before after : State Symbol Guard)
    (valid : Canonical before) (success : Success (EnumerationState.assimilate graph target source) before () after) : Canonical after := by
  by_cases same : target = source
  · subst source
    have unchanged : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    simpa [unchanged] using valid
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, readSource, readingSource, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨sourceValid, sourcePayload⟩ := rawValue_canonical source before readSource sourceValue valid readingSource
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
        obtain ⟨targetValid, targetPayload⟩ := rawValue_canonical target readSource readTarget targetValue sourceValid readingTarget
        cases intersection : intersectValues graph (.unenumerated node scs) targetValue with
        | none =>
            simp only [intersection] at continued
            exact (success_failure .invalidIntersection readTarget after () continued).elim
        | some merged =>
            have mergedValid := intersection_canonical graph (.unenumerated node scs) targetValue merged sourcePayload targetPayload intersection
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            obtain ⟨_, same⟩ := (require_success _ readTarget checked).mp required
            subst checked
            obtain ⟨ignored, targetWritten, targetWrite, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have targetWrittenValid := setValue_canonical target merged readTarget targetWritten targetValid mergedValid targetWrite
            obtain ⟨ignored, sourceWritten, sourceWrite, final⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have sourceWrittenValid := setValue_canonical source .eliminated targetWritten sourceWritten targetWrittenValid
              (by simp [references, ValidSuspended]) sourceWrite
            obtain rfl := (modify_success _ sourceWritten after).mp final
            exact sourceWrittenValid

/-- Actual node restriction preserves canonical input and stored suspended tries. -/
theorem mergeNode_canonical (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (valid : Canonical before) (inputs : ValidSuspended scs)
    (success : Success (mergeNode graph fuel uv node scs) before () after) : Canonical after := by
  unfold mergeNode at success
  obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp success
  have resolvedValid := representative_canonical fuel uv root before resolved valid resolution
  obtain ⟨previous, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨readValid, payloadValid⟩ := rawValue_canonical root resolved readState previous resolvedValid reading
  cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
  | none =>
      simp only [intersection] at continued
      exact (success_failure .invalidIntersection readState after () continued).elim
  | some merged =>
      have mergedValid := intersection_canonical graph (.unenumerated (some node) scs) previous merged inputs payloadValid intersection
      simp only [intersection] at continued
      obtain ⟨ignored, written, writing, continued⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      have writtenValid := setValue_canonical root merged readState written readValid mergedValid writing
      obtain ⟨ignored, inherited, inheriting, final⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain rfl := (modify_success _ written inherited).mp inheriting
      obtain ⟨_, same⟩ := (require_success _ _ after).mp final
      subst after
      exact writtenValid

/-- Union changes no payload and retains every stored trie. -/
theorem unionVariables_canonical (fuel left right : Nat) (before after : State Symbol Guard)
    (valid : Canonical before) (success : Success (unionVariables fuel left right) before () after) : Canonical after := by
  obtain ⟨forest, _, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact valid

/-- The actual complete terminal merge preserves canonical stored constraints. -/
theorem mergeTerminal_canonical (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (valid : Canonical before)
    (success : Success (mergeTerminal graph fuel first rest) before target after) : Canonical after := by
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedValid := mapM_invariant (fun sc => representative fuel sc.var) Canonical (first :: rest)
    (fun sc _ previous result next valid step => representative_canonical fuel sc.var result previous next valid step)
    before scanned recorded valid scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedValid := forM_invariant (fun sc => unionVariables fuel first.var sc.var) Canonical rest
    (fun sc _ previous next valid step => unionVariables_canonical fuel first.var sc.var previous next valid step)
    scanned united scannedValid unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedValid := representative_canonical fuel first.var winner united resolved unitedValid resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have assimilatedValid := forM_invariant (EnumerationState.assimilate graph winner) Canonical recorded
    (fun source _ previous next valid step => assimilate_canonical graph winner source previous next valid step)
    resolved assimilated resolvedValid assimilation
  obtain ⟨_, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst after
  exact assimilatedValid

/-- The terminal node branch combines only canonical stored and inherited tries. -/
theorem enumerateNode_terminal_canonical (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (first : Suspended) (rest : List Suspended) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (valid : Canonical before) (inputs : ValidSuspended scs) (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) : Canonical after := by
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, merging, continued⟩ := (success_bind _ _ _ _ _).mp success
  have mergedValid := mergeTerminal_canonical graph (fuel + 1) first rest before merged root valid merging
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have restrictedValid := mergeNode_canonical graph (fuel + 1) root node _ merged restricted mergedValid
    (fun sc member => inputs sc (List.mem_filter.mp member).1) restriction
  obtain ⟨_, same⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst after
  exact restrictedValid

/-- A fresh slot has no suspended constraints. -/
theorem allocation_canonical (node : Option Nat) (state : State Symbol Guard) (valid : Canonical state) :
    Canonical (allocated node state) := by
  intro value member
  rcases List.mem_append.mp member with old | fresh
  · exact valid value old
  · have same : value = .unenumerated node [] := by simpa using fresh
    simp [same, references, ValidSuspended]

/-- Fresh equality-class allocation preserves canonical stored constraints. -/
theorem suspension_canonical (count : Nat) (state : State Symbol Guard) (valid : Canonical state) :
    Canonical (suspendedState count state) := by
  induction count generalizing state with
  | zero => exact valid
  | succ count ih => exact ih (allocated none state) (allocation_canonical none state valid)

/-- Residual recording changes no suspended trie. -/
theorem recordResidual_canonical (residual : Option Guard) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (valid : Canonical before) (success : Success (recordResidual residual fragment) before () after) : Canonical after := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact valid
  | some guard =>
      obtain rfl := (modify_success _ before after).mp success
      exact valid

/-- The actual mutual traversal retains the source trie representation invariant. -/
theorem enumeration_canonical (graph : Graph Symbol Guard)
    (graphValid : ∀ node edges, graph.node node = .alternatives edges → ∀ edge ∈ edges, ValidEdge edge)
    (fuel : Nat) :
    (∀ scs node (before after : State Symbol Guard) fragment, Canonical before → ValidSuspended scs →
      Success (enumerateNode graph fuel scs node) before fragment after → Canonical after) ∧
    (∀ scs edge (before after : State Symbol Guard) fragment, Canonical before → ValidSuspended scs → ValidEdge edge →
      Success (enumerateEdge graph fuel scs edge) before fragment after → Canonical after) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node before after fragment _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge before after fragment _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node before after fragment valid inputs success
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | alternatives edges | recursive body | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                exact enumerateNode_terminal_canonical graph fuel node scs first rest before after fragment valid inputs
                  (by simp [view]) terminal success
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨member, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact ih.2 scs edge before after fragment valid inputs (graphValid node edges view edge member) continued)
                | (obtain ⟨uv, middle, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
                   have exactState : uv = before.counter ∧ middle = allocated (some node) before := by
                     simpa [Success, allocate_exact, ExceptT.run] using allocation
                   obtain ⟨uvSame, middleSame⟩ := exactState
                   subst uv
                   subst middle
                   obtain ⟨_, same⟩ := (success_pure (.hole before.counter) fragment (allocated (some node) before) after).mp final
                   subst after
                   exact allocation_canonical (some node) before valid)
      · intro scs edge before after fragment valid inputs edgeValid success
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
        have startValid := suspension_canonical edge.equalities.length before valid
        have inputsValid : ValidSuspended (scs ++ suspendedVars before.counter edge.equalities) := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact inputs sc old
          · have member : sc.trie ∈ edge.equalities := by
              rw [← suspendedVars_tries before.counter edge.equalities]
              exact List.mem_map.mpr ⟨sc, fresh, rfl⟩
            exact edgeValid.1 sc.trie member
        obtain ⟨children, expanded, traversal, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have expandedValid := mapM_invariant
          (fun entry => enumerateNode graph fuel (descendScs entry.2 (scs ++ suspendedVars before.counter edge.equalities)) entry.1)
          Canonical edge.children.zipIdx
          (fun entry _ previous child next valid step => ih.1 _ entry.1 previous next child valid
            (descend_valid _ entry.2 inputsValid) step)
          _ expanded children startValid traversal
        obtain ⟨ignored, guarded, guarding, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have guardedValid := recordResidual_canonical edge.residual (.node edge.symbol children) expanded guarded expandedValid guarding
        obtain ⟨_, same⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst after
        exact guardedValid

/-- The actual final root write stores no suspended constraints. -/
theorem enumerateOut_canonical (graph : Graph Symbol Guard)
    (graphValid : ∀ node edges, graph.node node = .alternatives edges → ∀ edge ∈ edges, ValidEdge edge)
    (fuel uv : Nat) (before after : State Symbol Guard) (fragment : Fragment Symbol) (valid : Canonical before)
    (success : Success (enumerateOut graph fuel uv) before fragment after) : Canonical after := by
  unfold enumerateOut at success
  obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readValid, payloadValid⟩ := getValue_canonical (fuel + 1) uv before readState value valid reading
  cases value with
  | eliminated | enumerated _ => exact (reject_unsuccessful readState after fragment continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful readState after fragment continued).elim
      | some node =>
          obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have resolvedValid := representative_canonical (fuel + 1) uv root readState resolved readValid resolution
          obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨currentSame, stateSame⟩ := (get_success resolved currentState current).mp reading
          subst current
          subst currentState
          obtain ⟨ignored, started, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ resolved started).mp bookkeeping
          obtain ⟨produced, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have expandedValid := (enumeration_canonical graph graphValid fuel).1 scs _
            {resolved with expansionAncestry := match graph.node node with
              | .recursive _ => (recursionKey node scs :: resolved.recursionAncestry root).eraseDups
              | _ => resolved.recursionAncestry root}
            expanded produced resolvedValid payloadValid expansion
          obtain ⟨ignored, cleared, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ expanded cleared).mp bookkeeping
          obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          have writtenValid := setValue_canonical root (.enumerated produced) {expanded with expansionAncestry := []} written expandedValid
            (by simp [references, ValidSuspended]) writing
          obtain ⟨_, same⟩ := (success_pure produced fragment written after).mp final
          subst after
          exact writtenValid

end MicroCFTA.EnumerationValidity
