import MicroCFTA.EnumerationProgress

/-!
# Fragment dependency separation

Returned fragments cannot refer to a protected expanding root. The proof
follows the concrete child traversal and the exact alias-class preservation.
-/

namespace MicroCFTA.EnumerationDependencies
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- A fragment contains a particular hole at some finite child position. -/
inductive HasHole : Fragment Symbol → Nat → Prop where
  | hole (uv : Nat) : HasHole (.hole uv) uv
  | child (symbol : Symbol) (children : List (Fragment Symbol)) (fragment : Fragment Symbol) (uv : Nat) :
      fragment ∈ children → HasHole fragment uv → HasHole (.node symbol children) uv

/-- Every fragment hole is separate from one protected class. -/
def FragmentAvoid (forest : UnionFind.Forest) (held : Nat) (fragment : Fragment Symbol) : Prop :=
  ∀ uv, HasHole fragment uv → ¬UnionFind.SameClass forest held uv

/-- Preserving the protected class preserves a fragment's dependency separation. -/
theorem fragmentAvoid_classes (before after : UnionFind.Forest) (held : Nat) (fragment : Fragment Symbol)
    (classes : ∀ uv, UnionFind.SameClass after held uv ↔ UnionFind.SameClass before held uv) :
    FragmentAvoid after held fragment ↔ FragmentAvoid before held fragment := by
  simp only [FragmentAvoid, classes]

/-- Actual node and edge traversal returns no dependency on a protected expanding root. -/
theorem enumeration_fragment_avoids (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node held (before after : State Symbol Guard) fragment, Safe before →
      held < before.counter → IsRoot before.representatives held →
      (∀ sc ∈ scs, sc.var < before.counter) → Avoids before.representatives held scs →
      Success (enumerateNode graph fuel scs node) before fragment after → FragmentAvoid before.representatives held fragment) ∧
    (∀ scs edge held (before after : State Symbol Guard) fragment, Safe before →
      held < before.counter → IsRoot before.representatives held →
      (∀ sc ∈ scs, sc.var < before.counter) → Avoids before.representatives held scs →
      Success (enumerateEdge graph fuel scs edge) before fragment after → FragmentAvoid before.representatives held fragment) := by
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
                obtain ⟨_, _, classes, target, fragmentSame, separate⟩ := enumerateNode_terminal_protected graph fuel node scs first rest held
                  before after fragment (by simp [view]) terminal safe.1.total safe.2 root avoids success
                subst fragment
                intro uv hole
                cases hole
                exact fun same => separate ((classes target).mpr same)
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
                   obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.hole before.counter) fragment (allocated (some node) before) after).mp final
                   subst fragment
                   intro uv hole related
                   cases hole
                   have equal := outside_class before.representatives before.counter before.counter held safe.1.forest (Nat.le_refl _)
                     (UnionFind.sameClass_symm related)
                   omega)
      · intro scs edge held before after fragment safe inside root bounded avoids success
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
        have inputAvoid : Avoids before.representatives held inputs := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact avoids sc old
          · exact fresh_avoids before safe.1 held inside edge.equalities sc fresh
        obtain ⟨children, expanded, traversed, continued⟩ := (success_bind _ _ _ _ _).mp continued
        let invariant := fun state : State Symbol Guard =>
          Safe state ∧ start.counter ≤ state.counter ∧ Protected held before state
        have childStep : ∀ (entry : Nat × Nat) previous child next, invariant previous →
            Success (enumerateNode graph fuel (descendScs entry.2 inputs) entry.1) previous child next →
            invariant next ∧ FragmentAvoid before.representatives held child := by
          intro entry previous child next valid childSuccess
          have childBound : ∀ sc ∈ descendScs entry.2 inputs, sc.var < previous.counter := by
            apply descend_bounded
            intro sc member
            exact Nat.lt_of_lt_of_le (inputBound sc member) valid.2.1
          have childAvoid := descend_avoids previous.representatives held entry.2 inputs (valid.2.2.avoids inputs inputAvoid)
          have childInside := Nat.lt_of_lt_of_le startInside valid.2.1
          obtain ⟨nextSafe, growth, _⟩ := (enumeration_safety graph fuel).1 _ entry.1 previous next child valid.1 childBound childSuccess
          have frame := (enumeration_protected graph fuel).1 _ entry.1 held previous next child valid.1 childInside
            valid.2.2.root childBound childAvoid childSuccess
          have fragmentAvoid := ih.1 _ entry.1 held previous next child valid.1 childInside valid.2.2.root childBound childAvoid childSuccess
          exact ⟨⟨nextSafe, Nat.le_trans valid.2.1 growth, valid.2.2.trans frame⟩,
            (fragmentAvoid_classes before.representatives previous.representatives held child valid.2.2.classes).mp fragmentAvoid⟩
        obtain ⟨_, childRelation⟩ := mapM_sound
          (fun entry => enumerateNode graph fuel (descendScs entry.2 inputs) entry.1) invariant
          (fun _ child => FragmentAvoid before.representatives held child) childStep edge.children.zipIdx
          start expanded children ⟨startSafe, Nat.le_refl _, startFrame⟩ traversed
        obtain ⟨ignored, guarded, _, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        obtain ⟨fragmentSame, _⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst fragment
        have allChildren := all₂_outputs (FragmentAvoid before.representatives held) edge.children.zipIdx children childRelation
        intro uv hole
        cases hole with
        | child _ _ child _ member below => exact allChildren child member uv below

/-- A child traversal can retain or remove old expanded slots, but it cannot create an expanded slot. -/
def EnumeratedOrigin (before after : State Symbol Guard) : Prop :=
  ∀ (uv : Nat) (fragment : Fragment Symbol), after.values[uv]? = some (.enumerated fragment) → before.values[uv]? = some (.enumerated fragment)

/-- An unchanged store has no new expanded slots. -/
theorem EnumeratedOrigin.refl (state : State Symbol Guard) : EnumeratedOrigin state state := fun _ _ => id

/-- The origin of expanded slots composes through consecutive state actions. -/
theorem EnumeratedOrigin.trans (first : EnumeratedOrigin before middle) (second : EnumeratedOrigin middle after) :
    EnumeratedOrigin before after := fun uv fragment stored => first uv fragment (second uv fragment stored)

/-- Writing a pending or eliminated value does not create an expanded slot. -/
theorem setValue_origin (uv : Nat) (value : UVarValue Symbol) (before after : State Symbol Guard)
    (pending : ∀ fragment, value ≠ .enumerated fragment)
    (success : Success (setValue uv value) before () after) : EnumeratedOrigin before after := by
  obtain rfl := (modify_success _ before after).mp success
  intro held fragment stored
  by_cases same : held = uv
  · subst held
    have inside := (List.getElem?_eq_some_iff.mp stored).1
    simp only [List.length_set] at inside
    have valueSame : value = .enumerated fragment := by simpa [inside] using stored
    exact (pending fragment valueSame).elim
  · simpa [Ne.symm same] using stored

/-- Fresh pending allocation does not create an expanded slot. -/
theorem allocation_origin (node : Option Nat) (state : State Symbol Guard) : EnumeratedOrigin state (allocated node state) := by
  intro uv fragment stored
  by_cases inside : uv < state.values.length
  · simpa [allocated, List.getElem?_append_left inside] using stored
  · have outside : state.values.length ≤ uv := Nat.le_of_not_lt inside
    rw [show (allocated node state).values = state.values ++ [.unenumerated node []] from rfl,
      List.getElem?_append_right outside] at stored
    cases offset : uv - state.values.length <;> simp [offset] at stored

/-- The actual assimilation action does not create expanded values. -/
theorem assimilate_origin (graph : Graph Symbol Guard) (target source : Nat) (before after : State Symbol Guard)
    (success : Success (EnumerationState.assimilate graph target source) before () after) : EnumeratedOrigin before after := by
  by_cases same : target = source
  · subst source
    have unchanged : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    subst after
    exact .refl before
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, readSource, readingSource, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨_, sourceSame⟩ := (rawValue_success source before readSource sourceValue).mp readingSource
    subst readSource
    cases sourceValue with
    | eliminated =>
        obtain ⟨_, same⟩ := (success_pure () () before after).mp continued
        subst after
        exact .refl before
    | enumerated fragment =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        exact (success_failure .invalidIntersection readTarget after () continued).elim
    | unenumerated node scs =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨_, targetSame⟩ := (rawValue_success target before readTarget targetValue).mp readingTarget
        subst readTarget
        cases intersection : intersectValues graph (.unenumerated node scs) targetValue with
        | none =>
            simp only [intersection] at continued
            exact (success_failure .invalidIntersection before after () continued).elim
        | some merged =>
            obtain ⟨mergedNode, mergedScs, mergedSame⟩ := intersection_pending graph (.unenumerated node scs) targetValue merged intersection
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            obtain ⟨_, same⟩ := (require_success _ before checked).mp required
            subst checked
            obtain ⟨ignored, targetWritten, targetWrite, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have targetOrigin := setValue_origin target merged before targetWritten (by simp [mergedSame]) targetWrite
            obtain ⟨ignored, sourceWritten, sourceWrite, final⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have sourceOrigin := setValue_origin source .eliminated targetWritten sourceWritten (by simp) sourceWrite
            obtain rfl := (modify_success _ sourceWritten after).mp final
            exact targetOrigin.trans sourceOrigin

/-- Actual node restriction does not create an expanded slot. -/
theorem mergeNode_origin (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (success : Success (mergeNode graph fuel uv node scs) before () after) : EnumeratedOrigin before after := by
  unfold mergeNode at success
  obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨found, _, _, resolvedSame⟩ := (representative_success fuel uv before resolved root).mp resolution
  subst resolved
  obtain ⟨previous, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨_, readSame⟩ := (rawValue_success root _ readState previous).mp reading
  subst readState
  cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
  | none =>
      simp only [intersection] at continued
      exact (success_failure .invalidIntersection _ after () continued).elim
  | some merged =>
      obtain ⟨mergedNode, mergedScs, mergedSame⟩ := intersection_pending graph (.unenumerated (some node) scs) previous merged intersection
      simp only [intersection] at continued
      obtain ⟨ignored, written, writing, continued⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      have writtenOrigin := setValue_origin root merged _ written (by simp [mergedSame]) writing
      obtain ⟨ignored, inherited, inheriting, final⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain rfl := (modify_success _ written inherited).mp inheriting
      obtain ⟨_, same⟩ := (require_success _ _ after).mp final
      subst after
      exact writtenOrigin

/-- The complete terminal merge cannot introduce an expanded slot. -/
theorem mergeTerminal_origin (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat)
    (success : Success (mergeTerminal graph fuel first rest) before target after) : EnumeratedOrigin before after := by
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scanStep : ∀ sc ∈ first :: rest, ∀ previous root next, EnumeratedOrigin before previous →
      Success (representative fuel sc.var) previous root next → EnumeratedOrigin before next := by
    intro sc _ previous root next valid step
    obtain ⟨found, _, _, rfl⟩ := (representative_success fuel sc.var previous next root).mp step
    exact valid
  have scannedOrigin := mapM_invariant (fun sc => representative fuel sc.var) (EnumeratedOrigin before) (first :: rest) scanStep
    before scanned recorded (.refl before) scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unionStep : ∀ sc ∈ rest, ∀ previous next, EnumeratedOrigin before previous →
      Success (unionVariables fuel first.var sc.var) previous () next → EnumeratedOrigin before next := by
    intro sc _ previous next valid step
    obtain ⟨forest, _, rfl⟩ := (unionVariables_success fuel first.var sc.var previous next).mp step
    exact valid
  have unitedOrigin := forM_invariant (fun sc => unionVariables fuel first.var sc.var) (EnumeratedOrigin before) rest unionStep
    scanned united scannedOrigin unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedOrigin : EnumeratedOrigin before resolved := by
    obtain ⟨found, _, _, rfl⟩ := (representative_success fuel first.var united resolved winner).mp resolution
    exact unitedOrigin
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have assimilatedOrigin := forM_invariant (EnumerationState.assimilate graph winner) (EnumeratedOrigin before) recorded
    (fun source _ previous next valid step => valid.trans (assimilate_origin graph winner source previous next step))
    resolved assimilated resolvedOrigin assimilation
  obtain ⟨_, same⟩ := (success_pure winner target assimilated after).mp final
  subst after
  exact assimilatedOrigin

/-- A terminal node branch cannot introduce an expanded slot. -/
theorem enumerateNode_terminal_origin (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (first : Suspended) (rest : List Suspended) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) : EnumeratedOrigin before after := by
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, merging, continued⟩ := (success_bind _ _ _ _ _).mp success
  have mergedOrigin := mergeTerminal_origin graph (fuel + 1) first rest before merged root merging
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have restrictedOrigin := mergeNode_origin graph (fuel + 1) root node _ merged restricted restriction
  obtain ⟨_, same⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst after
  exact mergedOrigin.trans restrictedOrigin

/-- Suspending equality classes only allocates pending slots. -/
theorem suspension_origin (count : Nat) (state : State Symbol Guard) : EnumeratedOrigin state (suspendedState count state) := by
  induction count generalizing state with
  | zero => exact .refl state
  | succ count ih => exact (allocation_origin none state).trans (ih (allocated none state))

/-- Residual recording cannot introduce an expanded slot. -/
theorem recordResidual_origin (residual : Option Guard) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (success : Success (recordResidual residual fragment) before () after) : EnumeratedOrigin before after := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact .refl before
  | some guard =>
      obtain rfl := (modify_success _ before after).mp success
      exact .refl before

/-- Only the outer caller's final write can introduce an expanded value. -/
theorem enumeration_origin (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node (before after : State Symbol Guard) fragment,
      Success (enumerateNode graph fuel scs node) before fragment after → EnumeratedOrigin before after) ∧
    (∀ scs edge (before after : State Symbol Guard) fragment,
      Success (enumerateEdge graph fuel scs edge) before fragment after → EnumeratedOrigin before after) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node before after fragment success
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge before after fragment success
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node before after fragment success
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | alternatives edges | recursive body | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                exact enumerateNode_terminal_origin graph fuel node scs first rest before after fragment (by simp [view]) terminal success
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨_, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact ih.2 scs edge before after fragment continued)
                | (obtain ⟨uv, middle, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
                   have exactState : uv = before.counter ∧ middle = allocated (some node) before := by
                     simpa [Success, allocate_exact, ExceptT.run] using allocation
                   obtain ⟨uvSame, middleSame⟩ := exactState
                   subst uv
                   subst middle
                   obtain ⟨_, same⟩ := (success_pure (.hole before.counter) fragment (allocated (some node) before) after).mp final
                   subst after
                   exact allocation_origin (some node) before)
      · intro scs edge before after fragment success
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
        obtain ⟨children, expanded, traversal, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have expandedOrigin := mapM_invariant
          (fun entry => enumerateNode graph fuel (descendScs entry.2 (scs ++ suspendedVars before.counter edge.equalities)) entry.1)
          (EnumeratedOrigin before) edge.children.zipIdx
          (fun entry _ previous child next valid step => valid.trans (ih.1 _ entry.1 previous next child step))
          _ expanded children (suspension_origin edge.equalities.length before) traversal
        obtain ⟨ignored, guarded, guarding, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have guardedOrigin := recordResidual_origin edge.residual (.node edge.symbol children) expanded guarded guarding
        obtain ⟨_, same⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst after
        exact expandedOrigin.trans guardedOrigin

/-- Inherited suspended inputs avoid every already expanded slot. -/
def InputsPending (state : State Symbol Guard) (scs : List Suspended) : Prop :=
  ∀ held fragment, state.values[held]? = some (.enumerated fragment) → Avoids state.representatives held scs

/-- Every contained hole obeys the fragment's allocation bound. -/
theorem hasHole_bounded (limit : Nat) (fragment : Fragment Symbol) (uv : Nat)
    (bounded : FragmentBound limit fragment) (hole : HasHole fragment uv) : uv < limit := by
  induction hole with
  | hole uv => exact bounded
  | child symbol children fragment uv member below ih =>
      exact ih (fragmentsBound_member limit children bounded fragment member)

/-- A stored expanded slot in a safe state is an allocated root. -/
theorem enumerated_root (state : State Symbol Guard) (safe : Safe state) (uv : Nat) (fragment : Fragment Symbol)
    (stored : state.values[uv]? = some (.enumerated fragment)) : uv < state.counter ∧ IsRoot state.representatives uv := by
  refine ⟨?_, (safe.2 uv (.enumerated fragment) stored).mp (by simp)⟩
  rw [safe.1.aligned]
  exact (List.getElem?_eq_some_iff.mp stored).1

/-- A returned hole reaches a pending representative when its inputs avoid old expanded slots. -/
theorem returned_hole_pending (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter) (pending : InputsPending before scs)
    (success : Success (enumerateNode graph fuel scs node) before fragment after) :
    ∀ uv, HasHole fragment uv → ∃ root size node scs,
      UnionFind.Reaches after.representatives uv root size ∧ after.values[root]? = some (.unenumerated node scs) := by
  obtain ⟨safeAfter, _, fragmentBound⟩ := (enumeration_safety graph fuel).1 scs node before after fragment safe bounded success
  have origin := (enumeration_origin graph fuel).1 scs node before after fragment success
  intro uv hole
  have uvBound := hasHole_bounded after.counter fragment uv fragmentBound hole
  obtain ⟨root, size, path⟩ := safeAfter.1.total uv
  have rootBound := reaches_bounded after.representatives after.counter safeAfter.1.forest path uvBound
  have index : root < after.values.length := by rw [← safeAfter.1.aligned]; exact rootBound
  let value := after.values[root]
  have stored : after.values[root]? = some value := List.getElem?_eq_getElem index
  have rootLive : value ≠ .eliminated :=
    (safeAfter.2 root value stored).mpr ⟨size, .root (UnionFind.reaches_terminal path)⟩
  cases valueEq : value with
  | eliminated => exact (rootLive valueEq).elim
  | unenumerated pendingNode pendingScs => exact ⟨root, size, pendingNode, pendingScs, path, by simpa [valueEq] using stored⟩
  | enumerated oldFragment =>
      have afterStored : after.values[root]? = some (.enumerated oldFragment) := by simpa [valueEq] using stored
      have beforeStored := origin root oldFragment afterStored
      obtain ⟨inside, rootBefore⟩ := enumerated_root before safe root oldFragment beforeStored
      have avoids := pending root oldFragment beforeStored
      have separated := (enumeration_fragment_avoids graph fuel).1 scs node root before after fragment safe inside rootBefore bounded avoids success
      have frame := (enumeration_protected graph fuel).1 scs node root before after fragment safe inside rootBefore bounded avoids success
      exact (separated uv hole ((frame.classes uv).mp (UnionFind.sameClass_symm (UnionFind.sameClass_root path)))).elim

end MicroCFTA.EnumerationDependencies
