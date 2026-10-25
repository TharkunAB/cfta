import MicroCFTA.EnumerationReferences

/-!
# Ordering stored fragment dependencies

Expanded slots have a level below every hole in their fragments. Pending
slots share the current frontier level. Each final root write advances it.
-/

namespace MicroCFTA.EnumerationOrder
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Stored fragment dependencies strictly increase their level; pending roots share the frontier. -/
structure Stratified (state : State Symbol Guard) (level : Nat → Nat) (frontier : Nat) : Prop where
  classes : UnionFind.Satisfies state.representatives level
  expanded : ∀ uv fragment, state.values[uv]? = some (.enumerated fragment) →
    level uv < frontier ∧ ∀ hole, HasHole fragment hole → level uv < level hole
  pending : ∀ uv node scs, state.values[uv]? = some (.unenumerated node scs) → level uv = frontier

/-- The initialized pending root has no fragment dependency. -/
theorem initial_stratified (root : Nat) : Stratified (initial root : State Symbol Guard) (fun _ => 0) 0 := by
  refine ⟨fun _ _ _ => rfl, ?_, fun _ _ _ _ => rfl⟩
  intro uv fragment stored
  cases uv <;> simp [initial] at stored

/-- A live stored slot is its own representative in any chosen root map. -/
theorem stored_root_fixed (state : State Symbol Guard) (safe : Safe state) (roots : Nat → Nat)
    (paths : Roots state.representatives roots) (uv : Nat) (value : UVarValue Symbol)
    (stored : state.values[uv]? = some value) (live : value ≠ .eliminated) : roots uv = uv :=
  (root_iff state.representatives roots paths uv).mp ((safe.2 uv value stored).mp live)

/-- Rebuild levels after child traversal using preserved expanded classes and pending targets. -/
theorem traversal_stratified (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter) (inputs : InputsPending before scs)
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified before level frontier)
    (success : Success (enumerateNode graph fuel scs node) before fragment after) :
    ∃ nextLevel, Stratified after nextLevel frontier := by
  obtain ⟨safeAfter, _, _⟩ := (enumeration_safety graph fuel).1 scs node before after fragment safe bounded success
  obtain ⟨roots, paths⟩ := roots_exist after.representatives safeAfter.1.total
  let nextLevel := fun uv => match after.values[roots uv]? with
    | some (.enumerated _) => level (roots uv)
    | _ => frontier
  have original := (enumeration_origin graph fuel).1 scs node before after fragment success
  have fixedExpanded : ∀ uv storedFragment, after.values[uv]? = some (.enumerated storedFragment) → nextLevel uv = level uv := by
    intro uv storedFragment stored
    have fixed := stored_root_fixed after safeAfter roots paths uv _ stored (by simp)
    simp [nextLevel, fixed, stored]
  refine ⟨nextLevel, ?_, ?_, ?_⟩
  · intro left right same
    have sameRoot := (class_iff after.representatives roots paths left right).mp same
    simp [nextLevel, sameRoot]
  · intro uv storedFragment stored
    rw [fixedExpanded uv storedFragment stored]
    have beforeStored := original uv storedFragment stored
    obtain ⟨bound, dependencies⟩ := stratified.expanded uv storedFragment beforeStored
    refine ⟨bound, ?_⟩
    intro hole present
    have oldDependency := dependencies hole present
    cases target : after.values[roots hole]? with
    | none => simpa [nextLevel, target] using bound
    | some value =>
        cases value with
        | eliminated | unenumerated _ _ => simpa [nextLevel, target] using bound
        | enumerated targetFragment =>
            have beforeTarget := original (roots hole) targetFragment target
            obtain ⟨inside, root⟩ := enumerated_root before safe (roots hole) targetFragment beforeTarget
            have frame := (enumeration_protected graph fuel).1 scs node (roots hole) before after fragment safe inside root bounded
              (inputs (roots hole) targetFragment beforeTarget) success
            obtain ⟨size, path⟩ := paths hole
            have related := (frame.classes hole).mp (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
            have sameLevel := stratified.classes (roots hole) hole related
            simpa [nextLevel, target, sameLevel] using oldDependency
  · intro uv node scs stored
    have fixed := stored_root_fixed after safeAfter roots paths uv _ stored (by simp)
    simp [nextLevel, fixed, stored]

/-- The next final write advances pending levels and leaves old expanded levels fixed. -/
theorem write_stratified (before : State Symbol Guard) (safe : Safe before) (level : Nat → Nat) (frontier uv : Nat)
    (stratified : Stratified before level frontier) (node : Option Nat) (scs : List Suspended)
    (stored : before.values[uv]? = some (.unenumerated node scs)) (fragment : Fragment Symbol)
    (pendingHoles : ∀ hole, HasHole fragment hole → ∃ root size node scs,
      UnionFind.Reaches before.representatives hole root size ∧ before.values[root]? = some (.unenumerated node scs))
    (separate : FragmentAvoid before.representatives uv fragment) :
    ∃ nextLevel, Stratified {before with values := before.values.set uv (.enumerated fragment)} nextLevel (frontier + 1) := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives safe.1.total
  have fixed := stored_root_fixed before safe roots paths uv _ stored (by simp)
  have selectedLevel := stratified.pending uv node scs stored
  let nextLevel := fun index => if roots index = uv then frontier else if level index = frontier then frontier + 1 else level index
  have sameRootLevel : ∀ index, roots index = uv → level index = frontier := by
    intro index selected
    obtain ⟨size, path⟩ := paths index
    have same := stratified.classes index (roots index) (UnionFind.sameClass_root path)
    simpa [selected, selectedLevel] using same
  have increases : ∀ index, level index ≤ nextLevel index := by
    intro index
    by_cases selected : roots index = uv
    · simp [nextLevel, selected, sameRootLevel index selected]
    · by_cases atFrontier : level index = frontier <;> simp [nextLevel, selected, atFrontier]
  have selectedNext : nextLevel uv = frontier := by simp [nextLevel, fixed]
  have oldExpanded : ∀ index storedFragment, before.values[index]? = some (.enumerated storedFragment) → nextLevel index = level index := by
    intro index storedFragment old
    have bound := (stratified.expanded index storedFragment old).1
    have notSelected : roots index ≠ uv := by intro same; have equal := sameRootLevel index same; omega
    have notFrontier : level index ≠ frontier := by omega
    simp [nextLevel, notSelected, notFrontier]
  refine ⟨nextLevel, ?_, ?_, ?_⟩
  · intro left right same
    have sameRoot := (class_iff before.representatives roots paths left right).mp same
    have sameLevel := stratified.classes left right same
    simp [nextLevel, sameRoot, sameLevel]
  · intro index storedFragment read
    by_cases selected : index = uv
    · subst index
      have inside := (List.getElem?_eq_some_iff.mp stored).1
      have fragmentSame : storedFragment = fragment := by simpa [inside] using read.symm
      subst storedFragment
      rw [selectedNext]
      refine ⟨by omega, ?_⟩
      intro hole present
      obtain ⟨root, size, node, scs, path, pendingRead⟩ := pendingHoles hole present
      have holeLevel := (stratified.classes hole root (UnionFind.sameClass_root path)).trans (stratified.pending root node scs pendingRead)
      have different : roots hole ≠ uv := by
        intro same
        apply separate hole present
        exact (class_iff before.representatives roots paths uv hole).mpr (fixed.trans same.symm)
      simp [nextLevel, different, holeLevel]
    · have old : before.values[index]? = some (.enumerated storedFragment) := by simpa [Ne.symm selected] using read
      obtain ⟨bound, dependencies⟩ := stratified.expanded index storedFragment old
      rw [oldExpanded index storedFragment old]
      exact ⟨by omega, fun hole present => Nat.lt_of_lt_of_le (dependencies hole present) (increases hole)⟩
  · intro index pendingNode pendingScs read
    have notSelected : index ≠ uv := by
      intro same
      subst index
      have inside := (List.getElem?_eq_some_iff.mp stored).1
      simp [inside] at read
    have old : before.values[index]? = some (.unenumerated pendingNode pendingScs) := by simpa [Ne.symm notSelected] using read
    have indexFixed := stored_root_fixed before safe roots paths index _ old (by simp)
    simp [nextLevel, indexFixed, notSelected, stratified.pending index pendingNode pendingScs old]

/-- Reads that preserve values and classes retain the same dependency levels. -/
theorem stratified_read (before after : State Symbol Guard) (level : Nat → Nat) (frontier : Nat)
    (stable : RenderStable before after) (stratified : Stratified before level frontier) : Stratified after level frontier := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right same
    exact stratified.classes left right ((stable.classes left right).mp same)
  · intro uv fragment stored
    exact stratified.expanded uv fragment (by simpa [stable.values] using stored)
  · intro uv node scs stored
    exact stratified.pending uv node scs (by simpa [stable.values] using stored)

/-- Ancestry bookkeeping does not change the stored dependency ordering. -/
theorem stratified_ancestry (state : State Symbol Guard) (ancestry : List RecursionKey) (level : Nat → Nat) (frontier : Nat)
    (stratified : Stratified state level frontier) : Stratified {state with expansionAncestry := ancestry} level frontier :=
  ⟨stratified.classes, stratified.expanded, stratified.pending⟩

/-- The actual final expansion write advances a valid dependency ordering by one level. -/
theorem enumerateOut_stratified (graph : Graph Symbol Guard) (fuel uv : Nat) (before after : State Symbol Guard)
    (fragment : Fragment Symbol) (ready : Ready uv before) (pending : PendingReferences before)
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified before level frontier)
    (success : Success (enumerateOut graph fuel uv) before fragment after) :
    ∃ nextLevel, Stratified after nextLevel (frontier + 1) := by
  unfold enumerateOut at success
  obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readSafe, readCounter, readFrame, stored⟩ := getValue_root (fuel + 1) uv before readState value ready.safe ready.inside ready.root reading
  have readStable := (getValue_storage (fuel + 1) uv before readState value ready.safe ready.inside reading).1
  have readPending := pending_read before readState readStable pending
  have readStratified := stratified_read before readState level frontier readStable stratified
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
          have resolvedStratified := stratified_read readState resolved level frontier resolvedStable readStratified
          have resolvedStored : resolved.values[uv]? = some (.unenumerated (some node) scs) := resolvedFrame.value ▸ stored
          have bounded : ∀ sc ∈ scs, sc.var < resolved.counter := resolvedSafe.1.values _ (List.mem_of_getElem? resolvedStored)
          have oldStored : before.values[uv]? = some (.unenumerated (some node) scs) := readFrame.value ▸ stored
          have inputAvoid := (readFrame.trans resolvedFrame).avoids scs (ready.avoids node scs oldStored)
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
          have startInside : uv < start.counter := by simpa [start, resolvedCounter, readCounter] using ready.inside
          have pendingInputs := pending_inputs start resolvedPending uv (some node) scs resolvedStored
          obtain ⟨expandedLevel, expandedStratified⟩ := traversal_stratified graph fuel _ scs start expanded produced startSafe bounded
            pendingInputs level frontier (stratified_ancestry resolved ancestry level frontier resolvedStratified) expansion
          have expandedSafe := (enumeration_safety graph fuel).1 scs _ start expanded produced startSafe bounded expansion |>.1
          have frame := (enumeration_protected graph fuel).1 scs _ uv start expanded produced startSafe startInside resolvedFrame.root bounded inputAvoid expansion
          have holeAvoid := (enumeration_fragment_avoids graph fuel).1 scs _ uv start expanded produced startSafe startInside resolvedFrame.root bounded inputAvoid expansion
          have pendingHoles := returned_hole_pending graph fuel _ scs start expanded produced startSafe bounded pendingInputs expansion
          have expandedStored : expanded.values[uv]? = some (.unenumerated (some node) scs) := frame.value.trans resolvedStored
          have afterAvoid := (fragmentAvoid_classes start.representatives expanded.representatives uv produced frame.classes).mpr holeAvoid
          obtain ⟨ignored, cleared, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ expanded cleared).mp bookkeeping
          obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          have writtenSame := (modify_success _ _ written).mp writing
          obtain ⟨nextLevel, ordered⟩ := write_stratified {expanded with expansionAncestry := []}
            (ancestry_safe expanded [] expandedSafe) expandedLevel frontier uv (stratified_ancestry expanded [] expandedLevel frontier expandedStratified)
            (some node) scs expandedStored produced pendingHoles afterAvoid
          obtain ⟨_, same⟩ := (success_pure produced fragment written after).mp final
          subst after
          exact ⟨nextLevel, by simpa [writtenSame] using ordered⟩

/-- Scheduler scanning changes no stored dependency or level relation. -/
theorem findExpandable_stratified (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) (safe : Safe before) (level : Nat → Nat) (frontier : Nat)
    (stratified : Stratified before level frontier)
    (success : Success (findExpandable graph fuel) before result after) : Stratified after level frontier := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives safe.1.total
  have scan := (findExpandable_exact graph fuel roots before after result paths success).1
  refine ⟨?_, ?_, ?_⟩
  · intro left right same
    exact stratified.classes left right ((class_iff before.representatives roots paths left right).mpr
      ((class_iff after.representatives roots scan.roots left right).mp same))
  · intro uv fragment stored
    exact stratified.expanded uv fragment (by simpa [scan.values] using stored)
  · intro uv node scs stored
    exact stratified.pending uv node scs (by simpa [scan.values] using stored)

/-- The complete actual caller retains a finite strict ordering of stored fragment dependencies. -/
theorem enumerateFully_stratified (graph : Graph Symbol Guard) (complete : CompleteGraph graph)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle)
    (fuel : Nat) (oracleState : OracleState) (before after : State Symbol Guard) (safe : Safe before) (pending : PendingReferences before)
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified before level frontier)
    (success : Success (enumerateFully graph order oracle fuel oracleState) before () after) :
    ∃ nextLevel nextFrontier, Stratified after nextLevel nextFrontier := by
  induction fuel generalizing oracleState before level frontier with
  | zero => exact (success_failure .fuelExhausted before after () success).elim
  | succ fuel ih =>
      rw [fully_action] at success
      obtain ⟨available, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨scannedSafe, _⟩ := findExpandable_safety graph (fuel + 1) before scanned available safe scanning
      have scannedPending := findExpandable_pending graph (fuel + 1) before scanned available safe.1.total pending scanning
      have scannedStratified := findExpandable_stratified graph (fuel + 1) before scanned available safe level frontier stratified scanning
      cases selected : pickNext (order oracleState) available with
      | done =>
          simp only [selected] at continued
          obtain ⟨_, same⟩ := (success_pure () () scanned after).mp continued
          subst after
          exact ⟨level, frontier, scannedStratified⟩
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
          have readStratified := stratified_read scanned readState level frontier stable scannedStratified
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
                  obtain ⟨expandedLevel, expandedStratified⟩ := enumerateOut_stratified graph (fuel + 1) uv readState expanded fragment
                    readReady readPending level frontier readStratified expansion
                  obtain ⟨⟨afterReject, afterState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have observedSame := observer beforeState uv (.inl fragment) expanded _ observed observation
                  subst observed
                  obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  cases ignored
                  obtain ⟨_, same⟩ := (require_success (!afterReject) expanded accepted).mp acceptance
                  subst accepted
                  exact ih afterState expanded expandedSafe expandedPending expandedLevel (frontier + 1) expandedStratified continued

/-- Successful initialized complete enumeration establishes finite acyclic fragment levels. -/
theorem initialized_stratified (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (fuel root : Nat)
    (after : State Symbol Guard)
    (success : Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) (initial root) () after) :
    ∃ level frontier, Stratified after level frontier :=
  enumerateFully_stratified graph complete (fun _ _ => none) noPruning noPruning_readOnly fuel () (initial root) after
    ⟨initial_storage root, initial_live root⟩ (initial_pending root) (fun _ => 0) 0 (initial_stratified root) success

end MicroCFTA.EnumerationOrder
