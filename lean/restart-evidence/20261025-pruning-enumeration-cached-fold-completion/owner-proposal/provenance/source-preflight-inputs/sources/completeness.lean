import MicroCFTA.EnumerationExecution

/-!
# Constructing executions from complete assignments

Pending values with a common accepted term admit the source intersection
and assimilation branches. Their structural-empty checks cannot reject.
-/

namespace MicroCFTA.EnumerationCompleteness
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- A concrete slot stores a pending graph or equality variable. -/
def PendingAt (state : State Symbol Guard) (uv : Nat) : Prop :=
  ∃ node scs, state.values[uv]? = some (.unenumerated node scs)

/-- A selected old slot is pending or has already been assimilated. -/
def PendingOrEliminated (state : State Symbol Guard) (uv : Nat) : Prop :=
  PendingAt state uv ∨ state.values[uv]? = some .eliminated

/-- The stored assignment supplies the restriction of each present slot. -/
theorem stored_satisfies (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (state : State Symbol Guard)
    (satisfies : Satisfies language meaning assignment state) (uv : Nat) (value : UVarValue Symbol)
    (stored : state.values[uv]? = some value) : slotSatisfies assignment uv (slot language value) := by
  simpa [heap, stored] using satisfies.1.2 uv

/-- A satisfying pending value passes the actual structural-empty check. -/
theorem satisfies_not_empty (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (uv : Nat) (value : UVarValue Symbol)
    (satisfies : slotSatisfies assignment uv (slot (Accepted graph meaning) value)) : hasEmptyContents graph value = false := by
  cases empty : hasEmptyContents graph value with
  | false => rfl
  | true => exact (empty_check_sound graph meaning assignment uv value empty satisfies).elim

/-- Assimilation preserves pending or eliminated slot shapes. -/
theorem assimilated_pending (state : State Symbol Guard) (target source : Nat) (node : Option Nat) (scs : List Suspended)
    (different : target ≠ source) (targetInside : target < state.values.length) (sourceInside : source < state.values.length) :
    PendingAt (assimilated state target source (.unenumerated node scs)) target ∧
      ∀ uv, PendingOrEliminated state uv → PendingOrEliminated (assimilated state target source (.unenumerated node scs)) uv := by
  refine ⟨⟨node, scs, by simp [assimilated, targetInside, Ne.symm different]⟩, ?_⟩
  intro uv previous
  by_cases atSource : uv = source
  · subst uv
    exact Or.inr (by simp [assimilated, sourceInside])
  · by_cases atTarget : uv = target
    · subst uv
      exact Or.inl ⟨node, scs, by simp [assimilated, targetInside, Ne.symm different]⟩
    · have same : (assimilated state target source (.unenumerated node scs)).values[uv]? = state.values[uv]? := by
        simp [assimilated, Ne.symm atTarget, Ne.symm atSource]
      rcases previous with ⟨oldNode, oldScs, stored⟩ | eliminated
      · exact Or.inl ⟨oldNode, oldScs, same.trans stored⟩
      · exact Or.inr (same.trans eliminated)

/-- Equal satisfying pending values always admit the actual assimilation action. -/
theorem assimilate_terminates (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (correct : IntersectionCorrect graph (Accepted graph meaning)) (assignment : Nat → Term Symbol)
    (before : State Symbol Guard) (target source : Nat)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment before)
    (targetPending : PendingAt before target) (sourcePending : PendingOrEliminated before source)
    (equal : assignment target = assignment source) :
    ∃ after, Success (EnumerationState.assimilate graph target source) before () after ∧
      Satisfies (Accepted graph meaning) meaning assignment after ∧ PendingAt after target ∧
      ∀ uv, PendingOrEliminated before uv → PendingOrEliminated after uv := by
  by_cases same : target = source
  · subst source
    exact ⟨before, by simpa [EnumerationState.assimilate] using (success_pure () () before before).mpr ⟨rfl, rfl⟩,
      satisfies, targetPending, fun _ valid => valid⟩
  · rcases sourcePending with ⟨sourceNode, sourceScs, sourceRead⟩ | eliminated
    · obtain ⟨targetNode, targetScs, targetRead⟩ := targetPending
      let mergedNode := match sourceNode, targetNode with
        | none, node => node | node, none => node | some left, some right => some (graph.intersect left right)
      let merged : UVarValue Symbol := .unenumerated mergedNode (sourceScs ++ targetScs)
      have intersection : intersectValues graph (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs) = some merged := by
        cases sourceNode <;> cases targetNode <;> rfl
      have sourceHolds := stored_satisfies (Accepted graph meaning) meaning assignment before satisfies source _ sourceRead
      have targetHolds := stored_satisfies (Accepted graph meaning) meaning assignment before satisfies target _ targetRead
      have sourceAtTarget : slotSatisfies assignment target (slot (Accepted graph meaning) (.unenumerated sourceNode sourceScs)) := by
        simpa [slot, slotSatisfies, equal] using sourceHolds
      have mergedHolds := (intersection_semantics graph (Accepted graph meaning) correct assignment target _ _ merged intersection).mpr
        ⟨sourceAtTarget, targetHolds⟩
      have notEmpty := satisfies_not_empty graph meaning assignment target merged mergedHolds
      have execution := assimilate_exact graph before target source sourceNode targetNode sourceScs targetScs merged same sourceRead targetRead intersection notEmpty
      have pending := assimilated_pending before target source mergedNode (sourceScs ++ targetScs) same
        (List.getElem?_eq_some_iff.mp targetRead).1 (List.getElem?_eq_some_iff.mp sourceRead).1
      refine ⟨assimilated before target source merged, ?_, ?_, pending.1, pending.2⟩
      · simp [Success, execution, ExceptT.run]
      · exact (assimilation_semantics graph (Accepted graph meaning) correct meaning assignment before target source _ _ merged same sourceRead targetRead intersection equal).mpr satisfies
    · refine ⟨before, ?_, satisfies, targetPending, fun _ valid => valid⟩
      simp only [EnumerationState.assimilate, same, ↓reduceIte]
      exact (success_bind _ _ _ _ _).mpr ⟨.eliminated, before, (rawValue_success _ _ _ _).mpr ⟨eliminated, rfl⟩,
        (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

/-- Every recorded equal pending source can be assimilated in its actual order. -/
theorem assimilations_terminate (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (correct : IntersectionCorrect graph (Accepted graph meaning)) (assignment : Nat → Term Symbol)
    (target : Nat) (sources : List Nat) (before : State Symbol Guard)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment before) (targetPending : PendingAt before target)
    (pending : ∀ source ∈ sources, PendingOrEliminated before source)
    (equal : ∀ source ∈ sources, assignment target = assignment source) :
    ∃ after, Success (sources.forM (EnumerationState.assimilate graph target)) before () after ∧
      Satisfies (Accepted graph meaning) meaning assignment after ∧ PendingAt after target := by
  induction sources generalizing before with
  | nil => exact ⟨before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, satisfies, targetPending⟩
  | cons source rest ih =>
      obtain ⟨middle, first, middleSatisfies, middlePending, preserved⟩ := assimilate_terminates graph meaning correct assignment
        before target source satisfies targetPending (pending source (by simp)) (equal source (by simp))
      obtain ⟨after, continued, afterSatisfies, afterPending⟩ := ih middle middleSatisfies middlePending
        (fun source member => preserved source (pending source (by simp [member])))
        (fun source member => equal source (by simp [member]))
      exact ⟨after, (success_bind _ _ _ _ _).mpr ⟨(), middle, first, continued⟩, afterSatisfies, afterPending⟩

/-- Bounded inputs that avoid expanded slots reach pending representatives. -/
theorem inputs_pendingAt (state : State Symbol Guard) (safe : Safe state) (scs : List Suspended)
    (bounded : ∀ sc ∈ scs, sc.var < state.counter) (pending : InputsPending state scs)
    (sc : Suspended) (member : sc ∈ scs) (root size : Nat)
    (path : UnionFind.Reaches state.representatives sc.var root size) : PendingAt state root := by
  have inside := reaches_bounded state.representatives state.counter safe.1.forest path (bounded sc member)
  have index : root < state.values.length := by rw [← safe.1.aligned]; exact inside
  let value := state.values[root]
  have stored : state.values[root]? = some value := List.getElem?_eq_getElem index
  have live : value ≠ .eliminated := (safe.2 root value stored).mpr ⟨size, .root (UnionFind.reaches_terminal path)⟩
  cases valueEq : value with
  | eliminated => exact (live valueEq).elim
  | unenumerated node scs => exact ⟨node, scs, by simpa [valueEq] using stored⟩
  | enumerated fragment =>
      have exactSlot : state.values[root]? = some (.enumerated fragment) := by simpa [valueEq] using stored
      exact (pending root fragment exactSlot sc member (UnionFind.sameClass_symm (UnionFind.sameClass_root path))).elim

/-- A new accepted node restriction always merges into a pending representative. -/
theorem mergeNode_terminates (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (correct : IntersectionCorrect graph (Accepted graph meaning)) (assignment : Nat → Term Symbol)
    (before : State Symbol Guard) (uv node : Nat) (scs : List Suspended) (total : UnionFind.Total before.representatives)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment before)
    (pending : ∀ root size, UnionFind.Reaches before.representatives uv root size → PendingAt before root)
    (accepted : Accepted graph meaning node (assignment uv))
    (holds : ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) :
    ∃ fuel after, Success (mergeNode graph fuel uv node scs) before () after ∧
      Satisfies (Accepted graph meaning) meaning assignment after := by
  obtain ⟨root, size, path⟩ := total uv
  obtain ⟨fuel, found, lookup⟩ := UnionFind.findRoot_terminates path
  have foundPath := (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1
  obtain ⟨previousNode, previousScs, stored⟩ := pending found.representative found.size foundPath
  let mergedNode := match previousNode with | none => node | some previous => graph.intersect node previous
  let merged : UVarValue Symbol := .unenumerated (some mergedNode) (scs ++ previousScs)
  have intersection : intersectValues graph (.unenumerated (some node) scs) (.unenumerated previousNode previousScs) = some merged := by
    cases previousNode <;> rfl
  have equal : assignment uv = assignment found.representative := satisfies.1.1 _ _ (UnionFind.sameClass_root foundPath)
  have newHolds : slotSatisfies assignment found.representative (slot (Accepted graph meaning) (.unenumerated (some node) scs)) := by
    refine ⟨by simpa [permits, ← equal] using accepted, ?_⟩
    intro requirement member
    obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
    simpa [← equal] using holds sc present
  have previousHolds := stored_satisfies (Accepted graph meaning) meaning assignment before satisfies found.representative _ stored
  have mergedHolds := (intersection_semantics graph (Accepted graph meaning) correct assignment found.representative _ _ merged intersection).mpr
    ⟨newHolds, previousHolds⟩
  have notEmpty := satisfies_not_empty graph meaning assignment found.representative merged mergedHolds
  have execution := mergeNode_exact graph before fuel uv node scs found _ merged lookup stored intersection notEmpty
  exact ⟨fuel, nodeMerged before found merged, by simp [Success, execution, ExceptT.run],
    (mergeNode_semantics graph (Accepted graph meaning) correct meaning assignment before fuel uv node scs found _ merged
      total lookup stored intersection).mpr ⟨satisfies, accepted, holds⟩⟩

/-- The complete terminal equality merge has a successful sufficiently bounded execution. -/
theorem mergeTerminal_terminates (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (correct : IntersectionCorrect graph (Accepted graph meaning)) (assignment : Nat → Term Symbol)
    (before : State Symbol Guard) (first : Suspended) (rest : List Suspended) (total : UnionFind.Total before.representatives)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment before)
    (pending : ∀ sc ∈ first :: rest, ∀ root size, UnionFind.Reaches before.representatives sc.var root size → PendingAt before root)
    (equal : ∀ sc ∈ rest, assignment first.var = assignment sc.var) :
    ∃ fuel root after, Success (mergeTerminal graph fuel first rest) before root after ∧
      Satisfies (Accepted graph meaning) meaning assignment after ∧ PendingAt after root := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  obtain ⟨scanFuel, recorded, scanned, scan, _⟩ := mapM_terminates
    (fun fuel (sc : Suspended) => representative fuel sc.var)
    (fun state : State Symbol Guard => UnionFind.Total state.representatives)
    (fun fuel extra sc => representative_moreFuel fuel extra sc.var)
    (fun sc state valid => representative_terminates state valid sc.var) (first :: rest) before total
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots scanFuel (first :: rest) before scanned recorded ⟨rfl, paths⟩ scan
  obtain ⟨scanTotal, scanExact⟩ := representatives_assignment (Accepted graph meaning) meaning assignment scanFuel (first :: rest) before scanned recorded total scan
  have scanSatisfies := scanExact.mpr satisfies
  obtain ⟨unionFuel, united, unions, _⟩ := forM_terminates
    (fun fuel (sc : Suspended) => unionVariables fuel first.var sc.var)
    (fun state : State Symbol Guard => UnionFind.Total state.representatives)
    (fun fuel extra sc => unionVariables_moreFuel fuel extra first.var sc.var)
    (fun sc state valid => unionVariables_terminates state valid first.var sc.var) rest scanned scanTotal
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united := terminal_unions before.values roots [roots first.var] unionFuel first.var rest
    scanned united (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨unionTotal, unionExact⟩ := terminal_unions_assignment (Accepted graph meaning) meaning assignment unionFuel first.var rest scanned united scanTotal unions
  have unionSatisfies := unionExact.mpr ⟨scanSatisfies, equal⟩
  obtain ⟨rootFuel, winner, resolved, resolution, _⟩ := representative_terminates united unionTotal first.var
  obtain ⟨resolvedValid, count, winnerPath⟩ := merging_representative before.values roots selected rootFuel first.var winner united resolved joined resolution
  have resolvedSatisfies := (representative_assignment (Accepted graph meaning) meaning assignment rootFuel first.var winner united resolved unionTotal resolution).2.mpr unionSatisfies
  have sameSelected (uv : Nat) : uv ∈ recorded ↔ uv ∈ selected := by
    rw [recordedSame, resolve_members roots rest [roots first.var] uv]
    simp [List.mem_map]
  have firstSelected : roots first.var ∈ selected :=
    (resolve_members roots rest [roots first.var] (roots first.var)).mpr (Or.inl (by simp))
  have winnerRoot : IsRoot resolved.representatives winner := ⟨count, .root (UnionFind.reaches_terminal winnerPath)⟩
  have winnerFixed := resolvedValid.oldRoots winner winnerRoot
  have winnerSelected : winner ∈ selected := by
    rcases (resolvedValid.joined first.var winner).mp (UnionFind.sameClass_root winnerPath) with same | both
    · simpa [winnerFixed, same] using firstSelected
    · simpa [winnerFixed] using both.2
  have recordedPending : ∀ source ∈ recorded, PendingAt resolved source := by
    intro source member
    rw [recordedSame] at member
    obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨size, path⟩ := paths sc.var
    obtain ⟨node, scs, stored⟩ := pending sc present (roots sc.var) size path
    exact ⟨node, scs, by simpa [resolvedValid.values] using stored⟩
  have winnerEqual : assignment winner = assignment first.var :=
    (resolvedSatisfies.1.1 first.var winner (UnionFind.sameClass_root winnerPath)).symm
  have recordedEqual : ∀ source ∈ recorded, assignment winner = assignment source := by
    intro source member
    rw [recordedSame] at member
    obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨size, path⟩ := paths sc.var
    have toRoot := satisfies.1.1 sc.var (roots sc.var) (UnionFind.sameClass_root path)
    have toFirst : assignment first.var = assignment sc.var := by
      rcases List.mem_cons.mp present with rfl | member
      · rfl
      · exact equal sc member
    exact winnerEqual.trans (toFirst.trans toRoot)
  obtain ⟨after, assimilation, afterSatisfies, afterPending⟩ := assimilations_terminate graph meaning correct assignment winner recorded resolved resolvedSatisfies
    (recordedPending winner ((sameSelected winner).mpr winnerSelected)) (fun source member => Or.inl (recordedPending source member)) recordedEqual
  let fuel := scanFuel + unionFuel + rootFuel
  have scanMore : Success ((first :: rest).mapM fun sc => representative fuel sc.var) before recorded scanned := by
    have extended := retains_mapM _ _ (fun (sc : Suspended) => representative_moreFuel scanFuel (unionFuel + rootFuel) sc.var) (first :: rest) _ _ _ scan
    simpa [fuel, Nat.add_assoc] using extended
  have unionsMore : Success (rest.forM fun sc => unionVariables fuel first.var sc.var) scanned () united := by
    have extended := retains_forM _ _ (fun (sc : Suspended) => unionVariables_moreFuel unionFuel (scanFuel + rootFuel) first.var sc.var) rest _ _ _ unions
    simpa [fuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extended
  have resolutionMore : Success (representative fuel first.var) united winner resolved := by
    have extended := representative_moreFuel rootFuel (scanFuel + unionFuel) first.var _ _ _ resolution
    simpa [fuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extended
  refine ⟨fuel, winner, after, ?_, afterSatisfies, afterPending⟩
  unfold mergeTerminal
  exact (success_bind _ _ _ _ _).mpr ⟨recorded, scanned, scanMore,
    (success_bind _ _ _ _ _).mpr ⟨(), united, unionsMore,
      (success_bind _ _ _ _ _).mpr ⟨winner, resolved, resolutionMore,
        (success_bind _ _ _ _ _).mpr ⟨(), after, assimilation, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩⟩⟩

/-- Terminal suspended equalities construct an actual successful node branch without changing its assignment. -/
theorem enumerateNode_terminal_terminates (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (correct : IntersectionCorrect graph (Accepted graph meaning)) (assignment : Nat → Term Symbol)
    (before : State Symbol Guard) (safe : Safe before) (node : Nat) (term : Term Symbol)
    (scs : List Suspended) (bounded : ∀ sc ∈ scs, sc.var < before.counter) (pending : InputsPending before scs)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment before) (accepted : Accepted graph meaning node term)
    (holds : ∀ sc ∈ scs, Suspended.Holds assignment term sc) (first : Suspended) (rest : List Suspended)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest) :
    ∃ fuel root after, Success (enumerateNode graph fuel scs node) before (.hole root) after ∧
      Satisfies (Accepted graph meaning) meaning assignment after ∧ assignment root = term := by
  have selected (sc : Suspended) (member : sc ∈ first :: rest) : sc ∈ scs ∧ EqualityTrie.isTerminal sc.trie = true := by
    rw [← terminal] at member
    exact List.mem_filter.mp member
  have assigned (sc : Suspended) (member : sc ∈ first :: rest) : term = assignment sc.var :=
    (terminal_holds assignment term sc (selected sc member).2).mp (holds sc (selected sc member).1)
  obtain ⟨mergeFuel, root, merged, merging, mergedSatisfies, mergedPending⟩ := mergeTerminal_terminates graph meaning correct assignment
    before first rest safe.1.total satisfies
    (fun sc member target size path => inputs_pendingAt before safe scs bounded pending sc (selected sc member).1 target size path)
    (fun sc member => (assigned first (by simp)).symm.trans (assigned sc (by simp [member])))
  obtain ⟨mergedLive, mergedTotal⟩ := mergeTerminal_valid graph mergeFuel first rest before merged root safe.1.total safe.2 merging
  have rootTerm : assignment root = term :=
    ((mergeTerminal_backward graph (Accepted graph meaning) correct meaning assignment mergeFuel first rest before merged root safe.1.total merging mergedSatisfies).2 first (by simp)).trans
      (assigned first (by simp)).symm
  obtain ⟨pendingNode, pendingScs, pendingStored⟩ := mergedPending
  obtain ⟨rootSize, rootPath⟩ := (mergedLive root _ pendingStored).mp (by simp)
  have pendingRoot : ∀ target size, UnionFind.Reaches merged.representatives root target size → PendingAt merged target := by
    intro target size path
    have same := (UnionFind.reaches_unique path rootPath).1
    exact same ▸ ⟨pendingNode, pendingScs, pendingStored⟩
  obtain ⟨restrictFuel, after, restriction, afterSatisfies⟩ := mergeNode_terminates graph meaning correct assignment merged root node
    (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie) mergedTotal mergedSatisfies pendingRoot
    (by simpa [rootTerm] using accepted) (fun sc member => by simpa [rootTerm] using holds sc (List.mem_filter.mp member).1)
  have nonempty : graph.node node ≠ .empty := fun empty => accepted_empty graph meaning node term empty accepted
  refine ⟨mergeFuel + restrictFuel + 1, root, after, ?_, afterSatisfies, rootTerm⟩
  rw [terminal_branch graph (mergeFuel + restrictFuel) node scs first rest nonempty terminal]
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨root, merged, ?_, (success_bind _ _ _ _ _).mpr ⟨(), after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩
  · have extended := mergeTerminal_moreFuel graph mergeFuel (restrictFuel + 1) first rest before root merged merging
    simpa [Nat.add_assoc] using extended
  · have extended := mergeNode_moreFuel graph restrictFuel (mergeFuel + 1) root node
      (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie) merged () after restriction
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extended

end MicroCFTA.EnumerationCompleteness
