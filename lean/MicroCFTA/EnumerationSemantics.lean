import MicroCFTA.EnumerationDriver

/-!
# Assignment semantics of the concrete enumeration actions

Successful source actions retain their exact complete-assignment restrictions.
The graph intersection law is an explicit graph-interface obligation.
-/

namespace MicroCFTA.EnumerationSemantics
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver

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

/-- A successful raw read returns the stored value without changing the state. -/
theorem rawValue_success (uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol) :
    Success (rawValue uv) before value after ↔ before.values[uv]? = some value ∧ after = before := by
  cases stored : before.values[uv]? <;>
    simp [Success, rawValue, stored, EnumerationState.failure, bind, get, getThe, MonadStateOf.get,
      pure, StateT.bind, StateT.pure, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run, eq_comm]

/-- The actual representative action preserves the complete assignment exactly. -/
theorem representative_assignment (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv result : Nat) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives)
    (success : Success (representative fuel uv) before result after) :
    UnionFind.Total after.representatives ∧
      (Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before) := by
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after result).mp success
  exact ⟨UnionFind.findRoot_total total lookup, representative_semantics language meaning assignment fuel uv before found total lookup⟩

/-- Actual assimilation preserves all assignments that already equate its two slots. -/
theorem assimilate_assignment (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (target source : Nat) (before after : State Symbol Guard)
    (equal : assignment target = assignment source)
    (success : Success (EnumerationState.assimilate graph target source) before () after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before := by
  have original := success
  by_cases same : target = source
  · subst source
    have unchanged : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    simp [unchanged]
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, readSource, readingSource, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨sourceRead, sourceStateSame⟩ := (rawValue_success source before readSource sourceValue).mp readingSource
    subst readSource
    cases sourceValue with
    | eliminated =>
        obtain ⟨_, unchanged⟩ := (success_pure () () before after).mp continued
        simp [unchanged]
    | enumerated fragment =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨_, targetStateSame⟩ := (rawValue_success target before readTarget targetValue).mp readingTarget
        subst readTarget
        exact (success_failure .invalidIntersection before after () continued).elim
    | unenumerated sourceNode sourceScs =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨targetRead, targetStateSame⟩ := (rawValue_success target before readTarget targetValue).mp readingTarget
        subst readTarget
        cases targetValue with
        | eliminated | enumerated _ => exact (success_failure .invalidIntersection before after () continued).elim
        | unenumerated targetNode targetScs =>
            let merged : UVarValue Symbol := .unenumerated (match sourceNode, targetNode with
              | none, node => node | node, none => node | some left, some right => some (graph.intersect left right))
              (sourceScs ++ targetScs)
            have intersection : intersectValues graph (.unenumerated sourceNode sourceScs)
                (.unenumerated targetNode targetScs) = some merged := by cases sourceNode <;> cases targetNode <;> rfl
            have notEmpty : hasEmptyContents graph merged = false := by
              simp only [intersection] at continued
              obtain ⟨ignored, checked, required, _⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              have passed := ((require_success _ before checked).mp required).1
              simpa using passed
            have exactAction := assimilate_exact graph before target source sourceNode targetNode sourceScs targetScs
              merged same sourceRead targetRead intersection notEmpty
            have exactState : after = assimilated before target source merged := by
              simpa [Success, exactAction, ExceptT.run] using original
            rw [exactState]
            exact assimilation_semantics graph language correct meaning assignment before target source _ _ merged
              same sourceRead targetRead intersection equal

/-- Actual node restriction adds exactly its language and suspended requirements. -/
theorem mergeNode_assignment (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (success : Success (mergeNode graph fuel uv node scs) before () after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before ∧
      language node (assignment uv) ∧ ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
  cases lookup : UnionFind.findRoot fuel before.representatives uv with
  | none =>
      simp [Success, mergeNode, representative, lookup, EnumerationState.failure, bind, get, getThe, MonadStateOf.get,
        pure, StateT.bind, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
  | some found =>
      cases stored : before.values[found.representative]? with
      | none =>
          simp [Success, mergeNode, representative, lookup, rawValue, stored, EnumerationState.failure,
            bind, get, getThe, MonadStateOf.get, set, pure, StateT.bind, StateT.pure, StateT.get, StateT.set,
            ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
      | some previous =>
          cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
          | none =>
              simp [Success, mergeNode, representative, lookup, rawValue, stored, intersection, EnumerationState.failure,
                bind, get, getThe, MonadStateOf.get, set, pure, StateT.bind, StateT.pure, StateT.get, StateT.set,
                ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
          | some merged =>
              cases empty : hasEmptyContents graph merged with
              | true =>
                  simp [Success, mergeNode, representative, lookup, rawValue, stored, intersection, empty, require, reject,
                    setValue, inheritAncestry, bind, get, getThe, MonadStateOf.get, set, pure, modify, modifyGet,
                    MonadStateOf.modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.set, StateT.modifyGet,
                    ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
              | false =>
                  have execution := mergeNode_exact graph before fuel uv node scs found previous merged lookup stored intersection empty
                  have same : after = nodeMerged before found merged := by simpa [Success, execution, ExceptT.run] using success
                  rw [same]
                  exact mergeNode_semantics graph language correct meaning assignment before fuel uv node scs found previous merged
                    total lookup stored intersection

/-- A representative pre-scan preserves totality and every complete assignment. -/
theorem representatives_assignment (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel : Nat) (scs : List Suspended) (before after : State Symbol Guard)
    (recorded : List Nat) (total : UnionFind.Total before.representatives)
    (success : Success (scs.mapM fun sc => representative fuel sc.var) before recorded after) :
    UnionFind.Total after.representatives ∧
      (Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before) := by
  let invariant := fun state : State Symbol Guard => UnionFind.Total state.representatives ∧
    (Satisfies language meaning assignment state ↔ Satisfies language meaning assignment before)
  apply mapM_invariant (fun sc => representative fuel sc.var) invariant scs ?_ before after recorded ⟨total, Iff.rfl⟩ success
  intro sc _ previous result next valid step
  obtain ⟨nextTotal, equivalent⟩ := representative_assignment language meaning assignment fuel sc.var result previous next valid.1 step
  exact ⟨nextTotal, equivalent.trans valid.2⟩

/-- Successful terminal unions retain the original restrictions and add their listed equalities. -/
theorem terminal_unions_assignment (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel first : Nat) (rest : List Suspended) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives)
    (success : Success (rest.forM fun sc => unionVariables fuel first sc.var) before () after) :
    UnionFind.Total after.representatives ∧
      (Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before ∧
        ∀ sc ∈ rest, assignment first = assignment sc.var) := by
  induction rest generalizing before with
  | nil =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact ⟨total, by simp⟩
  | cons sc rest ih =>
      change Success (unionVariables fuel first sc.var >>= fun _ =>
        rest.forM fun sc => unionVariables fuel first sc.var) before () after at success
      obtain ⟨ignored, middle, unionStep, continued⟩ := (success_bind _ _ _ _ _).mp success
      cases ignored
      obtain ⟨forest, result, middleSame⟩ := (unionVariables_success fuel first sc.var before middle).mp unionStep
      subst middle
      have nextTotal := (UnionFind.union_correct total result).1
      obtain ⟨lastTotal, restExact⟩ := ih _ nextTotal continued
      refine ⟨lastTotal, ?_⟩
      rw [restExact, union_semantics language meaning assignment fuel first sc.var before forest total result]
      simp only [List.mem_cons, forall_eq_or_imp]
      exact and_assoc

/-- Assimilating the full recorded root list preserves all already equated assignments. -/
theorem terminal_assimilations_assignment (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (target : Nat) (sources : List Nat) (before after : State Symbol Guard)
    (equal : ∀ source ∈ sources, assignment target = assignment source)
    (success : Success (sources.forM (EnumerationState.assimilate graph target)) before () after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before := by
  let invariant := fun state : State Symbol Guard =>
    Satisfies language meaning assignment state ↔ Satisfies language meaning assignment before
  apply forM_invariant (EnumerationState.assimilate graph target) invariant sources ?_ before after Iff.rfl success
  intro source member previous next valid step
  exact (assimilate_assignment graph language correct meaning assignment target source previous next (equal source member) step).trans valid

/-- The actual terminal merge cannot discard a complete assignment restriction. -/
theorem mergeTerminal_backward (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (total : UnionFind.Total before.representatives)
    (success : Success (mergeTerminal graph fuel first rest) before target after)
    (satisfies : Satisfies language meaning assignment after) :
    Satisfies language meaning assignment before ∧
      ∀ sc ∈ first :: rest, assignment target = assignment sc.var := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, preScan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel (first :: rest)
    before scanned recorded ⟨rfl, paths⟩ preScan
  obtain ⟨scanTotal, scanExact⟩ := representatives_assignment language meaning assignment fuel (first :: rest) before scanned recorded total preScan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united := terminal_unions before.values roots [roots first.var] fuel first.var rest
    scanned united (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, count, path⟩ := merging_representative before.values roots selected fuel first.var winner
    united resolved joined resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨targetSame, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst target
  subst after
  have forestSame := (terminal_assimilations graph winner recorded resolved assimilated assimilation).1
  have consistent : UnionFind.Satisfies resolved.representatives assignment := by
    rw [← forestSame]
    exact satisfies.1.1
  have selectedMember : ∀ sc ∈ first :: rest, roots sc.var ∈ selected := by
    intro sc member
    apply (resolve_members roots rest [roots first.var] (roots sc.var)).mpr
    rcases List.mem_cons.mp member with rfl | present
    · exact Or.inl (by simp)
    · exact Or.inr ⟨sc, present, rfl⟩
  have equalOriginal : ∀ sc ∈ first :: rest, assignment winner = assignment sc.var := by
    intro sc member
    apply consistent
    exact UnionFind.sameClass_trans (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
      ((resolvedValid.joined first.var sc.var).mpr (Or.inr ⟨selectedMember first (by simp), selectedMember sc member⟩))
  have equalRecorded : ∀ source ∈ recorded, assignment winner = assignment source := by
    intro source member
    rw [recordedSame] at member
    obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
    have fixed : roots (roots sc.var) = roots sc.var := by
      obtain ⟨size, path⟩ := paths sc.var
      exact (root_iff before.representatives roots paths (roots sc.var)).mp ⟨size, .root (UnionFind.reaches_terminal path)⟩
    exact (equalOriginal sc present).trans (consistent sc.var (roots sc.var)
      ((resolvedValid.joined sc.var (roots sc.var)).mpr (Or.inl fixed.symm)))
  have resolvedSatisfies := (terminal_assimilations_assignment graph language correct meaning assignment winner recorded
    resolved assimilated equalRecorded assimilation).mp satisfies
  have unitedSatisfies := (representative_assignment language meaning assignment fuel first.var winner united resolved joined.total resolution).2.mp resolvedSatisfies
  have scannedSatisfies := ((terminal_unions_assignment language meaning assignment fuel first.var rest scanned united scanTotal unions).2.mp unitedSatisfies).1
  exact ⟨scanExact.mp scannedSatisfies, equalOriginal⟩

/-- A successful terminal merge retains every assignment that satisfies the requested equalities. -/
theorem mergeTerminal_forward (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (total : UnionFind.Total before.representatives)
    (success : Success (mergeTerminal graph fuel first rest) before target after)
    (satisfies : Satisfies language meaning assignment before)
    (equal : ∀ sc ∈ rest, assignment first.var = assignment sc.var) :
    Satisfies language meaning assignment after := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, preScan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨_, recordedSame⟩ := representatives_scan before.values roots fuel (first :: rest)
    before scanned recorded ⟨rfl, paths⟩ preScan
  obtain ⟨scanTotal, scanExact⟩ := representatives_assignment language meaning assignment fuel (first :: rest) before scanned recorded total preScan
  have scannedSatisfies := scanExact.mpr satisfies
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨unitedTotal, unionExact⟩ := terminal_unions_assignment language meaning assignment fuel first.var rest scanned united scanTotal unions
  have unitedSatisfies := unionExact.mpr ⟨scannedSatisfies, equal⟩
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedSatisfies := (representative_assignment language meaning assignment fuel first.var winner united resolved unitedTotal resolution).2.mpr unitedSatisfies
  have winnerEqual : assignment winner = assignment first.var := by
    obtain ⟨found, lookup, winnerSame, _⟩ := (representative_success fuel first.var united resolved winner).mp resolution
    rw [winnerSame]
    exact (unitedSatisfies.1.1 first.var found.representative
      (UnionFind.sameClass_root (UnionFind.findRoot_correct fuel united.representatives first.var found lookup).1)).symm
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have equalRecorded : ∀ source ∈ recorded, assignment winner = assignment source := by
    intro source member
    rw [recordedSame] at member
    obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
    have equalFirst : assignment first.var = assignment sc.var := by
      rcases List.mem_cons.mp present with rfl | member
      · rfl
      · exact equal sc member
    obtain ⟨size, path⟩ := paths sc.var
    exact winnerEqual.trans (equalFirst.trans (satisfies.1.1 sc.var (roots sc.var) (UnionFind.sameClass_root path)))
  have assimilatedSatisfies := (terminal_assimilations_assignment graph language correct meaning assignment winner recorded
    resolved assimilated equalRecorded assimilation).mpr resolvedSatisfies
  obtain ⟨_, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst after
  exact assimilatedSatisfies

/-- The complete actual terminal merge adds precisely the requested assignment equalities. -/
theorem mergeTerminal_assignment (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (total : UnionFind.Total before.representatives)
    (success : Success (mergeTerminal graph fuel first rest) before target after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before ∧
      ∀ sc ∈ rest, assignment first.var = assignment sc.var := by
  constructor
  · intro satisfies
    obtain ⟨beforeSatisfies, equal⟩ := mergeTerminal_backward graph language correct meaning assignment fuel first rest before after target total success satisfies
    exact ⟨beforeSatisfies, fun sc member => (equal first (by simp)).symm.trans (equal sc (List.mem_cons_of_mem _ member))⟩
  · rintro ⟨satisfies, equal⟩
    exact mergeTerminal_forward graph language correct meaning assignment fuel first rest before after target total success satisfies equal

/-- A terminal suspended trie denotes equality with its assigned UVar. -/
theorem terminal_holds (assignment : Nat → Term Symbol) (term : Term Symbol) (sc : Suspended)
    (terminal : EqualityTrie.isTerminal sc.trie = true) :
    Suspended.Holds assignment term sc ↔ term = assignment sc.var := by
  obtain ⟨trie, uv⟩ := sc
  cases trie with
  | terminal => exact terminal_requirement assignment term uv
  | empty | branch children => cases terminal

/-- A successful terminal node action adds exactly its node and inherited equality restrictions. -/
theorem enumerateNode_terminal_assignment (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel node : Nat) (scs : List Suspended) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before ∧
      language node (fill assignment fragment) ∧ ∀ sc ∈ scs, Suspended.Holds assignment (fill assignment fragment) sc := by
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, merging, continued⟩ := (success_bind _ _ _ _ _).mp success
  have mergedTotal := (mergeTerminal_valid graph (fuel + 1) first rest before merged root safe.1.total safe.2 merging).2
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst fragment
  subst after
  simp only [fill]
  have restrictionExact := mergeNode_assignment graph language correct meaning assignment (fuel + 1) root node
    (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie) merged restricted mergedTotal restriction
  constructor
  · intro satisfies
    obtain ⟨mergedSatisfies, nodeHolds, belowHolds⟩ := restrictionExact.mp satisfies
    obtain ⟨beforeSatisfies, equal⟩ := mergeTerminal_backward graph language correct meaning assignment (fuel + 1) first rest
      before merged root safe.1.total merging mergedSatisfies
    refine ⟨beforeSatisfies, nodeHolds, ?_⟩
    intro sc member
    cases isTerminal : EqualityTrie.isTerminal sc.trie with
    | true =>
        have selected : sc ∈ first :: rest := by rw [← terminal]; exact List.mem_filter.mpr ⟨member, isTerminal⟩
        exact (terminal_holds assignment _ sc isTerminal).mpr (equal sc selected)
    | false => exact belowHolds sc (List.mem_filter.mpr ⟨member, by simp [isTerminal]⟩)
  · rintro ⟨beforeSatisfies, nodeHolds, inherited⟩
    have selectedHolds : ∀ sc ∈ first :: rest, assignment root = assignment sc.var := by
      intro sc member
      rw [← terminal] at member
      obtain ⟨present, atRoot⟩ := List.mem_filter.mp member
      exact (terminal_holds assignment _ sc atRoot).mp (inherited sc present)
    have mergedSatisfies := mergeTerminal_forward graph language correct meaning assignment (fuel + 1) first rest before merged root
      safe.1.total merging beforeSatisfies (fun sc member => (selectedHolds first (by simp)).symm.trans (selectedHolds sc (List.mem_cons_of_mem _ member)))
    exact restrictionExact.mpr ⟨mergedSatisfies, nodeHolds, fun sc member => inherited sc (List.mem_filter.mp member).1⟩

/-- Every inherited trie has the canonical finite-map representation. -/
def ValidSuspended (scs : List Suspended) : Prop := ∀ sc ∈ scs, EqualityTrie.Valid sc.trie

/-- Descent preserves the canonical trie representation. -/
theorem descend_valid (scs : List Suspended) (index : Nat) (valid : ValidSuspended scs) :
    ValidSuspended (descendScs index scs) := by
  intro sc member
  simp only [descendScs, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨original, present, rfl⟩, _⟩ := member
  exact EqualityTrie.descend_valid original.trie (valid original present) index

/-- Source edge construction supplies canonical tries whose paths fit the edge. -/
def ValidEdge (edge : EnumerationState.Edge Symbol Guard) : Prop :=
  (∀ trie ∈ edge.equalities, EqualityTrie.Valid trie) ∧
    ∀ trie ∈ edge.equalities, ∀ index suffix, index :: suffix ∈ EqualityTrie.fromPathTrie trie → index < edge.children.length

/-- The graph path has complete node views and constructor-valid edge equalities. -/
def CompleteGraph (graph : Graph Symbol Guard) : Prop :=
  (∀ node body, graph.node node ≠ .recursive body) ∧
    ∀ node edges, graph.node node = .alternatives edges → ∀ edge ∈ edges, ValidEdge edge

/-- A selected edge accepts its completed ordered children and all its predicates. -/
def EdgeAccepts (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (edge : EnumerationState.Edge Symbol Guard) (term : Term Symbol) : Prop :=
  ∃ children, term = .node edge.symbol children ∧ All₂ (Accepted graph meaning) edge.children children ∧
    (∀ trie ∈ edge.equalities, EqualityHolds term trie) ∧ ResidualHolds meaning edge.residual term

/-- Residual recording adds exactly the retained guard predicate. -/
theorem recordResidual_assignment (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (residual : Option Guard) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (success : Success (recordResidual residual fragment) before () after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before ∧
      ResidualHolds meaning residual (fill assignment fragment) := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      simp [ResidualHolds]
  | some guard =>
      obtain rfl := (modify_success _ before after).mp success
      simp only [Satisfies, Fragments.stateSatisfies, guardsHold, List.mem_cons, forall_eq_or_imp, ResidualHolds]
      exact ⟨fun ⟨state, guarded, old⟩ => ⟨⟨state, old⟩, guarded⟩, fun ⟨⟨state, old⟩, guarded⟩ => ⟨state, guarded, old⟩⟩

/-- A child traversal composes forward invariants and backward assignment implications. -/
theorem mapM_backward (action : α → EnumerateM Symbol Guard β) (invariant satisfies : State Symbol Guard → Prop)
    (relation : α → β → Prop) (inputs : List α)
    (step : ∀ input ∈ inputs, ∀ before output after, invariant before → Success (action input) before output after →
      invariant after ∧ (satisfies after → satisfies before ∧ relation input output))
    (before after : State Symbol Guard) (outputs : List β) (valid : invariant before)
    (success : Success (inputs.mapM action) before outputs after) (holds : satisfies after) :
    satisfies before ∧ All₂ relation inputs outputs := by
  induction inputs generalizing before outputs with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] outputs before after).mp success
      exact ⟨holds, .nil⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at success
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨middleValid, firstMeaning⟩ := step input (by simp) before output middle valid first
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨outputsSame, afterSame⟩ := (success_pure (output :: tail) outputs last after).mp final
      subst outputs
      subst after
      obtain ⟨middleHolds, tailRelation⟩ := ih (fun input member => step input (List.mem_cons_of_mem _ member))
        middle tail middleValid remaining
      obtain ⟨beforeHolds, headRelation⟩ := firstMeaning middleHolds
      exact ⟨beforeHolds, .cons headRelation tailRelation⟩

/-- Pointwise child evidence maps both sides without changing their order. -/
theorem all₂_map_both (leftMap : α → γ) (rightMap : β → δ) (relation : α → β → Prop)
    (target : γ → δ → Prop) (step : ∀ left right, relation left right → target (leftMap left) (rightMap right))
    (left : List α) (right : List β) (related : All₂ relation left right) :
    All₂ target (left.map leftMap) (right.map rightMap) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (step _ _ head) ih

/-- Pointwise child evidence identifies the corresponding input at each output index. -/
theorem all₂_get_right (relation : α → β → Prop) (left : List α) (right : List β)
    (related : All₂ relation left right) (index : Nat) (output : β) (found : right[index]? = some output) :
    ∃ input, left[index]? = some input ∧ relation input output := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst output; exact ⟨_, rfl, head⟩
      | succ index => exact ih index found

/-- Indexed child evidence supplies acceptance and every descended suspended equality. -/
theorem child_evidence (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (nodes : List Nat) (scs : List Suspended) (children : List (Fragment Symbol))
    (related : All₂ (fun entry child => Accepted graph meaning entry.1 (fill assignment child) ∧
      ∀ sc ∈ descendScs entry.2 scs, Suspended.Holds assignment (fill assignment child) sc) nodes.zipIdx children) :
    All₂ (Accepted graph meaning) nodes (children.map (fill assignment)) ∧
      ∀ index child, (children.map (fill assignment))[index]? = some child →
        ∀ sc ∈ descendScs index scs, Suspended.Holds assignment child sc := by
  constructor
  · have accepted := all₂_map_both Prod.fst (fill assignment) _ (Accepted graph meaning)
      (fun _ _ evidence => evidence.1) nodes.zipIdx children related
    simpa using accepted
  · intro index child found
    rw [List.getElem?_map] at found
    obtain ⟨fragment, stored, same⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨entry, entryStored, evidence⟩ := all₂_get_right _ nodes.zipIdx children related index fragment stored
    have indexSame : entry.2 = index := by
      rw [List.getElem?_zipIdx] at entryStored
      obtain ⟨node, _, rfl⟩ := Option.map_eq_some_iff.mp entryStored
      simp
    simpa [indexSame, same] using evidence.2

/-- Actual complete node and edge traversal preserves all prior assignment restrictions and proves its returned term. -/
theorem enumeration_backward (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment : Nat → Term Symbol) (fuel : Nat) :
    (∀ scs node (before after : State Symbol Guard) fragment, Safe before →
      (∀ sc ∈ scs, sc.var < before.counter) → ValidSuspended scs →
      Success (enumerateNode graph fuel scs node) before fragment after →
      Satisfies (Accepted graph meaning) meaning assignment after →
      Satisfies (Accepted graph meaning) meaning assignment before ∧
        Accepted graph meaning node (fill assignment fragment) ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (fill assignment fragment) sc) ∧
    (∀ scs edge (before after : State Symbol Guard) fragment, Safe before →
      (∀ sc ∈ scs, sc.var < before.counter) → ValidSuspended scs →
      (∀ sc ∈ scs, EqualityTrie.isTerminal sc.trie = false) → ValidEdge edge →
      Success (enumerateEdge graph fuel scs edge) before fragment after →
      Satisfies (Accepted graph meaning) meaning assignment after →
      Satisfies (Accepted graph meaning) meaning assignment before ∧
        EdgeAccepts graph meaning edge (fill assignment fragment) ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (fill assignment fragment) sc) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node before after fragment _ _ _ success _
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge before after fragment _ _ _ _ _ success _
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node before after fragment safe bounded valid success satisfies
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | recursive body => exact (complete.1 node body view).elim
        | alternatives edges | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                exact (enumerateNode_terminal_assignment graph (Accepted graph meaning) correct meaning assignment fuel node scs first rest
                  before after fragment safe (by simp [view]) terminal success).mp satisfies
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨selected, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   have nonterminal : ∀ sc ∈ scs, EqualityTrie.isTerminal sc.trie = false := by
                     intro sc member
                     cases atRoot : EqualityTrie.isTerminal sc.trie with
                     | false => rfl
                     | true =>
                         have present : sc ∈ scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) := List.mem_filter.mpr ⟨member, atRoot⟩
                         rw [terminal] at present
                         cases present
                   obtain ⟨beforeSatisfies, ⟨children, fragmentSame, childRuns, equalities, residual⟩, inherited⟩ :=
                     ih.2 scs edge before after fragment safe bounded valid nonterminal
                       (complete.2 node edges view edge selected) continued satisfies
                   refine ⟨beforeSatisfies, ?_, inherited⟩
                   rw [fragmentSame]
                   exact Accepted.edge node edges edge children view selected childRuns
                     (by simpa [fragmentSame] using equalities) (by simpa [fragmentSame] using residual))
      · intro scs edge before after fragment safe bounded valid nonterminal edgeValid success satisfies
        rw [edge_action graph fuel scs edge] at success
        obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp success
        cases ignored
        obtain ⟨arity, same⟩ := (require_success _ before checked).mp required
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
        have startGrowth : before.counter ≤ start.counter := by simp [start, suspended_counter]
        have inputsBound : ∀ sc ∈ inputs, sc.var < start.counter := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact Nat.lt_of_lt_of_le (bounded sc old) startGrowth
          · simpa [start, suspended_counter] using suspended_bounded before.counter edge.equalities sc fresh
        have inputsValid : ValidSuspended inputs := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact valid sc old
          · have member : sc.trie ∈ edge.equalities := by
              rw [← suspendedVars_tries before.counter edge.equalities]
              exact List.mem_map.mpr ⟨sc, fresh, rfl⟩
            exact edgeValid.1 sc.trie member
        obtain ⟨children, expanded, traversed, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨ignored, guarded, guarding, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst fragment
        subst after
        obtain ⟨expandedSatisfies, residual⟩ := (recordResidual_assignment (Accepted graph meaning) meaning assignment edge.residual
          (.node edge.symbol children) expanded guarded guarding).mp satisfies
        let invariant := fun state : State Symbol Guard => Safe state ∧ start.counter ≤ state.counter
        have childStep : ∀ entry ∈ edge.children.zipIdx, ∀ previous child next, invariant previous →
            Success (enumerateNode graph fuel (descendScs entry.2 inputs) entry.1) previous child next →
            invariant next ∧ (Satisfies (Accepted graph meaning) meaning assignment next →
              Satisfies (Accepted graph meaning) meaning assignment previous ∧
                Accepted graph meaning entry.1 (fill assignment child) ∧
                ∀ sc ∈ descendScs entry.2 inputs, Suspended.Holds assignment (fill assignment child) sc) := by
          intro entry _ previous child next previousValid childSuccess
          have childBound : ∀ sc ∈ descendScs entry.2 inputs, sc.var < previous.counter := by
            apply descend_bounded
            intro sc member
            exact Nat.lt_of_lt_of_le (inputsBound sc member) previousValid.2
          obtain ⟨nextSafe, growth, _⟩ := (enumeration_safety graph fuel).1 _ entry.1 previous next child previousValid.1 childBound childSuccess
          refine ⟨⟨nextSafe, Nat.le_trans previousValid.2 growth⟩, ?_⟩
          exact ih.1 _ entry.1 previous next child previousValid.1 childBound (descend_valid inputs entry.2 inputsValid) childSuccess
        obtain ⟨startSatisfies, childRelation⟩ := mapM_backward
          (fun entry => enumerateNode graph fuel (descendScs entry.2 inputs) entry.1) invariant
          (Satisfies (Accepted graph meaning) meaning assignment)
          (fun entry child => Accepted graph meaning entry.1 (fill assignment child) ∧
            ∀ sc ∈ descendScs entry.2 inputs, Suspended.Holds assignment (fill assignment child) sc)
          edge.children.zipIdx childStep start expanded children ⟨startSafe, Nat.le_refl _⟩ traversed expandedSatisfies
        obtain ⟨childRuns, descendants⟩ := child_evidence graph meaning assignment edge.children inputs children childRelation
        have lengthSame : (children.map (fill assignment)).length = edge.children.length := childRuns.length_eq.symm
        have inheritedArity : arityAllows (children.map (fill assignment)).length scs = true := by simpa [lengthSame] using arity
        have freshArity : arityAllows (children.map (fill assignment)).length (suspendedVars before.counter edge.equalities) = true := by
          rw [lengthSame, fresh_arity_iff]
          exact edgeValid.2
        have inheritedHolds := suspended_descent_complete assignment edge.symbol (children.map (fill assignment)) scs valid
          inheritedArity (by intro sc member atRoot; simp [nonterminal sc member] at atRoot)
          (fun index child found sc member => descendants index child found sc
            (descendScs_mono index scs inputs (by intro sc member; exact List.mem_append_left _ member) member))
        have equalities := edge_equalities_from_children assignment edge.symbol (children.map (fill assignment)) edge.equalities
          before.counter scs edgeValid.1 freshArity descendants
        refine ⟨(suspendMany_semantics (Accepted graph meaning) meaning assignment edge.equalities.length before safe.1.aligned).mp startSatisfies,
          ?_, ?_⟩
        · exact ⟨children.map (fill assignment), by simp [fill], childRuns, by simpa [fill] using equalities, residual⟩
        · simpa [fill] using inheritedHolds

end MicroCFTA.EnumerationSemantics
