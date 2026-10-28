import MicroCFTA.EnumerationTermination

/-!
# Graph provenance for rendered variables

A rendered hole must refer to a class with a graph restriction or a completed
fragment. Free equality variables have neither and cannot provide a hole.
-/

namespace MicroCFTA.EnumerationCarriers
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness EnumerationConstruction EnumerationOutConstruction EnumerationDecrease EnumerationHistogram EnumerationTermination

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- A stored value has a graph restriction or its completed fragment. -/
def GraphValue : UVarValue Symbol → Prop
  | .unenumerated (some _) _ | .enumerated _ => True
  | _ => False

/-- A variable's class contains a stored graph restriction or completed fragment. -/
def CarriesGraph (state : State Symbol Guard) (uv : Nat) : Prop :=
  ∃ held value, UnionFind.SameClass state.representatives uv held ∧ state.values[held]? = some value ∧ GraphValue value

/-- An action retains each existing graph-bearing equality class. -/
def PreservesCarriers (before after : State Symbol Guard) : Prop :=
  ∀ uv, CarriesGraph before uv → CarriesGraph after uv

/-- Carrier preservation composes across consecutive actual states. -/
theorem PreservesCarriers.trans (first : PreservesCarriers before middle) (second : PreservesCarriers middle after) :
    PreservesCarriers before after := fun uv carried => second uv (first uv carried)

/-- An unchanged state preserves every carrier. -/
theorem PreservesCarriers.refl (state : State Symbol Guard) : PreservesCarriers state state := fun _ carried => carried

/-- A graph-bearing slot supplies a carrier for every variable in its class. -/
theorem carries_stored (state : State Symbol Guard) (uv held : Nat) (value : UVarValue Symbol)
    (same : UnionFind.SameClass state.representatives uv held) (stored : state.values[held]? = some value) (graph : GraphValue value) :
    CarriesGraph state uv := ⟨held, value, same, stored, graph⟩

/-- A total forest makes each graph-bearing slot its own carrier. -/
theorem carries_self (state : State Symbol Guard) (total : UnionFind.Total state.representatives) (uv : Nat) (value : UVarValue Symbol)
    (stored : state.values[uv]? = some value) (graph : GraphValue value) : CarriesGraph state uv := by
  obtain ⟨root, size, path⟩ := total uv
  exact ⟨uv, value, ⟨root, size, path, path⟩, stored, graph⟩

/-- Enlarging classes and retaining values preserves graph carriers. -/
theorem carriers_classes (before after : State Symbol Guard) (values : after.values = before.values)
    (classes : ∀ left right, UnionFind.SameClass before.representatives left right → UnionFind.SameClass after.representatives left right) :
    PreservesCarriers before after := by
  rintro uv ⟨held, value, same, stored, graph⟩
  exact ⟨held, value, classes uv held same, by simpa [values] using stored, graph⟩

/-- Actual representative lookup preserves every graph carrier. -/
theorem representative_carriers (fuel uv root : Nat) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives) (success : Success (representative fuel uv) before root after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after := by
  obtain ⟨found, lookup, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact ⟨UnionFind.findRoot_total total lookup, carriers_classes _ _ rfl
    (fun left right same => (UnionFind.findRoot_classes total lookup left right).mpr same)⟩

/-- Actual equality union preserves every graph carrier. -/
theorem union_carriers (fuel left right : Nat) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives) (success : Success (unionVariables fuel left right) before () after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after := by
  obtain ⟨forest, lookup, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact ⟨(UnionFind.union_correct total lookup).1, carriers_classes _ _ rfl
    (fun left right same => ((UnionFind.union_correct total lookup).2 left right).mpr (Or.inl same))⟩

/-- Fresh allocation retains every earlier graph carrier. -/
theorem allocation_carriers (node : Option Nat) (before : State Symbol Guard) : PreservesCarriers before (allocated node before) := by
  rintro uv ⟨held, value, same, stored, graph⟩
  have inside := (List.getElem?_eq_some_iff.mp stored).1
  exact ⟨held, value, same, by simpa [allocated, List.getElem?_append, inside] using stored, graph⟩

/-- Replacing a stored graph-bearing value by another retains every carrier. -/
theorem set_graph_carriers (before : State Symbol Guard) (uv : Nat) (value : UVarValue Symbol) (graph : GraphValue value) :
    PreservesCarriers before {before with values := before.values.set uv value} := by
  rintro other ⟨held, old, same, stored, oldGraph⟩
  by_cases selected : held = uv
  · subst held
    have inside := (List.getElem?_eq_some_iff.mp stored).1
    exact ⟨uv, value, same, by simp [inside], graph⟩
  · exact ⟨held, old, same, by simpa [Ne.symm selected] using stored, oldGraph⟩

/-- Pending-value intersection retains either operand's graph restriction. -/
theorem intersection_graph (graph : Graph Symbol Guard) (left right merged : UVarValue Symbol)
    (intersection : intersectValues graph left right = some merged) (bearing : GraphValue left ∨ GraphValue right) : GraphValue merged := by
  cases left <;> cases right <;> simp only [intersectValues] at intersection
  all_goals try cases intersection
  rename_i left ls right rs
  cases left <;> cases right <;> simp_all [GraphValue]

/-- Assimilation transfers the source's graph restriction into its equal target class. -/
theorem assimilated_carriers (graph : Graph Symbol Guard) (before : State Symbol Guard) (target source : Nat)
    (left right merged : UVarValue Symbol) (different : target ≠ source)
    (sourceRead : before.values[source]? = some left) (targetRead : before.values[target]? = some right)
    (intersection : intersectValues graph left right = some merged)
    (related : UnionFind.SameClass before.representatives target source) : PreservesCarriers before (assimilated before target source merged) := by
  rintro uv ⟨held, value, same, stored, bearing⟩
  have targetInside := (List.getElem?_eq_some_iff.mp targetRead).1
  by_cases atSource : held = source
  · subst held
    have valueSame : value = left := Option.some.inj (stored.symm.trans sourceRead)
    refine ⟨target, merged, UnionFind.sameClass_trans same (UnionFind.sameClass_symm related), ?_, ?_⟩
    · simp [assimilated, targetInside, Ne.symm different]
    · exact intersection_graph graph left right merged intersection (Or.inl (valueSame ▸ bearing))
  · by_cases atTarget : held = target
    · subst held
      have valueSame : value = right := Option.some.inj (stored.symm.trans targetRead)
      refine ⟨target, merged, same, ?_, ?_⟩
      · simp [assimilated, targetInside, Ne.symm different]
      · exact intersection_graph graph left right merged intersection (Or.inr (valueSame ▸ bearing))
    · exact ⟨held, value, same, (assimilation_frame before target source held merged atTarget atSource).trans stored, bearing⟩

/-- Every successful assimilation within one class preserves its graph carrier. -/
theorem assimilate_carriers (graph : Graph Symbol Guard) (target source : Nat) (before after : State Symbol Guard)
    (related : UnionFind.SameClass before.representatives target source)
    (success : Success (EnumerationState.assimilate graph target source) before () after) : PreservesCarriers before after := by
  have original := success
  by_cases same : target = source
  · subst source
    have unchanged : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    subst after
    exact .refl before
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, sourceState, sourceLookup, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨sourceRead, sourceSame⟩ := (rawValue_success source before sourceState sourceValue).mp sourceLookup
    subst sourceState
    cases sourceValue with
    | eliminated =>
        obtain ⟨_, stateSame⟩ := (success_pure () () before after).mp continued
        subst after
        exact .refl before
    | enumerated fragment =>
        obtain ⟨targetValue, targetState, targetLookup, continued⟩ := (success_bind _ _ _ _ _).mp continued
        exact (success_failure .invalidIntersection targetState after () continued).elim
    | unenumerated sourceNode sourceScs =>
        obtain ⟨targetValue, targetState, targetLookup, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨targetRead, targetSame⟩ := (rawValue_success target before targetState targetValue).mp targetLookup
        subst targetState
        cases targetValue with
        | eliminated | enumerated _ => exact (success_failure .invalidIntersection before after () continued).elim
        | unenumerated targetNode targetScs =>
            let merged : UVarValue Symbol := .unenumerated (match sourceNode, targetNode with
              | none, node => node | node, none => node | some left, some right => some (graph.intersect left right)) (sourceScs ++ targetScs)
            have intersection : intersectValues graph (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs) = some merged := by
              cases sourceNode <;> cases targetNode <;> rfl
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, _⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have notEmpty : hasEmptyContents graph merged = false := by simpa using ((require_success _ before checked).mp required).1
            have execution := assimilate_exact graph before target source sourceNode targetNode sourceScs targetScs merged same sourceRead targetRead intersection notEmpty
            have afterSame : after = assimilated before target source merged := by simpa [Success, execution, ExceptT.run] using original
            rw [afterSame]
            exact assimilated_carriers graph before target source _ _ merged same sourceRead targetRead intersection related

/-- The complete terminal merge preserves each graph-bearing class through duplicate assimilation. -/
theorem mergeTerminal_carriers (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (total : UnionFind.Total before.representatives)
    (success : Success (mergeTerminal graph fuel first rest) before target after) : PreservesCarriers before after := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, scan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel (first :: rest) before scanned recorded ⟨rfl, paths⟩ scan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united := terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
    (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, count, path⟩ := merging_representative before.values roots selected fuel first.var winner united resolved joined resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨_, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst after
  have resolvedCarriers : PreservesCarriers before resolved := carriers_classes before resolved resolvedValid.values
    (fun left right same => (resolvedValid.joined left right).mpr (Or.inl ((class_iff before.representatives roots paths left right).mp same)))
  have selectedMember : ∀ sc ∈ first :: rest, roots sc.var ∈ selected := by
    intro sc member
    apply (resolve_members roots rest [roots first.var] (roots sc.var)).mpr
    rcases List.mem_cons.mp member with rfl | present
    · exact Or.inl (by simp)
    · exact Or.inr ⟨sc, present, rfl⟩
  have relatedRecorded : ∀ source ∈ recorded, UnionFind.SameClass resolved.representatives winner source := by
    intro source member
    rw [recordedSame] at member
    obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
    have fixed : roots (roots sc.var) = roots sc.var := by
      obtain ⟨size, original⟩ := paths sc.var
      exact (root_iff before.representatives roots paths (roots sc.var)).mp ⟨size, .root (UnionFind.reaches_terminal original)⟩
    exact UnionFind.sameClass_trans (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
      ((resolvedValid.joined first.var (roots sc.var)).mpr (Or.inr ⟨selectedMember first (by simp), by simpa [fixed] using selectedMember sc present⟩))
  have traversed := forM_invariant (EnumerationState.assimilate graph winner)
    (fun state : State Symbol Guard => state.representatives = resolved.representatives ∧ PreservesCarriers resolved state) recorded
    (by
      intro source member previous next valid execution
      have preserves := assimilate_carriers graph winner source previous next (by simpa [valid.1] using relatedRecorded source member) execution
      exact ⟨(assimilate_effect graph previous next winner source execution).1.trans valid.1, valid.2.trans preserves⟩)
    resolved assimilated ⟨rfl, .refl resolved⟩ assimilation
  exact resolvedCarriers.trans traversed.2

/-- A reached graph restriction preserves all old carriers and supplies one for its returned variable. -/
theorem mergeNode_carriers (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (success : Success (mergeNode graph fuel uv node scs) before () after) :
    PreservesCarriers before after ∧ CarriesGraph after uv := by
  unfold mergeNode at success
  obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp success
  have resolvedCarriers := (representative_carriers fuel uv root before resolved total resolution).2
  obtain ⟨found, lookup, rootSame, resolvedSame⟩ := (representative_success fuel uv before resolved root).mp resolution
  have reached := (UnionFind.findRoot_correct fuel before.representatives uv found lookup).2
    (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1
  have related : UnionFind.SameClass resolved.representatives uv root := by
    simpa [resolvedSame, rootSame] using UnionFind.sameClass_root reached
  obtain ⟨previous, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨stored, same⟩ := (rawValue_success root resolved readState previous).mp reading
  subst readState
  cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
  | none =>
      simp only [intersection] at continued
      exact (success_failure .invalidIntersection resolved after () continued).elim
  | some merged =>
      have bearing : GraphValue merged := intersection_graph graph (.unenumerated (some node) scs) previous merged intersection (Or.inl trivial)
      simp only [intersection] at continued
      obtain ⟨ignored, written, writing, continued⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain rfl := (modify_success _ resolved written).mp writing
      obtain ⟨ignored, inherited, inheritance, final⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain rfl := (modify_success _ _ inherited).mp inheritance
      obtain ⟨_, afterSame⟩ := (require_success _ _ after).mp final
      subst after
      have inside := (List.getElem?_eq_some_iff.mp stored).1
      exact ⟨resolvedCarriers.trans (set_graph_carriers resolved root merged bearing),
        ⟨root, merged, related, by simp [inside], bearing⟩⟩

/-- Fresh equality allocation preserves every carrier through the whole edge batch. -/
theorem suspension_carriers (count : Nat) (before : State Symbol Guard) : PreservesCarriers before (suspendedState count before) := by
  induction count generalizing before with
  | zero => exact .refl before
  | succ count ih => exact (allocation_carriers none before).trans (ih (allocated none before))

/-- Residual recording preserves every graph carrier. -/
theorem recordResidual_carriers (residual : Option Guard) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (success : Success (recordResidual residual fragment) before () after) : PreservesCarriers before after := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact .refl before
  | some guard =>
      obtain rfl := (modify_success _ before after).mp success
      exact .refl before

end MicroCFTA.EnumerationCarriers
