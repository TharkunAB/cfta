import MicroCFTA.SourceCurrentTrackedProfileErasure
set_option linter.all true
namespace MicroCFTA.TrackedErasureKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input)
open InternedBinderProtocol (Reference)
open InternedRootProfile (profile Equivalent)
open SourceCurrentStoredMuTrackedProfile (erase)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredMuLexicalInputs (shadow)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def done (outcome : Outcome Nat Bool (Value Nat Bool)) : Bool :=
  match outcome with | .done .. => true | .pending .. => false
private theorem unpack (outcome : Outcome Nat Bool (Value Nat Bool)) (success : done outcome = true) :
    outcome = .done (val outcome) outcome.state := by
  cases outcome <;> simp_all [done,val,Outcome.state]
private def source (ordinaryCase : Bool) : Syntax Nat Bool :=
  if ordinaryCase then .binder false (.binder false (.union [.node [.mk 7 false [.var 0]],.var 1]))
  else .binder false (.binder false (.binder false (.union [.var 1,.var 2])))
private def built (ordinaryCase : Bool) := build (source ordinaryCase) [] empty
private def root (ordinaryCase : Bool) := val (built ordinaryCase)
private def reader (ordinaryCase : Bool) := (built ordinaryCase).state
private def target (ordinaryCase : Bool) := match root ordinaryCase with | .mu _ body _ _ => body | _ => .empty
private def outerName (ordinaryCase : Bool) : Reference :=
  match root ordinaryCase with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def entry (ordinaryCase : Bool) : Interned InternedBinderProtocol.NodeKey :=
  match target ordinaryCase with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def body (ordinaryCase : Bool) := match target ordinaryCase with | .mu _ body _ _ => body | _ => .empty
private def depth (ordinaryCase : Bool) := match target ordinaryCase with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary (ordinaryCase : Bool) := match target ordinaryCase with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def oldMarker : Reference := .uninterned 101
private def environment (ordinaryCase : Bool) : Environment Nat Bool :=
  fun name => if name = outerName ordinaryCase then some (if ordinaryCase then .empty else .reference oldMarker) else none
private def whole (ordinaryCase : Bool) := execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase)
private def marker : Reference := .uninterned 100
private def strictBody (ordinaryCase : Bool) := execute (body ordinaryCase)
  (shadow (.interned (entry ordinaryCase).identity) (.reference marker) (environment ordinaryCase)) (reader ordinaryCase)

private theorem built_done (ordinaryCase : Bool) :
    build (source ordinaryCase) [] empty = .done (root ordinaryCase) (reader ordinaryCase) := by
  exact unpack (built ordinaryCase) (by cases ordinaryCase <;> cbv)
private theorem ready (ordinaryCase : Bool) : Ready (reader ordinaryCase) :=
  SourceEqualityRequiredCache.constructed (source ordinaryCase) (root ordinaryCase) (reader ordinaryCase) (built_done ordinaryCase)
private theorem target_shape (ordinaryCase : Bool) :
    target ordinaryCase = .mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) := by
  cases ordinaryCase <;> cbv
private theorem target_available (ordinaryCase : Bool) : Available (reader ordinaryCase) (target ordinaryCase) := by
  have rootAvailable := (InternedFreshOrdinaryFacts.build_verified (source ordinaryCase) [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result (root ordinaryCase) (reader ordinaryCase) (built_done ordinaryCase)
  have selected : target ordinaryCase ∈ InternedProbeProvenance.children (root ordinaryCase) := by
    cases ordinaryCase <;> cbv <;> exact List.mem_cons_self
  exact rootAvailable.children _ selected
private theorem replacements (ordinaryCase : Bool) : Replacements (reader ordinaryCase) (environment ordinaryCase) := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found
    cases ordinaryCase with
    | false => exact InternedNestedProvenance.ordinary_available _ 101
    | true => exact empty_available _
  · cases found
private theorem whole_done (ordinaryCase : Bool) :
    execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) = .done (val (whole ordinaryCase)) (whole ordinaryCase).state :=
  unpack (whole ordinaryCase) (by cases ordinaryCase <;> cbv)
private theorem body_done (ordinaryCase : Bool) :
    execute (body ordinaryCase) (shadow (.interned (entry ordinaryCase).identity) (.reference marker) (environment ordinaryCase))
      (reader ordinaryCase) = .done (val (strictBody ordinaryCase)) (strictBody ordinaryCase).state :=
  unpack (strictBody ordinaryCase) (by cases ordinaryCase <;> cbv)
private theorem opened (ordinaryCase : Bool) : (target ordinaryCase).free.isEmpty = false := by
  cases ordinaryCase <;> cbv
private theorem used (ordinaryCase : Bool) : (.interned (entry ordinaryCase).identity) ∈ (body ordinaryCase).free := by
  cases ordinaryCase <;> cbv <;> first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self
private theorem fresh (ordinaryCase : Bool) :
    ∀ leaf ∈ leaves (body ordinaryCase), marker ∉ (profile (input (environment ordinaryCase) leaf)).getD [] := by
  cases ordinaryCase
  all_goals
    intro leaf member
    cbv at member
    rcases List.mem_cons.mp member with rfl | member
    · cbv
      intro impossible
      have same := List.mem_singleton.mp impossible
      cases same
    · obtain rfl := List.mem_singleton.mp member
      cbv
      intro impossible
      first
      | have same := List.mem_singleton.mp impossible
        cases same
      | cases impossible
private theorem marker_available (ordinaryCase : Bool) : Available (reader ordinaryCase) (.reference marker) :=
  InternedNestedProvenance.ordinary_available (reader ordinaryCase) 100
private theorem mixed_profile : profile (val (strictBody false)) = some [marker,oldMarker] := by cbv
private theorem mixed_result : val (whole false) = .reference oldMarker := by cbv
private theorem mixed_erased : erase marker (profile (val (strictBody false))) = some [oldMarker] := by
  rw [mixed_profile]
  cbv
private theorem node_nonempty : ((val (whole true)).referenceOf == .empty) = false := by cbv
private theorem ordinary_rows :
    ∃ row, InternedEdgeResidency.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker] := by
  let row := match InternedEdgeResidency.nodeEdges (val (strictBody true)) with
    | first :: _ => first
    | [] => (run (makeEdge 7 false []) (empty (Symbol := Nat) (Guard := Bool))).1
  exact ⟨row,by dsimp only [row]; cbv,by dsimp only [row]; cbv,
    by dsimp only [row]; cbv,by dsimp only [row]; cbv⟩
private theorem node_not_bare : val (strictBody true) ≠ .reference marker := by
  intro impossible
  have shape : profile (val (strictBody true)) = none := by cbv
  rw [impossible] at shape
  simp only [profile] at shape
  cases shape
private theorem endpoint (ordinaryCase : Bool) :
    Keeps (reader ordinaryCase) (strictBody ordinaryCase).state ∧
    Available (strictBody ordinaryCase).state (val (strictBody ordinaryCase)) ∧
    Equivalent (profile (val (whole ordinaryCase))) (erase marker (profile (val (strictBody ordinaryCase)))) := by
  obtain ⟨result,after,actual,kept,available,related⟩ := SourceCurrentStoredMuTrackedProfile.complete
    (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) (environment ordinaryCase)
    (reader ordinaryCase) (ready ordinaryCase) (target_shape ordinaryCase ▸ target_available ordinaryCase)
    (replacements ordinaryCase) (target_shape ordinaryCase ▸ opened ordinaryCase)
    marker (marker_available ordinaryCase) (fresh ordinaryCase) (val (whole ordinaryCase)) (whole ordinaryCase).state
      (target_shape ordinaryCase ▸ whole_done ordinaryCase)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans (body_done ordinaryCase))
  exact ⟨kept,available,related⟩

private def otherMarker : Reference := .uninterned 102
private def markers : List Reference := [.uninterned 103]
private def otherEnvironment (ordinaryCase : Bool) : Environment Nat Bool :=
  fun name => if name = outerName ordinaryCase then some (if ordinaryCase then .empty else .reference otherMarker) else none
private def otherWhole (ordinaryCase : Bool) := execute (target ordinaryCase) (otherEnvironment ordinaryCase) (reader ordinaryCase)
private def otherBody (ordinaryCase : Bool) := execute (body ordinaryCase)
  (shadow (.interned (entry ordinaryCase).identity) (.reference marker) (otherEnvironment ordinaryCase)) (reader ordinaryCase)
private theorem other_replacements (ordinaryCase : Bool) : Replacements (reader ordinaryCase) (otherEnvironment ordinaryCase) := by
  intro name value found
  dsimp only [otherEnvironment] at found
  split at found
  · cases found
    cases ordinaryCase with
    | false => exact InternedNestedProvenance.ordinary_available _ 102
    | true => exact empty_available _
  · cases found
private theorem other_whole_done (ordinaryCase : Bool) :
    execute (target ordinaryCase) (otherEnvironment ordinaryCase) (reader ordinaryCase) =
      .done (val (otherWhole ordinaryCase)) (otherWhole ordinaryCase).state :=
  unpack (otherWhole ordinaryCase) (by cases ordinaryCase <;> cbv)
private theorem other_body_done (ordinaryCase : Bool) :
    execute (body ordinaryCase) (shadow (.interned (entry ordinaryCase).identity) (.reference marker) (otherEnvironment ordinaryCase))
      (reader ordinaryCase) = .done (val (otherBody ordinaryCase)) (otherBody ordinaryCase).state :=
  unpack (otherBody ordinaryCase) (by cases ordinaryCase <;> cbv)
private theorem other_fresh (ordinaryCase : Bool) :
    ∀ leaf ∈ leaves (body ordinaryCase), marker ∉ (profile (input (otherEnvironment ordinaryCase) leaf)).getD [] := by
  cases ordinaryCase
  all_goals
    intro leaf member
    cbv at member
    rcases List.mem_cons.mp member with rfl | member
    · cbv
      intro impossible
      have same := List.mem_singleton.mp impossible
      cases same
    · obtain rfl := List.mem_singleton.mp member
      cbv
      intro impossible
      first
      | have same := List.mem_singleton.mp impossible
        cases same
      | cases impossible
private theorem other_endpoint (ordinaryCase : Bool) :
    Keeps (reader ordinaryCase) (otherBody ordinaryCase).state ∧
    Available (otherBody ordinaryCase).state (val (otherBody ordinaryCase)) := by
  obtain ⟨result,after,actual,kept,available,_⟩ := SourceCurrentStoredMuTrackedProfile.complete
    (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) (otherEnvironment ordinaryCase)
    (reader ordinaryCase) (ready ordinaryCase) (target_shape ordinaryCase ▸ target_available ordinaryCase)
    (other_replacements ordinaryCase) (target_shape ordinaryCase ▸ opened ordinaryCase)
    marker (marker_available ordinaryCase) (other_fresh ordinaryCase) (val (otherWhole ordinaryCase)) (otherWhole ordinaryCase).state
      (target_shape ordinaryCase ▸ other_whole_done ordinaryCase)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans (other_body_done ordinaryCase))
  exact ⟨kept,available⟩
private theorem body_related (ordinaryCase : Bool) : SourceCurrentTrackedRootProfile.Related (marker :: markers)
    (val (strictBody ordinaryCase)) (val (otherBody ordinaryCase)) := by
  have first : SourceCurrentTrackedRootProfile.observe (marker :: markers) (val (strictBody ordinaryCase)) = none := by
    cases ordinaryCase <;> cbv
  have second : SourceCurrentTrackedRootProfile.observe (marker :: markers) (val (otherBody ordinaryCase)) = none := by
    cases ordinaryCase <;> cbv
  unfold SourceCurrentTrackedRootProfile.Related
  rw [first,second]
  exact InternedProfileEquivalence.refl _
private theorem whole_related (ordinaryCase : Bool) : SourceCurrentTrackedRootProfile.Related markers
    (val (whole ordinaryCase)) (val (otherWhole ordinaryCase)) := by
  exact SourceCurrentTrackedProfileErasure.open_execute marker markers (entry ordinaryCase) (entry ordinaryCase)
    (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)
    (environment ordinaryCase) (otherEnvironment ordinaryCase) (reader ordinaryCase) (reader ordinaryCase)
    (ready ordinaryCase) (ready ordinaryCase) (target_shape ordinaryCase ▸ target_available ordinaryCase)
    (target_shape ordinaryCase ▸ target_available ordinaryCase) (replacements ordinaryCase) (other_replacements ordinaryCase)
    (target_shape ordinaryCase ▸ opened ordinaryCase) (target_shape ordinaryCase ▸ opened ordinaryCase)
    (marker_available ordinaryCase) (marker_available ordinaryCase) (fresh ordinaryCase) (other_fresh ordinaryCase)
    (val (whole ordinaryCase)) (val (otherWhole ordinaryCase)) (whole ordinaryCase).state (otherWhole ordinaryCase).state
    (target_shape ordinaryCase ▸ whole_done ordinaryCase) (target_shape ordinaryCase ▸ other_whole_done ordinaryCase)
    (val (strictBody ordinaryCase)) (val (otherBody ordinaryCase)) (strictBody ordinaryCase).state (otherBody ordinaryCase).state
    (body_done ordinaryCase) (other_body_done ordinaryCase) (body_related ordinaryCase)

private theorem checked :
    (∀ ordinaryCase : Bool,
      Ready (reader ordinaryCase) ∧ Available (reader ordinaryCase) (target ordinaryCase) ∧
      execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) =
        .done (val (whole ordinaryCase)) (whole ordinaryCase).state ∧
      execute (target ordinaryCase) (otherEnvironment ordinaryCase) (reader ordinaryCase) =
        .done (val (otherWhole ordinaryCase)) (otherWhole ordinaryCase).state ∧
      Keeps (reader ordinaryCase) (strictBody ordinaryCase).state ∧
      Keeps (reader ordinaryCase) (otherBody ordinaryCase).state ∧
      SourceCurrentTrackedRootProfile.Related (marker :: markers) (val (strictBody ordinaryCase)) (val (otherBody ordinaryCase)) ∧
      SourceCurrentTrackedRootProfile.Related markers (val (whole ordinaryCase)) (val (otherWhole ordinaryCase))) ∧
    profile (val (strictBody false)) = some [marker,oldMarker] ∧
    profile (val (otherBody false)) = some [marker,otherMarker] ∧
    val (whole false) = .reference oldMarker ∧ val (otherWhole false) = .reference otherMarker ∧
    val (whole false) ≠ val (otherWhole false) ∧
    profile (val (strictBody true)) = none ∧
    SourceCurrentTrackedRootProfile.mask (marker :: [oldMarker]) (erase marker (profile (val (strictBody false)))) =
      erase marker (SourceCurrentTrackedRootProfile.mask (marker :: marker :: [oldMarker]) (profile (val (strictBody false)))) := by
  refine ⟨?_,mixed_profile,?_,mixed_result,?_,?_,?_,?_⟩
  · intro ordinaryCase
    exact ⟨ready ordinaryCase,target_available ordinaryCase,whole_done ordinaryCase,other_whole_done ordinaryCase,
      (endpoint ordinaryCase).1,(other_endpoint ordinaryCase).1,body_related ordinaryCase,whole_related ordinaryCase⟩
  · cbv
  · cbv
  · cbv; intro impossible; cases impossible
  · cbv
  · exact SourceCurrentTrackedProfileErasure.mask_erase marker (marker :: [oldMarker]) _

/-- Actual mixed local/outer and opaque body calls transfer tracked agreement through marker erasure. -/
theorem mixed_and_opaque :
    (∀ ordinaryCase : Bool,
      Ready (reader ordinaryCase) ∧ Available (reader ordinaryCase) (target ordinaryCase) ∧
      execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) =
        .done (val (whole ordinaryCase)) (whole ordinaryCase).state ∧
      execute (target ordinaryCase) (otherEnvironment ordinaryCase) (reader ordinaryCase) =
        .done (val (otherWhole ordinaryCase)) (otherWhole ordinaryCase).state ∧
      Keeps (reader ordinaryCase) (strictBody ordinaryCase).state ∧
      Keeps (reader ordinaryCase) (otherBody ordinaryCase).state ∧
      SourceCurrentTrackedRootProfile.Related (marker :: markers) (val (strictBody ordinaryCase)) (val (otherBody ordinaryCase)) ∧
      SourceCurrentTrackedRootProfile.Related markers (val (whole ordinaryCase)) (val (otherWhole ordinaryCase))) ∧
    profile (val (strictBody false)) = some [marker,oldMarker] ∧
    profile (val (otherBody false)) = some [marker,otherMarker] ∧
    val (whole false) = .reference oldMarker ∧ val (otherWhole false) = .reference otherMarker ∧
    val (whole false) ≠ val (otherWhole false) ∧
    profile (val (strictBody true)) = none ∧
    SourceCurrentTrackedRootProfile.mask (marker :: [oldMarker]) (erase marker (profile (val (strictBody false)))) =
      erase marker (SourceCurrentTrackedRootProfile.mask (marker :: marker :: [oldMarker]) (profile (val (strictBody false)))) := checked

end MicroCFTA.TrackedErasureKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.TrackedErasureKernels.mixed_and_opaque
#print MicroCFTA.TrackedErasureKernels.mixed_and_opaque
#print axioms MicroCFTA.TrackedErasureKernels.mixed_and_opaque
