import MicroCFTA.SourceCurrentStoredMuTrackedProfile
namespace MicroCFTA.StoredMuTrackedProfileKernels
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

private theorem checked_witness :
    (∀ ordinaryCase : Bool,
      build (source ordinaryCase) [] empty = .done (root ordinaryCase) (reader ordinaryCase) ∧ Ready (reader ordinaryCase) ∧
      Available (reader ordinaryCase) (target ordinaryCase) ∧
      target ordinaryCase = .mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) ∧
      (target ordinaryCase).free.isEmpty = false ∧ (.interned (entry ordinaryCase).identity) ∈ (body ordinaryCase).free ∧
      execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) =
        .done (val (whole ordinaryCase)) (whole ordinaryCase).state ∧
      execute (body ordinaryCase) (shadow (.interned (entry ordinaryCase).identity) (.reference marker) (environment ordinaryCase))
        (reader ordinaryCase) = .done (val (strictBody ordinaryCase)) (strictBody ordinaryCase).state ∧
      Keeps (reader ordinaryCase) (strictBody ordinaryCase).state ∧
      Available (strictBody ordinaryCase).state (val (strictBody ordinaryCase)) ∧
      Equivalent (profile (val (whole ordinaryCase))) (erase marker (profile (val (strictBody ordinaryCase))))) ∧
    marker ≠ oldMarker ∧ profile (val (strictBody false)) = some [marker,oldMarker] ∧
    erase marker (profile (val (strictBody false))) = some [oldMarker] ∧
    val (whole false) = .reference oldMarker ∧
    ((val (whole true)).referenceOf == .empty) = false ∧ val (strictBody true) ≠ .reference marker ∧
    (∃ row, InternedEdgeResidency.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker]) := by
  refine ⟨?_,(by intro impossible; cases impossible),mixed_profile,mixed_erased,mixed_result,node_nonempty,node_not_bare,ordinary_rows⟩
  intro ordinaryCase
  exact ⟨built_done ordinaryCase,ready ordinaryCase,target_available ordinaryCase,target_shape ordinaryCase,
    opened ordinaryCase,used ordinaryCase,whole_done ordinaryCase,body_done ordinaryCase,endpoint ordinaryCase⟩

theorem mixed_marker_and_ordinary_opacity :
    (∀ ordinaryCase : Bool,
      build (source ordinaryCase) [] empty = .done (root ordinaryCase) (reader ordinaryCase) ∧ Ready (reader ordinaryCase) ∧
      Available (reader ordinaryCase) (target ordinaryCase) ∧
      target ordinaryCase = .mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) ∧
      (target ordinaryCase).free.isEmpty = false ∧ (.interned (entry ordinaryCase).identity) ∈ (body ordinaryCase).free ∧
      execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) =
        .done (val (whole ordinaryCase)) (whole ordinaryCase).state ∧
      execute (body ordinaryCase) (shadow (.interned (entry ordinaryCase).identity) (.reference marker) (environment ordinaryCase))
        (reader ordinaryCase) = .done (val (strictBody ordinaryCase)) (strictBody ordinaryCase).state ∧
      Keeps (reader ordinaryCase) (strictBody ordinaryCase).state ∧
      Available (strictBody ordinaryCase).state (val (strictBody ordinaryCase)) ∧
      Equivalent (profile (val (whole ordinaryCase))) (erase marker (profile (val (strictBody ordinaryCase))))) ∧
    marker ≠ oldMarker ∧ profile (val (strictBody false)) = some [marker,oldMarker] ∧
    erase marker (profile (val (strictBody false))) = some [oldMarker] ∧
    val (whole false) = .reference oldMarker ∧
    ((val (whole true)).referenceOf == .empty) = false ∧ val (strictBody true) ≠ .reference marker ∧
    (∃ row, InternedEdgeResidency.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker]) := checked_witness
end MicroCFTA.StoredMuTrackedProfileKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.StoredMuTrackedProfileKernels.mixed_marker_and_ordinary_opacity
#print MicroCFTA.StoredMuTrackedProfileKernels.mixed_marker_and_ordinary_opacity
#print axioms MicroCFTA.StoredMuTrackedProfileKernels.mixed_marker_and_ordinary_opacity
