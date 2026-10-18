import MicroCFTA.SourceCurrentStoredMuMarkerEmpty
namespace MicroCFTA.StoredMuMarkerKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input)
open InternedBinderProtocol (Reference)
open InternedRootProfile (profile)
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
private def environment (ordinaryCase : Bool) : Environment Nat Bool :=
  fun name => if name = outerName ordinaryCase then some .empty else none
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
  · cases found; exact empty_available _
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
    · cbv; decide
    · obtain rfl := List.mem_singleton.mp member
      cbv; decide
private theorem marker_available (ordinaryCase : Bool) : Available (reader ordinaryCase) (.reference marker) :=
  InternedNestedProvenance.ordinary_available (reader ordinaryCase) 100
private theorem nested_bare : val (strictBody false) = .reference marker := by cbv
private theorem nested_empty : val (whole false) = .empty := by cbv
private theorem node_nonempty : ((val (whole true)).referenceOf == .empty) = false := by cbv
private theorem ordinary_rows :
    ∃ row, InternedEdgeResidency.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker] := by
  let row := match InternedEdgeResidency.nodeEdges (val (strictBody true)) with
    | first :: _ => first
    | [] => (run (makeEdge 7 false []) (empty (Symbol := Nat) (Guard := Bool))).1
  exact ⟨row,by cbv,by cbv,by cbv,by cbv⟩
private theorem node_not_bare : val (strictBody true) ≠ .reference marker := by
  intro impossible
  have shape : profile (val (strictBody true)) = none := by cbv
  rw [impossible] at shape
  simp only [profile] at shape
  cases shape
private theorem endpoint (ordinaryCase : Bool) :
    Keeps (reader ordinaryCase) (strictBody ordinaryCase).state ∧
    Available (strictBody ordinaryCase).state (val (strictBody ordinaryCase)) ∧
    (((val (whole ordinaryCase)).referenceOf == .empty) = true ↔
      val (strictBody ordinaryCase) = .empty ∨ val (strictBody ordinaryCase) = .reference marker) := by
  obtain ⟨result,after,actual,kept,available,reflected⟩ := SourceCurrentStoredMuMarkerEmpty.complete
    (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) (ready ordinaryCase)
    (target_shape ordinaryCase ▸ target_available ordinaryCase) (replacements ordinaryCase) (target_shape ordinaryCase ▸ opened ordinaryCase)
    marker (marker_available ordinaryCase) (fresh ordinaryCase) (val (whole ordinaryCase)) (whole ordinaryCase).state
      (target_shape ordinaryCase ▸ whole_done ordinaryCase)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans (body_done ordinaryCase))
  exact ⟨kept,available,reflected⟩

private theorem checked_witness :
    (∀ ordinaryCase : Bool,
      build (source ordinaryCase) [] empty = .done (root ordinaryCase) (reader ordinaryCase) ∧ Ready (reader ordinaryCase) ∧
      Available (reader ordinaryCase) (target ordinaryCase) ∧
      target ordinaryCase = .mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) ∧
      (target ordinaryCase).free.isEmpty = false ∧ (.interned (entry ordinaryCase).identity) ∈ (body ordinaryCase).free ∧
      execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) = .done (val (whole ordinaryCase)) (whole ordinaryCase).state ∧
      execute (body ordinaryCase) (shadow (.interned (entry ordinaryCase).identity) (.reference marker) (environment ordinaryCase))
        (reader ordinaryCase) = .done (val (strictBody ordinaryCase)) (strictBody ordinaryCase).state ∧
      Keeps (reader ordinaryCase) (strictBody ordinaryCase).state ∧
      Available (strictBody ordinaryCase).state (val (strictBody ordinaryCase)) ∧
      (((val (whole ordinaryCase)).referenceOf == .empty) = true ↔
        val (strictBody ordinaryCase) = .empty ∨ val (strictBody ordinaryCase) = .reference marker)) ∧
    val (strictBody false) = .reference marker ∧ val (whole false) = .empty ∧
    ((val (whole true)).referenceOf == .empty) = false ∧ val (strictBody true) ≠ .reference marker ∧
    (∃ row, InternedEdgeResidency.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker]) := by
  refine ⟨?_,nested_bare,nested_empty,node_nonempty,node_not_bare,ordinary_rows⟩
  intro ordinaryCase
  exact ⟨built_done ordinaryCase,ready ordinaryCase,target_available ordinaryCase,target_shape ordinaryCase,opened ordinaryCase,used ordinaryCase,
    whole_done ordinaryCase,body_done ordinaryCase,endpoint ordinaryCase⟩

theorem nested_self_and_ordinary_marker :
    (∀ ordinaryCase : Bool,
      build (source ordinaryCase) [] empty = .done (root ordinaryCase) (reader ordinaryCase) ∧ Ready (reader ordinaryCase) ∧
      Available (reader ordinaryCase) (target ordinaryCase) ∧
      target ordinaryCase = .mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) ∧
      (target ordinaryCase).free.isEmpty = false ∧ (.interned (entry ordinaryCase).identity) ∈ (body ordinaryCase).free ∧
      execute (target ordinaryCase) (environment ordinaryCase) (reader ordinaryCase) = .done (val (whole ordinaryCase)) (whole ordinaryCase).state ∧
      execute (body ordinaryCase) (shadow (.interned (entry ordinaryCase).identity) (.reference marker) (environment ordinaryCase))
        (reader ordinaryCase) = .done (val (strictBody ordinaryCase)) (strictBody ordinaryCase).state ∧
      Keeps (reader ordinaryCase) (strictBody ordinaryCase).state ∧
      Available (strictBody ordinaryCase).state (val (strictBody ordinaryCase)) ∧
      (((val (whole ordinaryCase)).referenceOf == .empty) = true ↔
        val (strictBody ordinaryCase) = .empty ∨ val (strictBody ordinaryCase) = .reference marker)) ∧
    val (strictBody false) = .reference marker ∧ val (whole false) = .empty ∧
    ((val (whole true)).referenceOf == .empty) = false ∧ val (strictBody true) ≠ .reference marker ∧
    (∃ row, InternedEdgeResidency.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker]) := checked_witness
end MicroCFTA.StoredMuMarkerKernels
