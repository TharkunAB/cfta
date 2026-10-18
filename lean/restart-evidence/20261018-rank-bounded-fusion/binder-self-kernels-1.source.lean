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
private def source (opaque : Bool) : Syntax Nat Bool :=
  if opaque then .binder false (.binder false (.union [.node [.mk 7 false [.var 0]],.var 1]))
  else .binder false (.binder false (.binder false (.union [.var 1,.var 2])))
private def built (opaque : Bool) := build (source opaque) [] empty
private def root (opaque : Bool) := val (built opaque)
private def reader (opaque : Bool) := (built opaque).state
private def target (opaque : Bool) := match root opaque with | .mu _ body _ _ => body | _ => .empty
private def outerName (opaque : Bool) : Reference :=
  match root opaque with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def entry (opaque : Bool) : Interned InternedBinderProtocol.NodeKey :=
  match target opaque with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def body (opaque : Bool) := match target opaque with | .mu _ body _ _ => body | _ => .empty
private def depth (opaque : Bool) := match target opaque with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary (opaque : Bool) := match target opaque with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def environment (opaque : Bool) : Environment Nat Bool :=
  fun name => if name = outerName opaque then some .empty else none
private def whole (opaque : Bool) := execute (target opaque) (environment opaque) (reader opaque)
private def marker : Reference := .uninterned 100
private def strictBody (opaque : Bool) := execute (body opaque)
  (shadow (.interned (entry opaque).identity) (.reference marker) (environment opaque)) (reader opaque)

private theorem built_done (opaque : Bool) :
    build (source opaque) [] empty = .done (root opaque) (reader opaque) := by
  exact unpack (built opaque) (by cases opaque <;> cbv)
private theorem ready (opaque : Bool) : Ready (reader opaque) :=
  SourceEqualityRequiredCache.constructed (source opaque) (root opaque) (reader opaque) (built_done opaque)
private theorem target_shape (opaque : Bool) :
    target opaque = .mu (entry opaque) (body opaque) (depth opaque) (ordinary opaque) := by
  cases opaque <;> cbv
private theorem target_available (opaque : Bool) : Available (reader opaque) (target opaque) := by
  have rootAvailable := (InternedFreshOrdinaryFacts.build_verified (source opaque) [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result (root opaque) (reader opaque) (built_done opaque)
  have selected : target opaque ∈ InternedProbeProvenance.children (root opaque) := by
    cases opaque <;> cbv <;> exact List.mem_cons_self
  exact rootAvailable.children _ selected
private theorem replacements (opaque : Bool) : Replacements (reader opaque) (environment opaque) := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found; exact empty_available _
  · cases found
private theorem whole_done (opaque : Bool) :
    execute (target opaque) (environment opaque) (reader opaque) = .done (val (whole opaque)) (whole opaque).state :=
  unpack (whole opaque) (by cases opaque <;> cbv)
private theorem body_done (opaque : Bool) :
    execute (body opaque) (shadow (.interned (entry opaque).identity) (.reference marker) (environment opaque))
      (reader opaque) = .done (val (strictBody opaque)) (strictBody opaque).state :=
  unpack (strictBody opaque) (by cases opaque <;> cbv)
private theorem opened (opaque : Bool) : (target opaque).free.isEmpty = false := by
  cases opaque <;> cbv
private theorem used (opaque : Bool) : (.interned (entry opaque).identity) ∈ (body opaque).free := by
  cases opaque <;> cbv <;> simp
private theorem fresh (opaque : Bool) :
    ∀ leaf ∈ leaves (body opaque), marker ∉ (profile (input (environment opaque) leaf)).getD [] := by
  cases opaque <;> cbv <;> simp
private theorem marker_available (opaque : Bool) : Available (reader opaque) (.reference marker) :=
  InternedNestedProvenance.ordinary_available (reader opaque) 100
private theorem nested_bare : val (strictBody false) = .reference marker := by cbv
private theorem nested_empty : val (whole false) = .empty := by cbv
private theorem node_nonempty : (val (whole true)).referenceOf == .empty = false := by cbv
private theorem ordinary_rows :
    ∃ row, InternedProbeProvenance.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker] := by
  let row := match InternedProbeProvenance.nodeEdges (val (strictBody true)) with
    | first :: _ => first
    | [] => (run (makeEdge 7 false []) (empty (Symbol := Nat) (Guard := Bool))).1
  exact ⟨row,by cbv,by cbv,by cbv,by cbv⟩
private theorem node_not_bare : val (strictBody true) ≠ .reference marker := by
  intro impossible
  have shape : profile (val (strictBody true)) = none := by cbv
  rw [impossible] at shape
  cases shape
private theorem endpoint (opaque : Bool) :
    Keeps (reader opaque) (strictBody opaque).state ∧
    Available (strictBody opaque).state (val (strictBody opaque)) ∧
    (((val (whole opaque)).referenceOf == .empty) = true ↔
      val (strictBody opaque) = .empty ∨ val (strictBody opaque) = .reference marker) := by
  obtain ⟨result,after,actual,kept,available,reflected⟩ := SourceCurrentStoredMuMarkerEmpty.complete
    (entry opaque) (body opaque) (depth opaque) (ordinary opaque) (environment opaque) (reader opaque) (ready opaque)
    (target_shape opaque ▸ target_available opaque) (replacements opaque) (target_shape opaque ▸ opened opaque)
    marker (marker_available opaque) (fresh opaque) (val (whole opaque)) (whole opaque).state
      (target_shape opaque ▸ whole_done opaque)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans (body_done opaque))
  exact ⟨kept,available,reflected⟩

private theorem checked_witness :
    (∀ opaque : Bool,
      build (source opaque) [] empty = .done (root opaque) (reader opaque) ∧ Ready (reader opaque) ∧
      Available (reader opaque) (target opaque) ∧
      target opaque = .mu (entry opaque) (body opaque) (depth opaque) (ordinary opaque) ∧
      (target opaque).free.isEmpty = false ∧ (.interned (entry opaque).identity) ∈ (body opaque).free ∧
      execute (target opaque) (environment opaque) (reader opaque) = .done (val (whole opaque)) (whole opaque).state ∧
      execute (body opaque) (shadow (.interned (entry opaque).identity) (.reference marker) (environment opaque))
        (reader opaque) = .done (val (strictBody opaque)) (strictBody opaque).state ∧
      Keeps (reader opaque) (strictBody opaque).state ∧
      Available (strictBody opaque).state (val (strictBody opaque)) ∧
      (((val (whole opaque)).referenceOf == .empty) = true ↔
        val (strictBody opaque) = .empty ∨ val (strictBody opaque) = .reference marker)) ∧
    val (strictBody false) = .reference marker ∧ val (whole false) = .empty ∧
    (val (whole true)).referenceOf == .empty = false ∧ val (strictBody true) ≠ .reference marker ∧
    (∃ row, InternedProbeProvenance.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker]) := by
  refine ⟨?_,nested_bare,nested_empty,node_nonempty,node_not_bare,ordinary_rows⟩
  intro opaque
  exact ⟨built_done opaque,ready opaque,target_available opaque,target_shape opaque,opened opaque,used opaque,
    whole_done opaque,body_done opaque,endpoint opaque⟩

theorem nested_self_and_ordinary_marker :
    (∀ opaque : Bool,
      build (source opaque) [] empty = .done (root opaque) (reader opaque) ∧ Ready (reader opaque) ∧
      Available (reader opaque) (target opaque) ∧
      target opaque = .mu (entry opaque) (body opaque) (depth opaque) (ordinary opaque) ∧
      (target opaque).free.isEmpty = false ∧ (.interned (entry opaque).identity) ∈ (body opaque).free ∧
      execute (target opaque) (environment opaque) (reader opaque) = .done (val (whole opaque)) (whole opaque).state ∧
      execute (body opaque) (shadow (.interned (entry opaque).identity) (.reference marker) (environment opaque))
        (reader opaque) = .done (val (strictBody opaque)) (strictBody opaque).state ∧
      Keeps (reader opaque) (strictBody opaque).state ∧
      Available (strictBody opaque).state (val (strictBody opaque)) ∧
      (((val (whole opaque)).referenceOf == .empty) = true ↔
        val (strictBody opaque) = .empty ∨ val (strictBody opaque) = .reference marker)) ∧
    val (strictBody false) = .reference marker ∧ val (whole false) = .empty ∧
    (val (whole true)).referenceOf == .empty = false ∧ val (strictBody true) ≠ .reference marker ∧
    (∃ row, InternedProbeProvenance.nodeEdges (val (strictBody true)) = [row] ∧
      row.entry.key.symbol = 7 ∧ row.entry.key.constraint = false ∧ row.children = [.reference marker]) := checked_witness
end MicroCFTA.StoredMuMarkerKernels
